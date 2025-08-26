From stdpp Require Import telescopes.
From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_inversion.

(* ========================================================================== *)
(** * Iteration Descriptors. *)

Class FinitelyObservable (A : Type) := {
    (* [permitted T Xs] holds if [Xs] is a possible prefix
     of visited elements of the collection [T]. *)
    permitted : list A → Prop;

    (* [complete T Xs] holds if [Xs] is the complete list
     of elements of the collection [T]. *)
    complete  : list A → Prop;
  }.

Section iteration_methods.
  Context `{!osirisGS Σ}.
  Context {A : Type} `{Encode A, FinitelyObservable A}.

  Definition isIter (iter : val) : iProp Σ :=
    ∀ (ψ : iEff Σ) E (I : list A → iProp Σ) (f : val),
      □ (∀ (Xs : list A) (X : A),
           ⌜ permitted (Xs ++ [X]) ⌝ -∗
           I Xs -∗
           (∀ ι, EWP (call f #X) @ E <| (ι, ψ) |> {{ ensures _, I (Xs ++ [X]) }}))
      -∗
      I [] -∗
      ∀ ι, EWP (call iter f) @E <| (ι, ψ) |>
        {{ ensures _, ∃ Xs, I Xs ∗ ⌜ complete Xs ⌝ }}.

End iteration_methods.


(* ========================================================================== *)
(** * Lazy Sequences. *)

Section lazy_sequences.
  Context `{!osirisGS Σ}.
  Context  {A : Type} `{Encode A, FinitelyObservable A}.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Heads. *)

  (* The predicate [isHead] is defined as [isHead_pre isSeq], where [isSeq] is
     the fixpoint of [isSeq_pre]. *)
  (* A head is either a [Cons] pair or a [Nil] marker. *)
  Definition isHead_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           :  iEff Σ -d> val -d> list A -d> iPropO Σ  :=
    λ Ψ h Xs,
      match h with
      | VData "Nil" [] =>
          ⌜ complete Xs ⌝
      | VData "Cons" p =>
          ∃ (X : A) k, ⌜ p = [ #X; #k]⌝ ∧
                 ⌜ permitted (Xs ++ [X]) ⌝ ∗ ▷ isSeq Ψ k (Xs ++ [X])
      | _ =>
          False
      end%I.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead Ψ1 Ψ2 h Xs]. *)
  Definition isSeq_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           : (iEff Σ -d> val -d> list A -d> iPropO Σ) :=
    λ Ψ k Xs,
      (∃ ι,
      EWP (call k #()) <| (ι, Ψ) |> {{ ensures h, isHead_pre isSeq Ψ h Xs }})%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isHead_pre_contractive : Contractive isSeq_pre.
  Proof.
    rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq Ψ k us.
    f_equiv=>?. simpl. repeat (f_contractive || f_equiv). by apply HisSeq.
  Qed.
  Definition isSeq_def :
    iEff Σ -d> val -d> list A -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold Ψ k us :
    isSeq Ψ k us ⊣⊢ isSeq_pre isSeq Ψ k us.
  Proof. by rewrite isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
  Global Lemma isHead_unfold Ψ :
    isHead Ψ = isHead_pre isSeq Ψ.
  Proof. done. Qed.

End lazy_sequences.


(* ========================================================================== *)
(** * Protocol. *)

Definition yield l x : val := VXData l [x].

(* This protocol describes the effects performed by [yield]. *)

Section inversion_protocol.
  Context `{!osirisGS Σ}.
  Context  {A : Type} `{Encode A, FinitelyObservable A}.

  Definition ψ_yield l (iterView : list A → iProp Σ) : iEff Σ :=
    (>> Xs X >>
       ! (yield l #X)
         {{ iterView Xs ∗ ⌜ permitted (Xs ++ [X]) ⌝ }};
       ? (@O2Ret val exn #())
         {{ iterView (Xs ++ [X]) }} @ OS).

  Lemma upcl_yield l iterView v Φ :
    iEff_car (upcl OS (ψ_yield l iterView)) v Φ ⊣⊢
      (∃ Xs (X : A), ⌜ v = yield l #X ⌝ ∗
                     (iterView Xs ∗
                     ⌜ permitted (Xs ++ [X]) ⌝) ∗
                     (iterView (Xs ++ [X]) -∗ Φ (O2Ret (VUnit))))%I.
  Proof. by rewrite /ψ_yield  (upcl_tele' [tele _ _] [tele]) //=. Qed.

End inversion_protocol.


(* ========================================================================== *)
(** * Verification. *)

Section verification.

  (* ------------------------------------------------------------------------ *)
  (** Ghost Theory. *)

  Section ghost_theory.
    Context {A : Type}.

    (* We use ghost variables with contents in the CMRA [Auth(Ex(List A))]. *)
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    (* The assertion [own γ (●E Ys)] states that the handler
       has seen the elements [Ys]. *)
    Definition handlerView γ Ys : iProp Σ :=
      own γ (●E (Ys : ofe_car (leibnizO (list A)))).
    (* The assertion [own γ (◯E Xs)] states that [iter]
       has seen the elements [Xs]. *)
    Definition iterView γ Xs : iProp Σ :=
      own γ (◯E (Xs : ofe_car (leibnizO (list A)))).

    (* Create a new ghost cell from this CMRA. *)
    (* In the verification of [invert], the ghost variable [γ]
       initially holds the empty list. *)
    Lemma new_cell Zs : ⊢ (|==> ∃ γ, handlerView γ Zs ∗ iterView γ Zs)%I.
    Proof.
      iMod (own_alloc ((●E (Zs : ofe_car (leibnizO (list A)))) ⋅
                       (◯E (Zs : ofe_car (leibnizO (list A)))))) as (γ) "[??]";
      [ apply excl_auth_valid | eauto with iFrame ]; done.
    Qed.

    (* Handler and [iter]'s views are in agreement. *)
    Lemma confront_views γ Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs -∗ ⌜ Xs = Ys ⌝.
    Proof.
      iIntros "Hγ● Hγ◯".
      by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
    Qed.

    (* With the ownership of both views, one can update the contents of [γ]. *)
    Lemma update_cell γ Zs Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs ==∗ handlerView γ Zs  ∗ iterView γ Zs.
    Proof.
      iIntros "Hγ● Hγ◯".
      iMod (own_update_2 _ _ _ (●E (Zs : ofe_car (leibnizO (list A))) ⋅
                                ◯E (Zs : ofe_car (leibnizO (list A))))
        with "Hγ● Hγ◯") as "[$$]";
      [ apply excl_auth_update |]; done.
    Qed.

  End ghost_theory.

  (* ========================================================================== *)
  (** * Specification. *)

  (* The specification of [invert] depends on (1) the specification of a
   iteration method [isIter] and (2) the specification of a lazy sequence
   [isSeq], both of which are introduced in the theory [iteration.v]. *)

  Section specification.
    Context `{!osirisGS Σ}.
    Context {A : Type} `{Encode A, FinitelyObservable A}.

    (* ------------------------------------------------------------------------ *)
    (** Specification of [invert]. *)

    Definition env := stdlib_env.

    Definition invert_spec invert : iProp Σ :=
      ∀ (iter : val),
      isIter iter -∗
      (∀ ι, EWP (call_anonfun env invert [iter]) <|(ι, ⊥)|> {{ ensures k, isSeq ⊥ k [] }}).

  End specification.

  Section invert_correct.
    Context `{!osirisGS Σ}.
    Context  {A : Type} `{Encode A, FinitelyObservable A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    Lemma yield_handler_correct l (iter yield : val) γ (Ys : list A) :
      handlerView γ Ys -∗
      (∀ ι, deep_handler_spec ⊤ ι (ψ_yield l (iterView γ))
        (ensures _, ∃ Xs : list A, iterView γ Xs ∗ ⌜complete Xs⌝)
        (λ o, eval_branches
           ("__osiris_anonymous_arg" ~> VUnit;
            "yield" ~> yield;
            "Yield" ~> VLoc l;
            "iter" ~> iter;
            "__osiris_anonymous_arg" ~> iter;
            env)
           o
           __branches3)
        ⊥ (ensures h, isHead ⊥ h Ys)).
    Proof.
      iLöb as "IH" forall (Ys γ).
      iIntros "HhandlerView %ι".
      prove_handler_spec.

      (* Value and Exception case: *)
      { iIntros ([o | ?]); [ | iIntros "[]"].
        iIntros "[%Xs [HiterView %Hcomplete]]".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        iModIntro.
        next_branch.
        simpl_eval. Ret. by iPureIntro. }

      (* Effectful case: *)
      { iIntros (v k) "HProt !>".
        (* Inversion on the [allows perform]. *)
        rewrite /prot; iPoseProof (upcl_yield with "HProt") as "HProt".
        iDestruct "HProt" as "[%Xs [%X [-> [[HiterView %Hpermitted] HProt]]]]".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        (* Update the handler and iterator views. *)
        iApply ewp_fupd;
          iMod (update_cell γ (Ys ++ [X]) with "HhandlerView HiterView")
          as "[HhandlerView HiterView]";
          iModIntro.
        next_branch.
        next_branch; last tauto.

        (* [Seq.Cons (x, fun () -> continue k ())]. *)
        simpl_eval.
        Par. { iApply ewp_widen. apply pure_wp_ret. apply eq_refl. iIntros (v <-). iPureIntro. apply eq_refl. }
        Par. iApply ewp_value. iPureIntro. apply eq_refl. iApply ewp_value. simpl.
        instantiate (1 := fun l => ⌜l = []⌝%I). equality.
        iIntros (?? <- ->). iApply ewp_value. simpl.
        instantiate (1 := fun l => ⌜l = [VClo _ __fun2]⌝%I). iPureIntro. reflexivity.
        iIntros (v1 v2 <- ->). simpl. Ret. simpl.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iSplit; [ by iPureIntro | ] ].
        (* Goal: [isSeq ⊥ (fun () -> continue k ()) (Ys ++ [X])]. *)
        rewrite !isSeq_unfold /isSeq_pre.
        iExists ι. iApply ewp_call_nonrec.
        simpl_eval.
        iApply ewp_handle_ret.
        simpl_wrap_eval_branches. simpl_eval_branches. simpl_eval_pat.
        simpl_eval. simpl. Par. iApply ewp_value. instantiate (1 := fun k' => ⌜k = k'⌝%I). equality.
        iApply ewp_value. instantiate (1 := fun t => ⌜t = VUnit⌝%I). equality.
        iIntros "!>" (?? <- ->). simpl.
        (* Goal: Result of resuming [k] is a Head of [T]. *)
        iApply ("HProt" with "HiterView").
        (* Use induction hypothesis on the handler. *)
        rewrite /deep_handler_spec seal_eq.
        iApply ("IH" $! (Ys ++ [X]) γ with "HhandlerView"). }
    Qed.

    Definition invert := __fun9.

    Lemma ewp_invert : ⊢ invert_spec invert.
      iIntros (iter) "Hiter %ι".
      (* Initialise handler view and iterator view. *)
      iApply ewp_fupd.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]"; iModIntro.
      unfold call_anonfun. simpl. unfold eval_anonfun.
      simpl_eval; simpl.
      Transparent call. unfold call. simpl. iApply ewp_please.
      (* [fun iter -> ...] has been translated as
         [fun x -> match x with | iter -> ...]. *)
      iModIntro.
      prove_simple_match. { simpl_eval. Ret. equality. }
      iModIntro.
      next_branch.

      (* [let open struct ...] *)
      iApply ewp_ELetOpen.
      (* Subgoal: [EWP eval_mexpr η (MStruct []) {{ ... }}]. *)
      simpl_eval_mexpr.
      iApply ewp_alloc. iIntros "!>" (l) "Hl". Ret. simpl.
      iExists _; iSplit; [ iPureIntro; reflexivity | ].

      (* [let yield x = ...] *)
      iApply (ewp_ELet_PVar_1
                (λ v,
                  □ ∀ (Xs : list A) (X : A),
                    iterView γ Xs -∗
                    ⌜permitted (Xs ++ [X])⌝ -∗
                    (∀ ι, EWP call v #X <| (ι, ψ_yield l (iterView γ)) |>
                      {{ ensures _, iterView γ (Xs ++ [X]) }}) )%I).
      { simpl_eval. Ret.
        iIntros "!>" (Xs X) "Hiter Hpermitted %ι'".
        iApply ewp_call_nonrec.
        iNext.
        iApply ewp_EPerform.
        { iApply ewp_EXData. simpl. reflexivity.
          instantiate (1 := [fun x' => ⌜x' = #X⌝%I]).
          Opaque eval.
          simpl.
          iSplit; [ | done ].
          iApply ewp_EPath. Ret. equality.
          iIntros (?) "Hlist".
          iPoseProof (big_sepL2_length with "Hlist") as "%Hlength".
          destruct vs; [ discriminate | destruct vs; [ | discriminate ]].
          simpl.
          iDestruct "Hlist" as "[-> _]".
          instantiate (1 := fun (v : val) => ⌜v = VXData _ _⌝%I).
          iPureIntro. reflexivity. }
        iIntros (? ->).
        iApply ewp_perform.
        rewrite /prot; iApply upcl_yield.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iFrame ].
        by iIntros. }

      iIntros (yield) "#yield_spec".

      (* fun () -> match iter yield with ... *)
      unfold deco, __exp6. simpl.
      Transparent eval. simpl_eval. Ret.
      rewrite /= isSeq_unfold /isSeq_pre.
      iExists ι.
      iApply ewp_call_nonrec.
      (* [fun () -> ... ] has been translated as
         [fun x -> match x with | () -> ... ]. *)
      iNext.
      prove_simple_match. { simpl_eval. Ret. equality. }
      simpl_eval_branches; simpl_eval_pat; simpl try2; fold eval.

      (* [match_with iter yield { ...] *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler ⊤ ι
                (* Handlee's protocol: *)
                (ψ_yield l (iterView γ))
                (* Handlee's postcondition: *)
                (ensures _, ∃ (Xs : list A), iterView γ Xs ∗ ⌜ complete Xs ⌝)%I
               with "[Hiter HiterView] [HhandlerView]").

      (* Subgoal: The body of the match [iter yield] produces
         [iterView γ Xs], where [Xs] is the full collection. *)
      { iApply (ewp_EApp).
        { iApply ewp_EPath; Ret; equality. }
        { iApply ewp_EPath; Ret; equality. }
        iApply ("Hiter" with "[] HiterView").
        iIntros "!>" (Xs X) "#Hpermitted HI %ι'".
        iApply ("yield_spec" with "HI Hpermitted"). }

      (* Subgoal: The branches of the match constitute
         a valid handler for yield. *)
      { iApply (yield_handler_correct with "HhandlerView"). }
   Qed.

End invert_correct.

End verification.
