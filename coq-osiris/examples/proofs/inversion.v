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
           EWP (call f #X) @ E <| ψ |> {{ λ _, I (Xs ++ [X]) }})
      -∗
      I [] -∗
      EWP (call iter f) @E <| ψ |>
        {{ λ _, ∃ Xs, I Xs ∗ ⌜ complete Xs ⌝ }}.

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
      | VData "Nil" (VTuple [])       =>
          ⌜ complete Xs ⌝
      | VData "Cons" p =>
          ∃ X k, ⌜ p = #(X, k) ⌝ ∧
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
      EWP (call k #()) <| Ψ |> {{ RET h, isHead_pre isSeq Ψ h Xs }}%I.

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

Definition yield l x : val := VXData l (VTuple [x]).

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
      EWP (call_anonfun env invert [iter]) {{ RET k, isSeq ⊥ k [] }}.

  End specification.

  Section invert_correct.
    Context `{!osirisGS Σ}.
    Context  {A : Type} `{Encode A, FinitelyObservable A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    Lemma yield_handler_correct l (iter yield : val) γ (Ys : list A) :
      handlerView γ Ys -∗
      deep_handler_spec ⊤ (ψ_yield l (iterView γ))
        (λ _ : outcome2 val exn, ∃ Xs : list A, iterView γ Xs ∗ ⌜complete Xs⌝)
        (λ o : code.outcome3 val exn,
            deep_handler_body
              ("__osiris_anonymous_arg" ~> VUnit;
               "yield" ~> yield;
               "Yield" ~> VLoc l;
               "iter" ~> iter;
               "__osiris_anonymous_arg" ~> iter;
               env) o __branches3 __branches3) ⊥ (RET h, isHead ⊥ h Ys).
    Proof.
      iLöb as "IH" forall (Ys γ).
      iIntros "HhandlerView".
      rewrite deep_handler_spec_unfold /deep_handler_spec_pre.
      iSplit.
      (* Value and Exception case: *)
      { iIntros (o) "[%Xs [HiterView %Hcomplete]]".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        destruct o; red_match;
          with_strategy transparent [evals] Simp; Ret; by iPureIntro. }

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
        red_match.

        (* [Seq.Cons (x, fun () -> continue k ())]. *)
        with_strategy transparent [evals] Simp; Ret; simpl.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iSplit; [ by iPureIntro | ] ].
        (* Goal: [isSeq ⊥ (fun () -> continue k ()) (Ys ++ [X])]. *)
        rewrite !isSeq_unfold /isSeq_pre.
        with_strategy transparent [extend eval_match evals]
          Simp; Bind; Bind; Simp; Ret; Bind; Simp; Ret; simpl.
        (* Goal: Result of resuming [k] is a Head of [T]. *)
        iApply ("HProt" with "HiterView").
        (* Use induction hypothesis on the handler. *)
        rewrite /deep_handler_spec seal_eq.
        iApply ("IH" $! (Ys ++ [X]) γ with "HhandlerView"). }
    Qed.

    Definition invert := __fun9.

    Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).


    Lemma ewp_ELet_singleton_var spec η x e e' ψ Q :
      EWP eval η e <| ψ |> {{ RET v, spec v }} -∗
      (∀ v, spec v -∗ EWP eval ((x, v) :: η) e' <| ψ |> {{ Q }}) -∗
      EWP eval η (ELet [Binding (PVar x) e] e') <| ψ |> {{ Q }}.
    Proof.
      iIntros "He He'".
      rewrite !eval_eval' /=.
      with_strategy transparent [eval_bindings] simpl.
      Par. Bind.
      iApply (ewp_mono with "[He]"). by rewrite eval_eval'.
      iIntros ([|]); [ simpl | done ].
      iIntros "Hspec".
      with_strategy transparent [extend] simpl.
      by iApply "He'".
    Qed.

    Lemma ewp_invert : ⊢ invert_spec invert.
      iIntros (iter) "Hiter".
      (* Initialise handler view and iterator view. *)
      iApply ewp_fupd.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]"; iModIntro.

      Call.
      (* [fun iter -> ...] has been translated as
         [fun x -> match x with | iter -> ...]. *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler _ ⊥ (ieq ?[y])).
      { Simp. by Ret. }
      rewrite deep_handler_spec_unfold; iSplit; last first.
      (* Trivially discard the effect case. *)
      { iIntros "!#" (??) "HF".
        by iPoseProof (upcl_bottom with "HF") as "F". }
      iIntros (? ->) "!> !>".
      enter_branch.

      (* [let open struct ...] *)
      iApply ewp_ELetOpen.
      (* Subgoal: [EWP eval_mexpr η (MStruct []) {{ ... }}]. *)
      Local Transparent eval_mexpr. simpl. Local Opaque eval_mexpr.
      iApply ewp_alloc. iIntros "!>" (l) "Hl". Ret. simpl.
      iExists _; iSplit; [ iPureIntro; reflexivity | ].

      (* [let yield x = ...] *)
      iApply (ewp_ELet_singleton_var
                (λ v,
                  □ ∀ (Xs : list A) (X : A),
                    iterView γ Xs -∗
                    ⌜permitted (Xs ++ [X])⌝ -∗
                    EWP call v #X <| ψ_yield l (iterView γ) |>
                      {{ λ _, iterView γ (Xs ++ [X]) }} )%I).
      { Simp; Ret; simpl.
        iIntros "!>" (Xs X) "Hiter Hpermitted".
        iApply ewp_call_nonrec.
        iNext.
        with_strategy transparent [evals] Simp.
        iApply ewp_perform.
        rewrite /prot; iApply upcl_yield.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iFrame ].
        by iIntros. }

      iIntros (yield) "#yield_spec".

      (* fun () -> match iter yield with ... *)
      Simp; Ret. rewrite /= isSeq_unfold /isSeq_pre.
      iApply ewp_call_nonrec.
      (* [fun () -> ... ] has been translated as
         [fun x -> match x with | () -> ... ]. *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler _ _ (ieq ?[y])).
      { Simp; by Ret. }
      rewrite deep_handler_spec_unfold; iSplit; last first.
      (* Trivially discard the effect case. *)
      { iIntros "!>" (??) "HF".
        by iPoseProof (upcl_bottom with "HF") as "F". }
      iIntros (? ->) "!> !>".
      enter_branch.

      (* [match_with iter yield { ...] *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler ⊤
                (* Handlee's protocol: *)
                (ψ_yield l (iterView γ))
                (* Handlee's postcondition: *)
                (λ _, ∃ (Xs : list A), iterView γ Xs ∗ ⌜ complete Xs ⌝)%I
               with "[Hiter HiterView] [HhandlerView]").

      (* Subgoal: The body of the match [iter yield] produces
         [iterView γ Xs], where [Xs] is the full collection. *)
      { Simp.
        iApply ("Hiter" with "[] HiterView").
        iIntros "!>" (Xs X) "#Hpermitted HI".
        iApply ("yield_spec" with "HI Hpermitted"). }

      (* Subgoal: The branches of the match constitute
         a valid handler for yield. *)
      { iApply (yield_handler_correct with "HhandlerView"). }
   Qed.

End invert_correct.

End verification.
