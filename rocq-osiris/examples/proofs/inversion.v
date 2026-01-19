From stdpp Require Import telescopes.
From iris.proofmode Require Import base ltac_tactics classes environments.
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

  Definition Iter_spec ι : val → microvx → iProp Σ :=
    λ f m,
      (∀ Ψ E I,
        □ iSpec τ[A] f (λ (X : A) m,
            ∀ (Xs : list A),
              ⌜permitted (Xs ++ [X])⌝ -∗
              I Xs -∗
              EWP[ι] m @ E <| Ψ |> {{ ensures #tt, I (Xs ++ [X]) }}) -∗
        I [] -∗
        EWP[ι] m @ E <|Ψ|> {{ ensures #tt, ∃ Xs, I Xs ∗ ⌜complete Xs⌝ }})%I.

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
    (isSeq :  thread -d> iEff Σ -d> val -d> list A -d> iPropO Σ)
           :  thread -d> iEff Σ -d> val -d> list A -d> iPropO Σ  :=
    λ ι Ψ h Xs,
      match h with
      | VData "Nil" [] =>
          ⌜ complete Xs ⌝
      | VData "Cons" p =>
          ∃ (X : A) k, ⌜ p = [ #X; #k]⌝ ∧
                 ⌜ permitted (Xs ++ [X]) ⌝ ∗ ▷ isSeq ι Ψ k (Xs ++ [X])
      | _ =>
          False
      end%I.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead Ψ1 Ψ2 h Xs]. *)
  Definition isSeq_pre
    (isSeq :  thread -d> iEff Σ -d> val -d> list A -d> iPropO Σ)
           : (thread -d> iEff Σ -d> val -d> list A -d> iPropO Σ) :=
    λ ι Ψ k Xs,
      iSpec τ[unit] k (λ _ m,
          EWP[ι] m <| Ψ |> {{ ensures h, isHead_pre isSeq ι Ψ h Xs }})%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isHead_pre_contractive : Contractive isSeq_pre.
  Proof.
    rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq ι Ψ k us.
    Transparent iSpec. unfold iSpec. Opaque iSpec.
    f_equiv. f_equiv.
    f_equiv=>?. simpl. repeat (f_contractive || f_equiv). by apply HisSeq.
  Qed.
  Definition isSeq_def :
    thread -d> iEff Σ -d> val -d> list A -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold ι Ψ k us :
    isSeq ι Ψ k us ⊣⊢ isSeq_pre isSeq ι Ψ k us.
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

    Definition invert_spec ι : val → microvx → iProp Σ :=
      λ (iter : val) m,
      (iSpec τ[val] iter (Iter_spec ι) -∗
       EWP[ι] m <|⊥|> {{ ensures k, isSeq ι ⊥ k [] }})%I.

  End specification.

  Section invert_correct.
    Context `{!osirisGS Σ}.
    Context  {A : Type} `{Encode A, FinitelyObservable A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    Lemma yield_handler_correct ι l γ (Ys : list A) η :
      lookup_name η "Yield" = ret (VLoc l) →
      handlerView γ Ys -∗
      (deep_handler_spec ⊤ ι (ψ_yield l (iterView γ))
        (ensures #tt, ∃ Xs : list A, iterView γ Xs ∗ ⌜complete Xs⌝)
        (λ o, eval_branches η o __branches3)
        ⊥ (ensures h, isHead ι ⊥ h Ys)).
    Proof.
      intros Hlookup.
      iLöb as "IH" forall (Ys γ).
      iIntros "HhandlerView".
      prove_handler_spec.

      (* Value and Exception case: *)
      { iIntros ([o | ?]); [ | iIntros "[]"]. simpl.
        iIntros "(%v & -> & Htemp)". destruct v.
        iDestruct "Htemp" as "(%Xs & HiterView & %Hcomplete)".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        iModIntro.
        iApply deep_handle_cons.
        { iPureIntro. ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
        iSplit; [ iIntros (? <-) | iIntros ([]) ].
        simpl_eval. iApply ewp_ret. by iPureIntro. }

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
        next_branch. iIntros (? []).
        next_branch; last tauto; iIntros (? ->).

        (* [Seq.Cons (x, fun () -> continue k ())]. *)
        iApply (ewp_EData _ _ _ _ _ [_;_] with "[-]").
        simpl; fold eval; iSplitR.
        { simpl_eval. iApply ewp_ret. instantiate (1 := (λ v, ⌜v = #X⌝)%I). equality. }
        { (* [fun () -> continue k ()] *)
          iSplit; last done.
          iApply (ewp_EAnon τ[unit]
                    (λ _ m, EWP[ι] m {{ ensures k, isHead ι ⊥ k (Ys ++ [X]) }})%I); simpl.
          iIntros ([]).
          iApply ewp_please; iNext.
          (* [fun () -> ...] is a pattern match on the argument,
             it gets desugared to [fun x -> match x with | () -> ...]. *)
          iApply ewp_EMatch.
          iApply (ewp_deep_handler).
          { simpl_eval. iApply ewp_ret. instantiate (1 := (ensures #v, ⌜v = tt⌝)%I).
            iExists tt; equality. }
          iApply prove_deep_handler_spec.
          iSplit; last first.
          { instantiate (1 := ⊥).
            iIntros (??); rewrite /prot upcl_bottom; iIntros ([]). }
          iIntros ([|]); [ | iIntros ([]) ].
          iIntros "(%u & -> & ->) !>".
          iApply deep_handle_cons; [ iPureIntro | iSplit ].
          { ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
          2: { iIntros ([]). }

          (* [continue k ()] *)
          iIntros (? <-).
          iApply (ewp_EContinue' with "[] [] [-]").
          { simpl_eval. iApply ewp_ret. instantiate (1 := (λ k', ⌜k' = k⌝)%I).
            iExists _; equality. }
          { iApply ewp_EUnit_forward. }
          iIntros (?? ->) "(-> & _)".
          iSpecialize ("HProt" with "HiterView").
          iSpecialize ("IH" with "HhandlerView").
          iApply "HProt". iIntros "!>".
          rewrite /deep_handler_spec seal_eq. iApply "IH". }

        iIntros (?) "Hargs".
        iPoseProof (big_sepL2_cons_inv_r with "Hargs") as "(%v & %vs' & -> & -> & Hargs)".
        iPoseProof (big_sepL2_cons_inv_r with "Hargs") as "(%v & %vs & -> & Hspec & Hargs)".
        iPoseProof (big_sepL2_nil_inv_r with "Hargs") as "->".
        iFrame "%". iExists (v). rewrite <- solve_encode_val. iSplit; first equality.
        iNext. rewrite isSeq_unfold /isSeq_pre. rewrite isHead_unfold.
        iApply "Hspec". }
    Qed.

    Definition invert := (EAnonFun __fun9).

    Lemma ewp_invert ι η : ⊢ EWP[ι] (eval η invert) {{ ensures c, □ iSpec τ[val] c (invert_spec ι) }}.
      iApply (ewp_EAnon_pers τ[val]); simpl.
      iIntros "!>" (iter) "Hiter". iApply ewp_please; iNext.
      iApply ewp_EMatch.
      iApply (ewp_deep_handler).
      { simpl_eval. iApply ewp_ret.
        instantiate (1 := (ensures v, ⌜v = iter⌝)%I). equality. }
      iApply prove_deep_handler_spec.
      iSplit; last first.
      { instantiate (1 := ⊥).
        iIntros (??); rewrite /prot upcl_bottom; iIntros ([]). }
      iIntros ([|]); [ | iIntros ([]) ].
      iIntros "-> !>".
      iApply deep_handle_cons; [ iPureIntro | iSplit ].
      { ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
      2: { iIntros ([]). }
      iIntros (? <-).

      (* Initialise handler view and iterator view. *)
      iApply ewp_fupd.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]"; iModIntro.

      (* [let open struct ...] *)
      iApply ewp_ELetOpen.
      (* Subgoal: [EWP eval_mexpr η (MStruct []) {{ ... }}]. *)
      iApply ewp_module. iApply ewp_sitems_extend.
      iIntros ([η' δ']) "(%l & -> & Hl)"; clear η' δ'.
      iApply ewp_sitems_nil. simpl.
      iExists _; iSplit; first equality. fold eval.

      (* [let yield x = ...] *)
      iApply (ewp_ELet_PVar_1 (λ v, □ iSpec τ[A] v (λ (X : A) m,
                                        ∀ (Xs : list A),
                                          ⌜permitted (Xs ++ [X])⌝ -∗
                                          iterView γ Xs -∗
                                          EWP[ι] m <| ψ_yield l (iterView γ) |>
                                          {{ ensures #tt, iterView γ (Xs ++ [X]) }}))%I).
      { iApply (ewp_EAnon_pers τ[A]). simpl.
        iIntros "!>" (X Xs) "Hiter Hpermitted".
        iApply ewp_please; iNext.
        iApply ewp_EPerform.
        { iApply ewp_EXData. simpl. reflexivity.
          instantiate (1 := [fun x' => ⌜x' = #X⌝%I]).
          simpl. fold eval.
          iSplit; [ | done ].
          iApply ewp_EPath. iApply ewp_ret. equality.
          iIntros (?) "Hlist".
          iPoseProof (big_sepL2_cons_inv_r with "Hlist") as "(%x1 & %vs' & -> & -> & Hlist)".
          iPoseProof (big_sepL2_nil_inv_r with "Hlist") as "->".
          instantiate (1 := fun (v : val) => ⌜v = VXData _ _⌝%I).
          iPureIntro. reflexivity. }
        iIntros (? ->).
        iApply ewp_perform.
        rewrite /prot; iApply upcl_yield.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iFrame ].
        iIntros; iExists tt; iSplit; [ equality | iAssumption ]. }

      iIntros (yield) "#yield_spec".

      (* fun () -> match iter yield with ... *)
      iApply (ewp_mono with "[-]"); last first.
      { instantiate (1 := (ensures k, _)%I).
        iIntros ([|]); [ | iIntros ([]) ].
        iIntros "Ho". simpl.
        rewrite isSeq_unfold /isSeq_pre /=.
        iExact "Ho". }
      iApply (ewp_EAnon τ[unit]).
      iIntros ([]).
      iApply ewp_please; iNext.
      (* [fun () -> ... ] has been translated as
         [fun x -> match x with | () -> ... ]. *)
      prove_simple_match. { simpl_eval. iApply ewp_ret. equality. }
      simpl_eval_branches; simpl_eval_pat; simpl try2; fold eval.

      (* [match_with iter yield { ...] *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler ι ⊤
                (* Handlee's protocol: *)
                (ψ_yield l (iterView γ))
                (* Handlee's postcondition: *)
                (ensures #tt, ∃ (Xs : list A), iterView γ Xs ∗ ⌜ complete Xs ⌝)%I
               with "[Hiter HiterView] [HhandlerView]").

      (* Subgoal: The body of the match [iter yield] produces
         [iterView γ Xs], where [Xs] is the full collection. *)
      { iApply (ewp_EApp τ[val] with "[Hiter]").
        { iApply ewp_EPath; iApply ewp_ret; iAssumption. }
        { instantiate (1 := (λ x, ⌜x = yield⌝)%I).
          iApply ewp_EPath; iApply ewp_ret; iExists _; equality. }
        iIntros (? -> m) "Hiter !>".
        rewrite /Iter_spec /tapp.
        iApply ("Hiter" with "yield_spec HiterView"). }

      { rewrite <- isHead_unfold.
        iApply (yield_handler_correct ι l with "HhandlerView").
        reflexivity. }
   Qed.

End invert_correct.

End verification.
