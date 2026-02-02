From Stdlib Require Import Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import thread_step ewp tactics.

From osiris.program_logic.pure Require Export pure.

(** *Basic rules on the program logic

  This file contains the "basic" rules of how to use the program logic.

  i.e.
  (1) How to reason about expressions at the [micro] monad level and
  (2) Proof that the weakest precondition is closed under [simp]
      (see [ewp_simp]). *)

(* ------------------------------------------------------------------------ *)

Section ewp_basic_rules.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  Context {A X : Type}.
  Context {E : coPset} {Ψ : iEff Σ} {Q : outcome2 A X → iProp Σ}.

  Implicit Type m : micro A X.

  (* Values *)
  Lemma ewp_ret v :
    Q (O2Ret v) -∗ ewp_def E (ret v : micro A X) Ψ Q.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_ret_inv v :
    ewp_def E (Ret v : micro A X) Ψ Q ={E}=∗ Q (O2Ret v).
  Proof.
    iIntros "HRet".
    by rewrite ewp_unfold /ewp_pre.
  Qed.

  Lemma ewp_throw (e : X) :
    Q (O2Throw e) -∗ ewp_def E (Throw e : micro A X) Ψ Q.
  Proof. iIntros "Hζ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw_inv v :
    ewp_def E (Throw v : micro A X) Ψ Q ={E}=∗ Q (O2Throw v).
  Proof.
    iIntros "HThrow".
    by rewrite ewp_unfold /ewp_pre.
  Qed.

  Lemma ewp_crash_inv :
    ewp_def E (Crash : micro A X) Ψ Q ={E}=∗ False.
  Proof.
    ewp_unfold (@Crash A X).
    by iIntros "Hsi".
  Qed.

  Lemma ewp_outcome2 o :
    Q o -∗ ewp_def E (inject2 o : micro A X) Ψ Q.
  Proof.
    iIntros "HΦ". destruct o; simpl.
    - by iApply ewp_ret.
    - by iApply ewp_throw.
  Qed.

  Lemma ewp_outcome2_inv o :
    ewp_def E (inject2 o : micro A X) Ψ Q ={E}=∗ Q o.
  Proof.
    iIntros "Hv".
    ewp_unfold (inject2 o); by destruct o.
  Qed.

  Lemma ewp_outcome2_fupd o :
    (|={E}=> Q o) -∗ ewp_def E (inject2 o : micro A X) Ψ Q.
  Proof.
    iIntros "HΦ".
    rewrite ewp_unfold /ewp_pre.
    by destruct o.
  Qed.

  (* ------------------------------------------------------------------------ *)

  Lemma ewp_step {σ π σ'} m m' μ :
    thread_step (σ, m, dom π) (σ', m', μ) →
    state_interp (σ, π) -∗
    ewp_def E m Ψ Q ==∗
    |={E}[∅]▷=>
        ewp_def E m' Ψ Q ∗
          (match μ with
           | None => state_interp (σ', π)
           | Some (ι', m') => ∃ φ' γ, state_interp (σ', <[ι':= γ]>π) ∗
                                        saved_prop.saved_pred_own γ DfracDiscarded φ' ∗
                                        ewp_def E m' ⊥ (λ o, □ φ' o)
          end).
  Proof.
    intros Hstep.
    iIntros "Hsi Hwp".
    ewp_unfold m.
    ewp_case m.
    spec_state. iModIntro. iMod "Hwp" as "[%Hprog Hwp]".
    spec_step.
    by ewp_mask_elim.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_mono m Q' :
    ewp_def E m Ψ Q' -∗
    (∀ o, Q' o -∗ Q o) -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros "Hwp Hmono".
    iLöb as "IH" forall (m).
    ewp_unfold m.
    ewp_case m.
    (* Case: [m] is a [WPOutcome] *)
    { iMod "Hwp"; iModIntro.
      iApply ("Hmono" with "Hwp"). }

    (* Case: [m] is a [WPCrash]. *)
    { done. }

    { (* Case: [m] is a [WPPerform]. We use [prot_mono]. *)
      iMod "Hwp" as "(%Φ & $ & Hwp)"; iModIntro.
      iIntros (w) "Hewp".
      iSpecialize ("Hwp" with "Hewp"); iNext.
      by iApply ("IH" with "Hwp Hmono"). }

    { (* Case: [m] is a [WPStep]. *)
      intro_state. spec_state. iModIntro.
      discharge_pure assumption.
      clear Hstep.
      iIntros (σ' m' μ) "%Hstep".
      spec_step.
      ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
      iApply ("IH" with "Hwp Hmono"). }

    { (* Case: [m] is a [WPJoin]. *)
      intro_state. spec_state.
      iMod "Hwp". iModIntro.
      destruct (π !! t) eqn:Hlookup; last done.
      iDestruct "Hwp" as "(%φ'0 & $ & Hwp)".
      iIntros "!> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
      iApply ("IH" with "Hwp Hmono"). }
  Qed.

  Lemma ewp_prot_mono m Ψ' :
    (Ψ' ⊑ Ψ)%ieff -∗
    ewp_def E m Ψ' Q -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros "#Hmono Hwp".
    iLöb as "IH" forall (m).
    ewp_unfold m.
    ewp_case m; try done.

    { (* Case: [m] is a [WPPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iDestruct "Hwp" as (φ) "(Hwp & HΨ)"; iExists φ.
      iSplitL "Hwp"; first iApply ("Hmono" with "Hwp"); cbn.
      iIntros (?) "Hφ". iSpecialize ("HΨ" with "Hφ").
      iNext; iApply ("IH" with "HΨ"). }

    { (* Case: [m] is a [WPStep]. *)
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. spec_step.
      ewp_mask_elim.
      iMod "Hwp" as "(Hwp & $)".
      by iApply ("IH" with "Hwp"). }

    { (* Case: [m] is a [WPJoin]. *)
      intro_state. spec_state. iMod "Hwp"; iModIntro.
      destruct (π !! t); last done.
      iDestruct "Hwp" as "(%φ'0 & $ & Hwp)".
      iIntros "!> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim.
      iMod "Hwp" as "(Hwp & $)".
      by iApply ("IH" with "Hwp"). }
  Qed.

  Lemma ewp_pers_smono m E' Q' :
    E' ⊆ E →
    ewp_def E' m Ψ Q' -∗
    □ (∀ v, Q' v ={E}=∗ Q v) -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros (HE) "He HΦ".
    iRevert "HΦ".
    iLöb as "IH" forall (A X m Ψ Q Q').
    iIntros "#HΦ".
    ewp_unfold m.
    ewp_case m.
    { (* Cases: [WPOutcome] *)
      iApply ("HΦ" with "[> -]"); by iApply (fupd_mask_mono E' E). }
    (* Case: [WPCrash] *)
    { by iApply (fupd_mask_mono E' E). }
    (* Case: [WPPerform] *)
    { iApply (fupd_mask_mono E' E); first done.
      iMod "He" as "(%Φ & $ & Hewp)"; iModIntro.
      iIntros (o) "Ho".
      iSpecialize ("Hewp" with "Ho"); iNext.
      iApply ("IH" with "Hewp HΦ"). }
    { (* Case: [WPStep] *)
      intro_state.
      iMod (fupd_mask_subseteq E') as "Hclose"; first done.
      spec_state. iModIntro. construct_wp_nonret.
      spec_step. ewp_mask_elim.
      iDestruct "He" as ">(H & Hforked)".
      iMod "Hclose"; iModIntro.
      iSplitL "H"; first by iApply ("IH" with "H HΦ").
      destruct μ as [ [ι' mforked] | ]; last iFrame.
      iDestruct "Hforked" as "(%φ' & %γ & Hsi & Hsaved & Hwp)".
      iFrame. iApply ("IH" with "Hwp").
      auto. }
    { (* Case: [WPJoin] *)
      intro_state.
      iMod (fupd_mask_subseteq E') as "Hclose"; first done.
      spec_state. iMod "He"; iModIntro.
      destruct (π !! t).
      - iDestruct "He" as "(%φ' & $ & He)".
        iIntros "!> %o Ho". iSpecialize ("He" with "Ho").
        ewp_mask_elim.
        iDestruct "He" as ">(H & Hforked)".
        iMod "Hclose"; iModIntro. iFrame.
        iApply ("IH" with "H HΦ").
      - iMod "He". iMod "Hclose". iModIntro. done. }
  Qed.

  Lemma ewp_pers_mono m Q' :
    ewp_def E m Ψ Q' -∗
    □ (∀ o, Q' o ={E}=∗ Q o) -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros "He #Hmono".
    iApply (ewp_pers_smono with "He"). set_solver.
    by iIntros "!>".
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd_post m :
    ewp_def E m Ψ (λ o, |={E}=> Q o) -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros "He".
    iApply (ewp_pers_mono with "He"); auto.
  Qed.

  Lemma ewp_fupd m :
    (|={E}=> ewp_def E m Ψ Q) -∗
    ewp_def E m Ψ Q.
  Proof.
    iIntros "He".
    ewp_unfold_all.
    ewp_case m; try iMod "He"; done.
  Qed.

End ewp_basic_rules.

(* ------------------------------------------------------------------------ *)
(* Invert cases where there are premises of the form
          [EWP (ret _) _] [EWP crash _] or [EWP (throw _) _] *)

Ltac ewp_invert :=
  lazymatch goal with
  (* EWP throw *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
      iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
  (* EWP ret *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
      iPoseProof (ewp_ret_inv with "[$]") as "HΦ"
  (* EWP crash *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ Crash _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "%"
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (crash _) _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "%"
  end.

(* ------------------------------------------------------------------------ *)

(* Handler specifications *)

Section handler_specifications.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  (** * Shallow handler specification. *)

  Definition shallow_handler_spec E Ψ (Q : outcome2 val exn → iProp Σ)
    (h : code.outcome3 val exn -> microvx)
    Ψ' Q' :=
    ((* [Return] and [Exception] branch *)
    (∀ o, Q o -∗ ▷ ewp_def E (h o) Ψ' Q') ∧

    (* [Effect] branch *)
    (∀ v k, Ψ allows perform v
          << λ o, ▷ ewp_def E (stop CResume (k, o)) Ψ Q >> -∗
        ▷ ewp_def E (h (O3Perform v k)) Ψ' Q'))%I.

End handler_specifications.

(* -------------------------------------------------------------------------- *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.
  Context {E : coPset} {Ψ : iEff Σ} {Q : outcome2 A X → iProp Σ}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma ewp_stop_perform {B X'} v k (Φ : outcome2 B X' → iProp Σ) :
    Ψ allows perform v << λ w, ▷ ewp_def E (k w) Ψ Φ >> -∗
    ewp_def E (Stop CPerf v k) Ψ Φ.
  Proof.
    iIntros "HP".
    ewp_unfold_head.
    by iModIntro.
  Qed.

  Lemma ewp_perform v (Φ : outcome2 val exn → iProp Σ) :
    Ψ allows perform v << Φ >> -∗
    ewp_def E (perform v) Ψ Φ.
  Proof.
    iIntros "HP".
    iApply ewp_stop_perform.
    iApply (monotonic_prot with "[] HP").
    iIntros (o) "Ho !>".
    iApply (ewp_outcome2 with "Ho").
  Qed.

  Lemma ewp_perform_inv {B X'} v k (Φ : outcome2 B X' → iProp Σ) :
    ewp_def E (Stop CPerf v k) Ψ Φ ={E}=∗
    Ψ allows perform v << λ w, ▷ ewp_def E (k w) Ψ Φ >>.
  Proof.
    ewp_unfold (Stop CPerf v k).
    by iIntros ">HP !>".
  Qed.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle Ψ' Φ' Φ e h:
    ewp_def E e Ψ Φ -∗
    shallow_handler_spec E Ψ Φ h Ψ' Φ' -∗
    ewp_def E (Handle e h) Ψ' Φ'.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)

    iIntros "He Hsh".
    iLöb as "IH" forall (e).
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn; rename π into π'.

    { (* [StepHandleRet] *)
      ewp_invert; iFrame.
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      iMod "Hsh";
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iApply "Hsh". }

    { (* [StepHandleThrow] *)
      ewp_invert; iFrame.
      iDestruct "Hsh" as "(Hsh & _)".
      iSpecialize ("Hsh" with "HΦ");
      iMod "Hsh";
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iApply "Hsh". }

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "He") as "HP".
      iMod "HP".

      iDestruct (gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H | ].

      iAssert (Ψ allows perform e0
                 << fun o => ▷ ewp_def E (stop CResume (l, o)) Ψ Φ >>)%I
        with "[HP HH]" as "HΨ".
      { iApply (monotonic_prot with "[HH] HP").
        iIntros (?) "Hwp"; cbn. iNext.
        rename σ into σ'.
        ewp_unfold_head.
        intro_state. ewp_mask_intro "Hmod".
        iDestruct (gen_heap_valid with "Hsi HH") as %Hl.
        construct_wp_nonret.
        eapply invert_thread_step_resume in Hstep; [ | eexact Hl ].
        destruct Hstep as (-> & -> & ->).
        rewrite try2_inject2_right.
        iDestruct (gen_heap_update with "Hsi HH") as ">(Hsi & HH)".
        iFrame.
        by ewp_mask_elim. }

      iSpecialize ("Hsh" with "HΨ").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iFrame.
      unfold cont; simpl. iApply "Hsh". }

    { (* [StepHandleFork] *)
      ewp_mask_intro "Hmod". iModIntro. iMod "Hmod". iModIntro. iFrame.
      destruct x.
      ewp_unfold_all. intro_state. spec_state. iModIntro.
      destruct Hstep as (? & ? & ? & Htstep).
      destruct_thread_step.
      construct_wp_nonret.
      destruct_thread_step.
      eassert (thread_step (σ'0, Stop CFork (v, v0) k, dom π) _) as Htstep.
      { eapply ForkS. eassumption. }
      spec_step.
      ewp_mask_elim.
      iMod "He" as "(Hwp & $)".
      iModIntro.
      iApply ("IH" with "Hwp Hsh"). }

    { (* [StepHandleJoin] *)
      ewp_mask_intro "Hmod". iModIntro. iMod "Hmod". iModIntro. iFrame.
      ewp_unfold_all. intro_state. spec_state. iMod "He". iModIntro.
      destruct (π !! ι); last done.
      iDestruct "He" as "(%φ' & $ & He)".
      iIntros "!> %o Ho". iSpecialize ("He" with "Ho").
      ewp_mask_elim.
      iMod "He" as "(He & $)". iModIntro.
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      eassert (thread_step (σ, e, dom π') _) as Hstep.
      { apply BaseS. eassumption. }
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ Hstep with "Hsi He") as ">H".
      iMod "H". ewp_mask_elim. iMod "H" as "(H & $)". iModIntro.
      iApply ("IH" with "H Hsh"). }
  Qed.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle_ret (a : val) h:
    ewp_def E (h (O3Ret a)) Ψ Q -∗
    ewp_def E (Handle (ret a) h) Ψ Q.
  Proof.
    destruct Ψ.
    iIntros "Hhandle".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn.

    - iFrame. ewp_mask_intro "Hmod"; ewp_mask_elim; done.
    - exfalso. eapply invert_can_step_Ret; unfold can_step; eauto.
  Qed.

  Lemma ewp_handle_throw (e : exn) h:
    ewp_def E (h (O3Throw e)) Ψ Q -∗
    ewp_def E (Handle (throw e) h) Ψ Q.
  Proof.
    iIntros "Hhandle".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn.

    - iFrame. ewp_mask_intro "Hmod"; ewp_mask_elim; done.
    - exfalso. eapply invert_can_step_Throw; unfold can_step; eauto.
  Qed.

  (* Inversion for [Handle] *)
  Lemma ewp_handle_inv {B Y} k l w (c : _ -> micro B Y) Φ :
    isCont l k -∗
    ewp_def E (Handle (k w) c) Ψ Φ -∗
    ewp_def E (Handle (stop CResume (l, w)) c) Ψ Φ.
  Proof.
    destruct Ψ.
    iIntros "Hl H".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap.gen_heap_valid with "Hsi Hl")  as "%".

    destruct_thread_step.
    eapply invert_step_resume in H; [ destruct H | eauto ]; subst.
    (* Thus, the reduction step must be a successful step. *)

    (* Update the ghost heap. *)
    iMod (gen_heap.gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    ewp_mask_elim. iFrame.
    by rewrite try2_inject2_right.
  Qed.

  (* Variant inversion rule for [Handle] *)
  Lemma ewp_handle_inv' k l w (c : _ -> micro A X)  :
    l ↦ K k -∗
    ▷ (l ↦ Shot -∗
        ewp_def E (Handle (k w) c) Ψ Q) -∗
    ewp_def E (Handle (stop CResume (l, w)) c) Ψ Q.
  Proof.
    destruct Ψ.
    iIntros "Hl H".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap.gen_heap_valid with "Hsi Hl")  as "%".

    destruct_thread_step.
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_resume in H; [ destruct H | eauto ]; subst.

    (* Update the ghost heap. *)
    iMod (gen_heap.gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right.
    iApply ("H" with "Hl").
  Qed.

End wp_handler_rules.

Section ewp_rules.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {Q : outcome2 A X → iProp Σ}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma is_ewp_case_try2_None {B X'} m (f : _ -> micro B X'):
    is_ewp_case m = WPStep ->
    is_ewp_case (try2 m f) = WPStep.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H0; try done.
  Qed.

  Lemma is_ewp_case_try_None {B X'} m (f : A -> micro B X') (h : X -> micro B X'):
    is_ewp_case m = WPStep ->
    is_ewp_case (try m f h) = WPStep.
  Proof.
    intros Hm.
    unfold try.
    by apply is_ewp_case_try2_None.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)

  Lemma ewp_try2 {B X'} m (f : _-> micro B X') Φ :
    ewp_def E m Ψ (λ o, ewp_def E (f o) Ψ Φ) -∗
    ewp_def E (try2 m f) Ψ Φ.
  Proof.
    iIntros "Hwp".
    iLöb as "IH" forall (m).
    ewp_case m.
    (* Case: [m1] is an outcome2. *)
    (* The result is immediate. *)
    { rewrite try2_inject2.
      iPoseProof (ewp_outcome2_inv with "Hwp") as "Hret"; cbn.
      iApply (ewp_fupd with "Hret"). }
    (* Case : [m1] is [crash]; trivial  *)
    { iClear "IH".
      iApply ewp_fupd.
      ewp_unfold (@Crash A X); by iMod "Hwp". }
    (* Case : [m1] is [Perform _ _]. *)
    { cbn.
      ewp_unfold_all.
      iMod "Hwp" as "(% & $ & Hwp)"; iModIntro.
      iIntros (o) "Ho"; iSpecialize ("Hwp" with "Ho"); iNext.
      iApply ("IH" with "Hwp"). }
    { (* If [m] can step, then so can [try m f h]. *)
      pose proof (is_ewp_case_try2_None m f Hhm) as Hhm2.
      ewp_unfold_all. rewrite Hhm. rewrite Hhm2.
      (* Process a step of computation. *)
      intro_state. spec_state.
      iModIntro. apply invert_can_progress in Hstep.
      destruct Hstep as [ Hstep | Hstep ].
      { (* Case: [m1] is [Join _]. *)
        destruct Hstep as (ι' & k & -> & Hdom).
        discriminate.  }
      destruct Hstep as [ Hstep | Hstep ].
      { (* Case: [m1] is [Fork _] *)
        destruct Hstep as (v1 & v2 & k & ->).
        simpl try2. construct_wp_nonret.
        remember (v1, v2) as p.
        destruct_thread_step.
        eassert (thread_step (σ', Stop CFork (v1, v2) k, dom π) _).
        { eapply ForkS. eassumption. }
        spec_step.
        ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
        iModIntro.
        iApply ("IH" with "Hwp"). }
      (* Get more information out of [e2]; *)
      construct_wp_nonret.
      pose proof (can_step_try2 _ _ f Hstep) as Hstep2.
      pose proof (invert_can_step_thread_step _ _ _ _ _ _ Hstep0 Hstep2) as (_ & ->).
      eapply invert_thread_step_try2 in Hstep0; last assumption.
      destruct Hstep0 as (?&->&Hstep0).
      (* Can use information from above to get [wp] about stepped computation *)
      spec_step.
      ewp_mask_elim. iDestruct "Hwp" as ">(Hwp & $)"; iFrame.
      iModIntro.
      (* Apply induction hypothesis  *)
      by iApply ("IH" with "Hwp"). }
    (* Case: [WPJoin] *)
    { simpl. ewp_unfold_all.
      intro_state. spec_state. iMod "Hwp".
      destruct (π !! x); last done.
      iDestruct "Hwp" as "(%φ' & $ & Hwp)".
      iIntros "!> !> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim.
      iMod "Hwp" as "[Hwp $]".
      iModIntro.
      iApply ("IH" with "Hwp"). }
  Qed.

  Lemma ewp_try {B X'} m (f : A -> micro B X') (h : X -> micro B X') Φ :
    ewp_def E m Ψ
      (λ o, match o with
            | O2Ret v => ewp_def E (f v) Ψ Φ
            | O2Throw e => ewp_def E (h e) Ψ Φ
            end) -∗
    ewp_def E (try m f h) Ψ Φ.
  Proof.
    iIntros "Hwp".
    iApply ewp_try2.
    iApply (ewp_mono with "Hwp").
    iIntros ([|]) "Hwp"; by cbn.
  Qed.

  (** *Bind rule *)
  Lemma ewp_bind {B} m (k : _ -> micro B X) Φ :
    ewp_def E m  Ψ
      (λ o, match o with
            | O2Ret v => ewp_def E (k v) Ψ Φ
            | O2Throw e => Φ (O2Throw e)
            end) -∗
    ewp_def E (bind m k) Ψ Φ.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]").
    iIntros ([v|e]).
    - iIntros "$".
    - iIntros "Hexn".
      iApply (ewp_throw with "Hexn").
  Qed.

  (* Par combinator *)

  Lemma ewp_Par {A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X')
    (k: outcome2 (A1 * A2) X' → micro A X) Φ1 Φ2 :
    ewp_def E m1 Ψ Φ1 -∗
    ewp_def E m2 Ψ Φ2 -∗
    (∀ e, Φ1 (O2Throw e) -∗ ▷ ewp_def E (k (O2Throw e)) Ψ Q) ∧
    (∀ e, Φ2 (O2Throw e) -∗ ▷ ewp_def E (k (O2Throw e)) Ψ Q) ∧
    (∀ v1 v2,
       Φ1 (O2Ret v1) -∗ Φ2 (O2Ret v2) -∗
       ▷ ewp_def E (k (O2Ret (v1, v2))) Ψ Q) -∗
    ewp_def E (Par m1 m2 k) Ψ Q.
  Proof.
    iIntros "H1 H2 Hjoin".
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2).

    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn; rename π into π'.

    { (* Case: [StepParRetRet].. *)
      ewp_invert; iRename "HΦ" into "HΦ2"; ewp_invert; iFrame.
      iMod "HΦ". iMod "HΦ2".
      iSpecialize ("Hjoin" with "HΦ HΦ2").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iApply "Hjoin". }

    (* In the four following cases, one of the branches of the [Par] is either a
     [crash] or [throw _].

     We invert the cases where there are premises of the form [WP crash _] or
     [WP (throw _) _] *)
     1-4: ewp_invert; try done.

    (* [StepParThrowLeft/Right] *)
    { iMod "HΦ".
      iDestruct "Hjoin" as "[Hexn1 _]".
      iSpecialize ("Hexn1" with "[$]").
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame. }
    { iMod "HΦ".
      iDestruct "Hjoin" as "[_ [Hexn2 _]]".
      iSpecialize ("Hexn2" with "[$]").
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame. }

    { (* [StepThroughParLeft]. *)
      destruct_code.
      - (* [ParPerformLeft] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        iPoseProof (ewp_perform_inv with "[$]") as "H1".
        iApply ewp_fupd. iMod "H1"; iModIntro.
        iApply ewp_stop_perform.
        iApply (monotonic_prot with "[H2 Hjoin] H1").
        iIntros (?) "Hk".
        iNext.
        iApply ("IH" with "Hk H2 Hjoin").

      - (* Step then [ForkS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (ForkS _ _ _ _ _ _ H0).
        iSpecialize ("H1" $! _ _ _ H1).
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - (* Step then [JoinS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iMod "H1".
        destruct (π !! x); last done.
        iDestruct "H1" as "(%φ' & $ & H1)".
        iIntros "!> !> %o Ho". iSpecialize ("H1" with "Ho").
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hjoin"). }

    { (* [StepThroughParRight]. *)
      destruct_code.

      - (* [StepParPerformRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        iPoseProof (ewp_perform_inv with "[$]") as "H2".
        iApply ewp_fupd. iMod "H2"; iModIntro.
        iApply ewp_stop_perform.
        iApply (monotonic_prot with "[H1 Hjoin] H2").
        iIntros (?) "H2".
        iNext.
        iApply ("IH" with "H1 H2 Hjoin").

      - (* [StepParForkRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (ForkS _ _ _ _ _ _ H0).
        iSpecialize ("H2" $! _ _ _ H1).
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - (* [StepParJoinRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iMod "H2".
        destruct (π !! x); last done.
        iDestruct "H2" as "(%φ' & $ & H2)".
        iIntros "!> !> %o Ho". iSpecialize ("H2" with "Ho").
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hjoin"). }

    { (* [ParLeft] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ Hstep with "Hsi H1") as ">H1".
      iMod "H1". ewp_mask_elim. iMod "H1" as "(H1 & $)".
      iApply ("IH" with "H1 H2 Hjoin"). }

    { (* [ParRight] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ Hstep with "Hsi H2") as ">H2".
      iMod "H2". ewp_mask_elim. iMod "H2" as "(H2 & $)".
      iApply ("IH" with "H1 H2 Hjoin"). }
  Qed.

End ewp_rules.

(* Rules that deal with microvx directly. *)

Section ewp_val_rules.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  (* [CEval]. *)

  Lemma pure_ewp {A X} E Ψ (φ : A → Prop) (ζ : X → Prop) m :
    pure_wp m φ ζ →
    ⊢ ewp_def E m Ψ (ilift (λ e, ⌜ζ e⌝) (λ v, ⌜φ v⌝)).
  Proof.
    iIntros (Hm).
    iLöb as "IH" forall (m Hm).
    iApply ewp_unfold; rewrite /ewp_pre /=.
    ewp_case m.
    - iModIntro. destruct o; iPureIntro.
      + by eapply invert_pure_wp_ret in Hm.
      + by eapply invert_pure_wp_throw in Hm.
    - (* [crash]'s satisfy [ψ] *)
      by eapply invert_pure_wp_crash in Hm.
    - (* [perform] is not immediately pure *)
      by apply invert_pure_wp_stop in Hm.
    - (* Case: [m] can step *)
      intro_state.
      ewp_mask_intro "Hmod".
      assert (∀ σ, can_step (σ, m)) by
        (destruct (pure_wp_progress m Hm) as [(a, ->)|[(e, ->)|]]; auto; discriminate).
      construct_wp_nonret.
      (* and no step can change [σ] or escape [pure] *)
      ewp_cleanup_mod. ewp_mask_elim.
      specialize (H σ).
      apply invert_can_step_thread_step in Hstep; last assumption.
      destruct Hstep as (Hstep & ->).
      destruct (pure_wp_preservation Hm Hstep) as (Hm' & <-).
      iFrame.
      by iApply "IH".
    - by apply invert_pure_wp_stop in Hm.
  Qed.

  Lemma ewp_pure `{Encode A} {X} (m : micro val X) (ζ : X → Prop) (φ : A → Prop) :
    pure m φ ζ →
    ⊢ imp m ⟨⟨ λ e, ⌜ζ e⌝ ⟩⟩ {{ λ x, ⌜φ x⌝ }} .
  Proof.
    iIntros (Hpure).
    iApply ewp_mono.
    iApply pure_ewp. apply Hpure.
    iIntros ([v|e]).
    - iIntros "(%a & %Henc & %Ha)".
      iPureIntro.
      exists a. auto.
    - iIntros "%He".
      iPureIntro.
      apply He.
  Qed.

End ewp_val_rules.
