Require Import Coq.Program.Equality.
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

  Implicit Type m : micro A X.

  (* Values *)
  Lemma ewp_value E Ψ Φ v :
    Φ (O2Ret v) -∗ ewp_def E (ret v : micro A X) Ψ Φ.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_ret_inv E Ψ Φ v :
    ewp_def E (ret v : micro A X) Ψ Φ ={E}=∗ Φ (O2Ret v).
  Proof. iIntros "HRet". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ ewp_def E (Throw v : micro A X) Ψ Φ.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw_inv E Ψ Φ v :
    ewp_def E (Throw v : micro A X) Ψ Φ ={E}=∗ Φ (O2Throw v).
  Proof. iIntros "HThrow". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_crash_inv E (Ψ : thread * iEff Σ) (Φ : outcome2 A X -> _) :
    ewp_def E (Crash : micro A X) Ψ Φ ={E}=∗ False.
  Proof.
    ewp_unfold (@Crash A X).
    iIntros "Hsi". done.
  Qed.

  Lemma ewp_outcome2 E Ψ Φ v :
    Φ v -∗ ewp_def E (inject2 v : micro A X) Ψ Φ.
  Proof.
    iIntros "HΦ". destruct v; simpl.
    { by iApply ewp_value. }
    { by iApply ewp_throw. }
  Qed.

  Lemma ewp_outcome2_inv E Ψ Φ v :
    ewp_def E (inject2 v : micro A X) Ψ Φ ={E}=∗ Φ v.
  Proof.
    iIntros "Hv". destruct v; simpl.
    { by iApply ewp_ret_inv. }
    { by iApply ewp_throw_inv. }
  Qed.

  Lemma ewp_outcome2_fupd E Ψ Φ v :
    (|={E}=> Φ v) -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ".
    destruct v; simpl.
    { by ewp_unfold (@ret A X a). }
    { by ewp_unfold (@throw A X e). }
  Qed.

  (* ------------------------------------------------------------------------ *)

  Lemma ewp_step {ι σ π σ'} E m m' μ {φ} Ψ:
    thread_step (σ, m, ι, dom π) (σ', m', μ) →
    state_interp (σ, π) -∗
    EWP m @ E <| (ι, Ψ) |> {{ φ }} ==∗
    |={E}[∅]▷=>
        EWP m' @ E <| (ι, Ψ) |> {{ φ }} ∗
          (match μ with
           | None => state_interp (σ', π)
           | Some (ι', m') => ∃ φ' γ, state_interp (σ', <[ι':= γ]>π) ∗
                                        saved_prop.saved_pred_own γ DfracDiscarded φ' ∗
                                        EWP m' @ E <| (ι', ⊥) |> {{ λ o, □ φ' o }}
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

  Lemma ewp_please E η e φ Ψ :
    ▷ EWP eval η e @ E <| Ψ |> {{ φ }} -∗
    EWP please_eval η e @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Heval".
    ewp_unfold (please_eval η e).
    rewrite /please_eval; destruct Ψ.
    intro_state.
    ewp_mask_intro "Hclose".
    construct_wp_nonret.
    iModIntro. ewp_mask_elim.
    apply invert_can_step_thread_step in Hstep; last (apply can_step_stop; tauto).
    destruct Hstep as [Hstep ->].
    destruct_step.
    rewrite try2_inject2_right. by iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_mono E m φ φ' ιΨ:
    EWP m @ E <| ιΨ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| ιΨ |> {{ φ' }}.
  Proof.
    destruct ιΨ.
    iLöb as "IH" forall (m).
    iIntros "Hwp Hmon".
    ewp_unfold m.
    ewp_case m.
    (* Case: [m] is a [WPOutcome] *)
    { iMod "Hwp"; iModIntro; iApply ("Hmon" with "[$]"). }

    (* Case: [m] is a [WPCrash]. *)
    { done. }

    { (* Case: [m] is a [WPPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[Hmon] Hwp").
      iIntros (w) "Hewp"; iNext.
      by iApply ("IH" with "Hewp Hmon"). }

    { (* Case: [m] is a [WPStep]. *)
      intro_state. spec_state. iModIntro.
      discharge_pure assumption.
      clear Hstep.
      iIntros (σ' m' μ) "%Hstep".
      spec_step.
      ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
      iApply ("IH" with "Hwp Hmon"). }

    { (* Case: [m] is a [WPJoin]. *)
      intro_state. spec_state.
      iMod "Hwp". iModIntro.
      destruct (π !! t0) eqn:Hlookup; last done.
      iDestruct "Hwp" as "(%φ'0 & $ & Hwp)".
      iIntros "!> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
      iApply ("IH" with "Hwp Hmon"). }
  Qed.

  Lemma ewp_mono_ret E m φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ ensures a, φ a }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ ensures a, φ' a }}.
  Proof.
    iIntros "H P".
    iApply (ewp_mono with "H").
    by iIntros ([]).
  Qed.

  Lemma ewp_prot_mono E m ι φ Ψ Ψ':
    (Ψ ⊑ Ψ')%ieff -∗
    EWP m @ E <| (ι, Ψ) |> {{ φ }} -∗
    EWP m @ E <| (ι, Ψ') |> {{ φ }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "#Hmono Hwp".
    ewp_unfold m.
    ewp_case m; try done.

    { (* Case: [m] is a [WPPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iDestruct "Hwp" as (?) "(Hwp & HΨ)"; iExists Φ.
      iSplitL "Hwp"; first iApply ("Hmono" with "Hwp"); cbn.
      iIntros (?) "HΦ". iSpecialize ("HΨ" with "HΦ").
      iNext; iApply ("IH" with "Hmono HΨ"). }

    { (* Case: [m] is a [WPStep]. *)
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. spec_step.
      ewp_mask_elim.
      iMod "Hwp" as "(Hwp & $)".
      by iApply ("IH" with "[//] Hwp"). }

    { (* Case: [m] is a [WPJoin]. *)
      intro_state. spec_state. iMod "Hwp"; iModIntro.
      destruct (π !! t); last done.
      iDestruct "Hwp" as "(%φ'0 & $ & Hwp)".
      iIntros "!> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim.
      iMod "Hwp" as "(Hwp & $)".
      by iApply ("IH" with "[//] Hwp"). }
  Qed.

  Lemma ewp_pers_smono E E' Ψ Φ Φ' m :
    E ⊆ E' →
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E'}=∗ Φ' v) -∗
    EWP m @ E' <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros (HE) "He".
    iLöb as "IH" forall (A X m Ψ Φ Φ').
    iIntros "#HΦ".
    ewp_unfold m.
    ewp_case m.
    { (* Cases: [WPOutcome] *)
      iApply ("HΦ" with "[> -]"); by iApply (fupd_mask_mono E _). }
    (* Case: [WPCrash] *)
    { by iApply (fupd_mask_mono E _). }
    (* Case: [WPPerform] *)
    { iApply (fupd_mask_mono E _); first done.
      iMod "He"; iModIntro.
      iApply (monotonic_prot with "[] He").
      iIntros (?) "Hewp". iNext.
      iApply ("IH" with "Hewp HΦ"). }
    { (* Case: [WPStep] *)
      intro_state.
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      spec_state. iModIntro. construct_wp_nonret.
      spec_step. ewp_mask_elim.
      iDestruct "He" as ">(H & Hforked)".
      iMod "Hclose"; iModIntro.
      iSplitL "H".
      - iApply ("IH" with "H HΦ").
      - destruct μ as [ [??] | ].
        + iDestruct "Hforked" as "(%φ' & %γ & Hsi & Hsaved & Hwp)".
          iFrame.
          iApply ("IH" with "Hwp").
          iModIntro. iIntros (v) "Hϕ !>". iApply "Hϕ".
        +  iFrame. }
    { (* Case: [WPJoin] *)
      intro_state.
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
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

  Corollary ewp_pers_mono E Ψ Φ Φ' m :
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E}=∗ Φ' v) -∗
    EWP m @ E <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros "He #HΦ".
    by iApply (ewp_pers_smono with "He").
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd_post E m Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => |={E}=> Φ v }} -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (ewp_pers_mono with "He").
    auto.
  Qed.

  Lemma ewp_fupd E m Ψ Φ :
    (|={E}=> EWP m @ E <| Ψ |> {{ Φ }}) -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    destruct Ψ. iIntros "He".
    ewp_unfold_all.
    ewp_case m; try iMod "He"; done.
  Qed.

  Lemma ewp_can_step {σ π} ι Ψ φ m E:
    state_interp (σ, π) -∗
    EWP m @ E <| (ι, Ψ) |> {{ φ }} ={E, ∅}=∗
    ⌜can_progress σ (dom π) m ∨ is_ewp_case m <> WPStep⌝.
  Proof.
    iIntros "SI Hwp".
    ewp_unfold_all.
    ewp_case m.
    1-3, 5: try iMod "Hwp";
        try (iApply fupd_mask_intro; first set_solver);
        iIntros "_"; iPureIntro; right; eauto.

    spec_state. iModIntro. by iPureIntro; left.
  Qed.

  Lemma ewp_can_step' {σ π} ι Ψ φ m E:
    state_interp (σ, π) -∗
    EWP m @ E <| (ι, Ψ) |> {{ φ }} ={E}=∗
    ⌜can_progress σ (dom π) m ∨ is_ewp_case m <> WPStep⌝.
  Proof.
    iIntros.
    iPoseProof (ewp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

End ewp_basic_rules.

(* ------------------------------------------------------------------------ *)
(* Invert cases where there are premises of the form
          [EWP (ret _) _] [EWP crash _] or [EWP (throw _) _] *)

Local Ltac ewp_invert :=
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
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (Stop CFork _ _) _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "%"
  end.

(* ------------------------------------------------------------------------ *)

(* Handler specifications *)

Section handler_specifications.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  (** * Shallow handler specification. *)

  Definition shallow_handler_spec E ι Ψ (Φ : outcome2 val exn -d> iProp Σ)
    (h : code.outcome3 val exn -> microvx)
    Ψ' Φ' :=
    ((* [Return] and [Exception] branch *)
    (∀ o, Φ o -∗ ▷ EWP (h o) @ E <| (ι, Ψ') |> {{ Φ' }}) ∧

    (* [Effect] branch *)
    (∀ v k, Ψ allows perform v
          << fun o => ▷ EWP (stop CResume (k, o)) @ E <| (ι, Ψ) |> {{ Φ }} >> -∗
        ▷ EWP (h (O3Perform v k)) @ E <| (ι, Ψ') |> {{ Φ' }}))%I.

End handler_specifications.

(* -------------------------------------------------------------------------- *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma ewp_stop_perform {B X'} E ι Ψ v Φ (k : _ -> micro B X'):
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| (ι, Ψ) |> {{ Φ }} >> -∗
    EWP (Stop CPerf v k) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "HP".
    iPoseProof (monotonic_prot with "[] HP") as "H"; cycle 1.
    { ewp_unfold_head; by iFrame. }
    iIntros (?) "HΦ". by iNext.
  Qed.

  Lemma ewp_perform E ι Ψ v Φ:
    Ψ allows perform v << Φ >> ⊢ EWP (perform v) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "HP". iApply ewp_stop_perform.
    iApply (monotonic_prot with "[] HP").
    iIntros (?) "HΦ". iNext.
    cbn. iApply ewp_outcome2; by cbn.
  Qed.

  Lemma ewp_perform_inv {B X'} E ι Ψ v Φ (k : _ -> micro B X'):
    EWP (Stop CPerf v k) @ E <| (ι, Ψ) |> {{ Φ }} ={E}=∗
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| (ι, Ψ) |> {{ Φ }} >>.
  Proof.
    iIntros "HP".
    ewp_unfold_all. iMod "HP"; iModIntro.
    iApply (monotonic_prot with "[] HP").
    iIntros (?) "HΦ"; by iNext.
  Qed.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle E ι Ψ Φ Ψ' Φ' e h:
    EWP e @ E <| (ι, Ψ) |> {{ Φ }} -∗
    shallow_handler_spec E ι Ψ Φ h Ψ' Φ' -∗
    EWP (Handle e h) @ E <| (ι, Ψ') |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)
    iLöb as "IH" forall (e).

    iIntros "He Hsh".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn; rename π into π'.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      ewp_mask_intro "Hmod"; ewp_mask_elim;
      iFrame.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "[$]") as "HP".
      iMod "HP".

      iDestruct (gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H | ].

      iAssert (Ψ allows perform e0
                 << fun o => ▷ EWP (stop CResume (l, o)) @ E <| (ι, Ψ) |> {{ Φ }} >>)%I
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
      destruct (Hstep (Thread 0%Z)) as (? & ? & ? & Htstep).
      destruct_thread_step.
      construct_wp_nonret.
      destruct_thread_step.
      eassert (thread_step (σ'0, Stop CFork (v, v0) k, ι, dom π) _) as Htstep.
      { eapply ForkS. eassumption. }
      spec_step.
      ewp_mask_elim.
      iMod "He" as "(Hwp & $)".
      iModIntro.
      iApply ("IH" with "Hwp Hsh"). }

    { (* [StepHandleJoin] *)
      ewp_mask_intro "Hmod". iModIntro. iMod "Hmod". iModIntro. iFrame.
      ewp_unfold_all. intro_state. spec_state. iMod "He". iModIntro.
      destruct (π !! ι0); last done.
      iDestruct "He" as "(%φ' & $ & He)".
      iIntros "!> %o Ho". iSpecialize ("He" with "Ho").
      ewp_mask_elim.
      iMod "He" as "(He & $)". iModIntro.
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleSelf] *)
      ewp_mask_intro "Hmod". iModIntro. iMod "Hmod". iModIntro. iFrame.
      ewp_unfold_all. intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_thread_step.
      destruct (Hstep ι) as (? & ? & ? & Htstep). spec_step.
      destruct_thread_step. ewp_mask_elim.
      iMod "He" as "(He & $)".
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleCrash] *)
      iPoseProof (ewp_crash_inv with "[$]") as "HF".
      by iMod "HF". }

    { (* [StepHandleLeft] *)
      eassert (thread_step (σ, e, ι, dom π') _) as Hstep.
      { apply BaseS. eassumption. }
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ _ _ Hstep with "Hsi He") as ">H".
      iMod "H". ewp_mask_elim. iMod "H" as "(H & $)". iModIntro.
      iApply ("IH" with "H Hsh"). }
  Qed.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle_ret E Ψ (Φ : outcome2 A X -> _) (a : val) h:
    EWP (h (O3Ret a)) @ E <| Ψ |> {{ Φ }} -∗
    EWP (Handle (ret a) h) @ E <| Ψ |> {{ Φ }}.
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

  Lemma ewp_handle_throw E Ψ (Φ : outcome2 A X -> _) (e : exn) h:
    EWP (h (O3Throw e)) @ E <| Ψ |> {{ Φ }} -∗
    EWP (Handle (throw e) h) @ E <| Ψ |> {{ Φ }}.
  Proof.
    destruct Ψ.
    iIntros "Hhandle".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn.

    - iFrame. ewp_mask_intro "Hmod"; ewp_mask_elim; done.
    - exfalso. eapply invert_can_step_Throw; unfold can_step; eauto.
  Qed.

  (* Inversion for [Handle] *)
  Lemma ewp_handle_inv {B Y} E k l w (c : _ -> micro B Y) Ψ Φ:
    isCont l k -∗
    EWP Handle (k w) c @ E <| Ψ |> {{ Φ }} -∗
    EWP Handle (stop CResume (l, w)) c @ E <| Ψ |> {{ Φ }}.
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
  Lemma ewp_handle_inv' k l w (c : _ -> micro A X) Ψ Φ:
    l ↦ K k -∗
    ▷ (l ↦ Shot -∗
        EWP Handle (k w) c <| Ψ |> {{ Φ }}) -∗
    EWP Handle (stop CResume (l, w)) c <| Ψ |> {{ Φ }}.
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

  Lemma ewp_try2 {B X'} E m (f : _-> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => EWP (f v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP (try2 m f) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "Hwp".
    ewp_case m.
    (* Case: [m1] is an outcome2. *)
    (* The result is immediate. *)
    { rewrite try2_inject2.
      iPoseProof (ewp_outcome2_inv with "[$]") as "Hret"; cbn.
      by iApply ewp_fupd. }

    (* Case : [m1] is [crash]; trivial  *)
    { iClear "IH".
      by setoid_rewrite (ewp_unfold Crash); rewrite /ewp_pre /=. }

    (* Case : [m1] is [Perform _ _]. *)
    { cbn.
      ewp_unfold_all. iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[] Hwp").
      iIntros (?) "HΨ"; iNext;
      by iSpecialize ("IH" with "HΨ"). }

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
        eassert (thread_step (σ', Stop CFork (v1, v2) k, t, dom π) _).
        { eapply ForkS. eassumption. }
        spec_step.
        ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
        iModIntro.
        iApply ("IH" with "Hwp"). }

      destruct Hstep as [ Hstep | Hstep ].
      { (* Case: [m1] is [Self]. *)
        destruct Hstep as (u & k & ->).
        simpl try2. construct_wp_nonret.
        destruct_thread_step.
        iAssert (⌜thread_step
                   (σ', Stop CSelf u0 k, t, dom π)
                   (σ', continue k (VThread t), None)⌝)%I as "Hstep".
        { iPureIntro. apply SelfS. }
        iSpecialize ("Hwp" with "Hstep").
        ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
        iApply ("IH" with "Hwp"). }

      (* Get more information out of [e2]; *)
      construct_wp_nonret.
      pose proof (can_step_try2 _ _ f Hstep) as Hstep2.
      pose proof (invert_can_step_thread_step _ _ _ _ _ _ _ Hstep0 Hstep2) as (_ & ->).

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

  Lemma ewp_try {B X'} E m (f : A -> micro B X') (h : X -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{  RET v => EWP (f v) @ E <| Ψ |> {{ Φ }}
                        | EXN v => EWP (h v) @ E <| Ψ |> {{ Φ }}}} -∗
    EWP (try m f h) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply ewp_try2.
    iApply (ewp_mono with "Hwp").
    iIntros ([]) "Hwp"; by cbn.
  Qed.

  (** *Bind rule *)
  Lemma ewp_bind {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ ensures v, EWP (k v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]"). iIntros (a) "H".
    destruct a; done.
  Qed.

  Lemma ewp_bind_exn {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{  RET v => EWP (k v) @ E <| Ψ |> {{ Φ }}
                        | EXN v => Φ (O2Throw v) }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]"). iIntros (a) "H".
    destruct a. done. by iApply ewp_throw.
  Qed.

  (** *Fmap rule *)
  Lemma ewp_fmap {B} E (f : A -> B) (m : micro A X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ ensures v, Φ (f v) }} -∗
    EWP fmap f m @ E <| Ψ |> {{ ensures v, Φ v }}.
  Proof.
    iIntros "Hwp". iApply ewp_bind.
    iApply (ewp_mono with "[$]"). iIntros (?) "H".
    destruct a; last done. cbn.
    iApply ewp_value; by cbn.
  Qed.

  (* Par combinator *)

  Lemma ewp_Par {E A1 A2 A3 X' Y} (m1 : micro A1 X') (m2 : micro A2 X')
    (k: outcome2 (A1 * A2) X' → micro A3 Y) φ φ1 φ2 Ψ :
    EWP m1 @ E <| Ψ |> {{ φ1 }} ⊢
      EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
      (∀ e, φ1 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ e, φ2 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ a1 a2,
          φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗
            EWP (k (O2Ret (a1, a2))) @ E <| Ψ |> {{ φ }}) -∗
      EWP (Par m1 m2 k) @ E <| Ψ |> {{ φ }}.
  Proof.
    clear A X. destruct Ψ as [ι Ψ].
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn; rename π into π'.

    { (* Case: [StepParRetRet].. *)
      ewp_invert; iRename "HΦ" into "HΦ2"; ewp_invert; iFrame.
      iMod "HΦ". iMod "HΦ2".
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iSpecialize ("Hjoin" with "HΦ HΦ2"). iFrame. }

    (* In the four following cases, one of the branches of the [Par] is either a
     [crash] or [throw _].

     We invert the cases where there are premises of the form [WP crash _] or
     [WP (throw _) _] *)
     1-4: ewp_invert; try done.

    (* [StepParThrowLeft/Right] *)
    1,2: iMod "HΦ";
    ewp_mask_intro "Hmod"; ewp_mask_elim;
    iFrame;
    try iApply ("Hexn1" with "[$]");
    try iApply ("Hexn2" with "[$]");
    done.

    { (* [StepThroughParLeft]. *)
      destruct_code.
      - (* [ParPerformLeft] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        iPoseProof (ewp_perform_inv with "[$]") as "H1".
        iApply ewp_fupd. iMod "H1"; iModIntro.
        iApply ewp_stop_perform.
        iApply (monotonic_prot with "[H2 Hexn1 Hexn2 Hjoin] H1").
        iIntros (?) "Hk".
        iNext.
        iApply ("IH" with "Hk H2 Hexn1 Hexn2 Hjoin").

      - (* Step then [ForkS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (ForkS _ _ _ _ _ _ _ H0).
        iSpecialize ("H1" $! _ _ _ H1).
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin").

      - (* Step then [JoinS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iMod "H1".
        destruct (π !! x); last done.
        iDestruct "H1" as "(%φ' & $ & H1)".
        iIntros "!> !> %o Ho". iSpecialize ("H1" with "Ho").
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin").

      - (* Step then [SelfS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CSelf x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (SelfS _ _ _ _ _).
        iSpecialize ("H1" $! _ _ _ H0).
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [StepThroughParRight]. *)
      destruct_code.

      - (* [StepParPerformRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        iPoseProof (ewp_perform_inv with "[$]") as "H2".
        iApply ewp_fupd. iMod "H2"; iModIntro.
        iApply ewp_stop_perform.
        iApply (monotonic_prot with "[H1 Hexn1 Hexn2 Hjoin] H2").
        iIntros (?) "H2".
        iNext.
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin").

      - (* [StepParForkRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (ForkS _ _ _ _ _ _ _ H0).
        iSpecialize ("H2" $! _ _ _ H1).
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin").

      - (* [StepParJoinRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iMod "H2".
        destruct (π !! x); last done.
        iDestruct "H2" as "(%φ' & $ & H2)".
        iIntros "!> !> %o Ho". iSpecialize ("H2" with "Ho").
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin").

      - (* [StepParSelfRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CSelf x _)) /ewp_pre /=.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_thread_step.
        epose proof (SelfS _ _ _ _ _).
        iSpecialize ("H2" $! _ _ _ H0).
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParLeft] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ _ _ Hstep with "Hsi H1") as ">H1".
      iMod "H1". ewp_mask_elim. iMod "H1" as "(H1 & $)".
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParRight] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ _ _ Hstep with "Hsi H2") as ">H2".
      iMod "H2". ewp_mask_elim. iMod "H2" as "(H2 & $)".
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }
  Qed.

  Lemma ewp_par {E A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X') {φ} φ1 φ2 Ψ :
    EWP m1 @ E <| Ψ |> {{ φ1 }} -∗
      EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
      (∀ e, φ1 (O2Throw e) -∗ φ (O2Throw e))-∗
      (∀ e, φ2 (O2Throw e) -∗ φ (O2Throw e)) -∗
      (∀ a1 a2,
          φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗ φ (O2Ret (a1, a2))) -∗
      EWP (par m1 m2) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hm1 Hm2 Hφ1 Hφ2 Hr".
    iApply (ewp_Par m1 m2 inject2 with "Hm1 Hm2 [Hφ1] [Hφ2] [Hr]").
    { iIntros (?) "Hφ". cbn.
      iApply ewp_throw. iApply ("Hφ1" with "Hφ"). }
    { iIntros (?) "Hφ". cbn.
      iApply ewp_throw. iApply ("Hφ2" with "Hφ"). }
    { iIntros (??) "Hφ1 Hφ2". cbn.
      iApply ewp_value. iApply ("Hr" with "Hφ1 Hφ2"). }
  Qed.

  Lemma ewp_par_same_exn {E A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X') {φ ψ} φ1 φ2 Ψ :
    EWP m1 @ E <| Ψ |> {{ RET v => φ1 v | EXN e => ψ e }} -∗
    EWP m2 @ E <| Ψ |> {{ RET v => φ2 v | EXN e => ψ e }} -∗
    (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗ φ (v1, v2)) -∗
    EWP (par m1 m2) @ E <| Ψ |> {{ RET v => φ v | EXN e => ψ e }}.
  Proof.
    iIntros "Hm1 Hm2 Hφ".
    iApply (ewp_par with "Hm1 Hm2"); auto.
  Qed.

End ewp_rules.

Lemma prove_ewp_Par `{!osirisGS Σ} {A X A1 A2 X'} m1 m2 (k : outcome2 (A1 * A2) X' -> micro A X) φ1 φ2 E ψ Q :
  EWP m1 @ E <|ψ|> {{ ensures v, φ1 v }} -∗
  EWP m2 @ E <|ψ|> {{ ensures v, φ2 v }} -∗
  (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗ EWP k (O2Ret (v1, v2)) @ E <|ψ|> {{ Q }}) -∗
  EWP (Par m1 m2 k) @ E <|ψ|> {{ Q }}.
Proof.
  iIntros "Hm1 Hm2 Hk".
  iApply (ewp_Par with "Hm1 Hm2"); simpl; try iIntros (e) "[]".
  iApply "Hk".
Qed.

(* Rules that deal with microvx directly. *)

Section ewp_val_rules.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  (* [CEval]. *)

  Lemma ewp_eval {B X'} E η e (k : _ → micro B X') φ Ψ :
    ▷ EWP (eval η e) @ E <| Ψ |>
      {{ fun v => EWP (k v) @ E <| Ψ |> {{ φ }} }} ⊢
      EWP (Stop CEval (η, e) k) @ E <| Ψ |> {{ φ }}.
  Proof.
    destruct Ψ.
    iIntros "Hwp".
    ewp_unfold_head. intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret. destruct_thread_step.
    ewp_mask_elim.
    iFrame.
    iApply (ewp_try2 with "Hwp").
  Qed.

  Lemma ewp_eval_ret E η e Ψ (φ : _ -> iPropI Σ):
    ▷ EWP eval η e @ E <| Ψ |> {{  φ }} ⊢
      EWP stop CEval (η, e) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    iApply ewp_eval.
    iNext. iApply (ewp_mono with "Hwp"); iIntros (?) "H".
    by iApply ewp_outcome2.
  Qed.

  Lemma pure_ewp {A E} E' Ψ (φ : A → Prop) (ζ : E → Prop) m :
    pure_wp m φ ζ →
    ⊢ EWP m @ E' <| Ψ |> {{ RET a => ⌜φ a⌝ | EXN e => ⌜ζ e⌝ }}.
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

  Lemma ewp_pure_wp {A X} (m : micro A X) E Ψ (φ : A -> Prop) :
    pure_wp m φ ⊥ ->
    ⊢ EWP m @ E <| Ψ |> {{ ensures v, ⌜φ v⌝ }}.
  Proof.
    iIntros (W).
    iApply ewp_mono.
    iApply pure_ewp. eassumption. iIntros ([]); eauto.
  Qed.

  Lemma ewp_pure `{Encode A} {X} (m : micro val X) E Ψ (φ : A -> Prop) :
    pure m φ ⊥ ->
      ⊢ EWP m @ E <| Ψ |> {{ ensures #v, ⌜φ v⌝ }} .
  Proof.
    iIntros (Hpure).
    iApply ewp_mono.
    iApply ewp_pure_wp. apply Hpure.
    iIntros ([v|]); [ | iIntros ([]) ].
    iIntros "(%a & %Henc & %Ha)".
    iPureIntro.
    exists a. auto.
  Qed.

End ewp_val_rules.


(** *General tactics *)
(* These tactics are declared here because they depende on
   1. Lemmas defined in [basic_rules.v] such as [ewp_value]
   2. The [simp] tactic, which is defined in [simp_tactics.v]  *)

(* Start proof mode. *)
Ltac Start_proof := iStartProof.

(* Hoare-style rules that correspond to [rule] lemmas *)
Ltac Try := iApply ewp_try.

Ltac Ret := repeat iApply ewp_value.

Ltac Throw := iApply ewp_throw.

Ltac Par := iApply prove_ewp_Par.

Ltac Bind := first [ iApply ewp_fmap | iApply ewp_bind ].
