Require Import Coq.Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import ewp tactics.

From osiris.program_logic.pure Require Export pure.

(** *Basic rules on the program logic

  This file contains the "basic" rules of how to use the program logic.

  i.e.
  (1) How to reason about expressions at the [micro] monad level and
  (2) Proof that the weakest precondition is closed under [simp]
      (see [ewp_simp]). *)

(* ------------------------------------------------------------------------ *)

Notation state_interp := osiris_state_interp.

Section ewp_basic_rules.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  Context {A X : Type}.

  Implicit Type m : micro A X.


  (* Values *)
  Lemma ewp_value E Ψ Φ v :
    Φ (O2Ret v) -∗ EWP (ret v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_ret_inv E Ψ Φ v :
    EWP (ret v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Ret v).
  Proof. iIntros "HRet". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw_inv E Ψ Φ v :
    EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Throw v).
  Proof. iIntros "HThrow". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_crash_inv E (Ψ : iEff Σ) (Φ : outcome2 A X -> _) s :
    EWP (Crash s : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ False.
  Proof.
    ewp_unfold (@crash A X s).
    iIntros "Hsi". done.
  Qed.

  Lemma ewp_outcome2 E Ψ Φ v :
    Φ v -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ". destruct v; simpl.
    { by iApply ewp_value. }
    { by iApply ewp_throw. }
  Qed.

  Lemma ewp_outcome2_inv E Ψ Φ v :
    EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
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

  Lemma ewp_step {σ σ'} E m n {φ} Ψ:
    step (σ, m) (σ', n) →
    state_interp σ -∗
     EWP m @ E <| Ψ |> {{ φ }} ={E,∅}=∗ |={∅}▷=> |={∅,E}=>
     (state_interp σ' ∗ EWP n @ E <| Ψ |> {{ φ }}).
  Proof.
    intro Hstep.
    iIntros "Hsi Hwp".
    ewp_unfold m.
    ewp_case_is_handleable m.
    ewp_case_is_concurrent m.
    spec_state; spec_step.
    by ewp_mask_elim.
  Qed.

  Lemma ewp_please E η e φ Ψ :
    ▷ EWP eval η e @ E <| Ψ |> {{ φ }} -∗
    EWP please_eval η e @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Heval".
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hclose".
    rewrite /please_eval.
    iSplitR. { iPureIntro. eexists _. apply StepEval. }
    intro_step.
    iModIntro. ewp_mask_elim.
    iAssert (⌜m' =  eval η e⌝)%I as "->".
    { iPureIntro.
      simple inversion Hstep; try discriminate.
      apply pair_eq in H as [_ H].
      remember (η0, e0) as p0.

      replace η0 with p0.1 in *; last first.
      { by rewrite Heqp0. }
      replace e0 with p0.2 in *; last first.
      { by rewrite Heqp0. }

      dependent destruction H.
      apply pair_eq in H0 as [_ H0].
      rewrite try2_ret_right in H0.
      by rewrite H0. }

    dependent destruction Hstep. iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_mono E m φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ φ' }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "Hwp Hmon".
    ewp_unfold m.
    ewp_case_is_handleable m.
    (* Case: [m] is a [HRet] or a [HThrow]. We easily conclude. *)
    1, 2 : iMod "Hwp"; iModIntro; iApply ("Hmon" with "[$]").

    (* Case: [m] is a [HCrash]. *)
    done.

    { (* Case: [m] is a [HPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[Hmon] Hwp").
      iIntros (w) "Hewp"; iNext.
      by iApply ("IH" with "Hewp Hmon"). }

    ewp_case_is_concurrent m.
    { (* Case: [m] is a [CFork]. *)
      iMod "Hwp"; iIntros "!> !>" (t).
      iDestruct ("Hwp" $! t) as "[Hcall Hk]".
      iFrame.
      iApply ("IH" with "Hk Hmon"). }

    { (* Case: [m] is a [CJoin]. *)
      iMod "Hwp"; iModIntro; iModIntro.
      iApply ("IH" with "Hwp Hmon"). }

    intro_state. spec_state. iModIntro.
    construct_wp_nonret.
    spec_step. ewp_mask_elim.

    iDestruct "Hwp" as ">[$ Hwp]".
    by iApply ("IH" with "Hwp").
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

  Lemma ewp_prot_mono E m φ Ψ Ψ':
    (Ψ ⊑ Ψ')%ieff -∗
    EWP m @ E <| Ψ |> {{ φ }} -∗
    EWP m @ E <| Ψ' |> {{ φ }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "#Hmono Hwp".
    ewp_unfold m.
    ewp_case_is_handleable m; try done.

    { (* Case: [m] is a [HPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iDestruct "Hwp" as (?) "(Hwp & HΨ)"; iExists Φ.
      iSplitL "Hwp"; first iApply ("Hmono" with "Hwp"); cbn.
      iIntros (?) "HΦ". iSpecialize ("HΨ" with "HΦ").
      iNext; iApply ("IH" with "Hmono HΨ"). }

    ewp_case_is_concurrent m.
    { (* Case: [m] is a [CFork]. *)
      iMod "Hwp"; iIntros "!> !>" (t).
      iDestruct ("Hwp" $! t) as "[Hcall Hk]".
      iFrame.
      iApply ("IH" with "Hmono Hk"). }

    { (* Case: [m] is a [CJoin]. *)
      iMod "Hwp"; iModIntro; iModIntro.
      iApply ("IH" with "Hmono Hwp"). }

    intro_state. spec_state. iModIntro.
    construct_wp_nonret.
    spec_step. ewp_mask_elim.

    iDestruct "Hwp" as ">[$ Hwp]".
    by iApply ("IH" with "[//] Hwp").
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
    ewp_case_is_handleable m.
    1,2: iApply ("HΦ" with "[> -]"); by iApply (fupd_mask_mono E _).
    { by iApply (fupd_mask_mono E _). }
    { iApply (fupd_mask_mono E _); first done.
      iMod "He"; iModIntro.
      iApply (monotonic_prot with "[] He").
      iIntros (?) "Hewp". iNext.
      iApply ("IH" with "Hewp HΦ"). }

    ewp_case_is_concurrent m.
    { iApply (fupd_mask_mono E _); first done.
      iMod "He"; iIntros "!> !>" (t).
      iDestruct ("He" $! t) as "[Hcall Hk]".
      iSplitL "Hcall".
      { iApply ("IH" with "Hcall").
        trivial. }
      iApply ("IH" with "Hk HΦ"). }

    { iApply (fupd_mask_mono E _); first done.
      iMod "He"; iModIntro; iModIntro.
      iApply ("IH" with "He HΦ"). }

    intro_state.
    iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    spec_state. iModIntro. construct_wp_nonret.
    spec_step. ewp_mask_elim.
    iDestruct "He" as ">(SI & H)"; iFrame.
    iMod "Hclose"; iApply ("IH" with "H HΦ").
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
    iIntros "He".
    ewp_unfold_all. destruct (is_handleable m).
    { destruct h; iMod "He"; done. }
    destruct (is_concurrent m).
    { destruct c; iMod "He"; iMod "He"; done. }
    intro_state. iMod "He".
    spec_state. by iFrame.
  Qed.

  Lemma ewp_can_step {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E, ∅}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None ∨ is_concurrent m <> None⌝.
  Proof.
    iIntros "SI Hwp".
    ewp_unfold_all.
    ewp_case_is_handleable m.
    1-4: try iMod "Hwp";
        try (iApply fupd_mask_intro; first set_solver);
        iIntros "_"; iPureIntro; right; eauto.

    ewp_case_is_concurrent m.
    1-2: iMod "Hwp";
        iApply fupd_mask_intro; first set_solver;
        iIntros "_"; iPureIntro; right; eauto.

    spec_state. iModIntro. iPureIntro; auto.
  Qed.

  Lemma ewp_can_step' {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None ∨ is_concurrent m <> None⌝.
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
  match goal with
  | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
      match goal with
      (* EWP throw *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
          iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
      (* EWP ret *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
          iMod (ewp_ret_inv with "[$]") as "HΦ"
      (* EWP crash *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (Crash _) _ _)] =>
          match goal with
          | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
            iMod (ewp_crash_inv with "[$]") as "%"
          end
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (Stop CFork _ _) _ _)] =>
          match goal with
          | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
              iMod (ewp_crash_inv with "[$]") as "%"
          end
      end
  end.

(* ------------------------------------------------------------------------ *)

(* Handler specifications *)

Section handler_specifications.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  (** * Shallow handler specification. *)

  Definition shallow_handler_spec E Ψ (Φ : outcome2 val exn -d> iProp Σ)
    (h : code.outcome3 val exn -> microvx)
    Ψ' Φ' :=
    ((* [Return] and [Exception] branch *)
    (∀ o, Φ o -∗ ▷ EWP (h o) @ E <| Ψ' |> {{ Φ' }}) ∧

    (* [Effect] branch *)
    (∀ v k, Ψ allows perform v
          << fun o => ▷ EWP (stop CResume (k, o)) @ E <| Ψ |> {{ Φ }} >> -∗
        ▷ EWP (h (O3Perform v k)) @ E <| Ψ' |> {{ Φ' }}))%I.

End handler_specifications.

(* -------------------------------------------------------------------------- *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Implicit Type Ψ : iEff Σ.
  Import ewp_rules_tactics.

  Lemma ewp_stop_perform {B X'} E Ψ v Φ (k : _ -> micro B X'):
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }} >> -∗
    EWP (Stop CPerf v k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP".
    iPoseProof (monotonic_prot with "[] HP") as "H"; cycle 1.
    { ewp_unfold_head; by iFrame. }
    iIntros (?) "HΦ". by iNext.
  Qed.

  Lemma ewp_perform E Ψ v Φ:
    Ψ allows perform v << Φ >> ⊢ EWP (perform v) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP". iApply ewp_stop_perform.
    iApply (monotonic_prot with "[] HP").
    iIntros (?) "HΦ". iNext.
    cbn. iApply ewp_outcome2; by cbn.
  Qed.

  Lemma ewp_perform_inv {B X'} E Ψ v Φ (k : _ -> micro B X'):
    EWP (Stop CPerf v k) @ E <| Ψ |> {{ Φ }} ={E}=∗
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }} >>.
  Proof.
    iIntros "HP".
    ewp_unfold_all. iMod "HP"; iModIntro.
    iApply (monotonic_prot with "[] HP").
    iIntros (?) "HΦ"; by iNext.
  Qed.

  Lemma ewp_stop_fork {B X'} E Ψ v1 v2 (k : _ -> micro B X') Φ :
    (∀ t, EWP call v1 v2 @ E <| ⊥ |> {{ λ _, True }} ∗
          EWP (k (O2Ret (VThread t))) @ E <| Ψ |> {{ Φ }}) -∗
    EWP (Stop CFork (v1, v2) k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hass".
    rewrite {1}(ewp_unfold (Stop CFork (v1, v2) k)) /=.
    iIntros "!> !>" (t).
    iDestruct ("Hass" $! t) as "[Hcall Hk]"; iFrame.
  Qed.

  Lemma ewp_fork E Ψ v1 v2 Φ :
    EWP call v1 v2 @ E <| ⊥ |> {{ λ _, True }} -∗
    (∀ t, Φ (O2Ret (VThread t))) -∗
    EWP (fork v1 v2) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hcall HΦ".
    iApply ewp_stop_fork.
    iIntros (t); iFrame.
    iApply ewp_value. iApply "HΦ".
  Qed.

  Lemma ewp_fork_inv {B X'} E Ψ v1 v2 (k : _ -> micro B X') Φ :
    EWP (Stop CFork (v1, v2) k) @ E <| Ψ |> {{ Φ }} -∗
    |={E}=> ▷ (∀ t, EWP call v1 v2 @ E <| ⊥ |> {{ λ _, True }} ∗
          EWP (k (O2Ret (VThread t))) @ E <| Ψ |> {{ Φ }}).
  Proof.
    iIntros "HF".
    rewrite {1}(ewp_unfold (Stop CFork (v1, v2) k)) /ewp_pre /=.
    iApply "HF".
  Qed.

  Lemma ewp_stop_join {B X'} E Ψ i Φ (k : _ -> micro B X') :
    EWP (k (O2Ret VUnit)) @ E <| Ψ |> {{ Φ }} -∗
    EWP (Stop CJoin i k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hk".
    rewrite {1}(ewp_unfold (Stop CJoin i k)) /=.
    iApply "Hk".
  Qed.

  Lemma ewp_join E Ψ i Φ :
    Φ (O2Ret (VUnit)) -∗
    EWP (join i) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply ewp_stop_join.
    iApply ewp_value. iApply "HΦ".
  Qed.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle E Ψ Φ Ψ' Φ' e h:
    EWP e @ E <| Ψ |> {{ Φ }} -∗
    shallow_handler_spec E Ψ Φ h Ψ' Φ' -∗
    EWP (Handle e h) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)
    iLöb as "IH" forall (e).

    iIntros "He Hsh".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      by ewp_mask_intro "Hmod"; ewp_mask_elim.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "[$]") as "HP".
      iMod "HP".

      iDestruct (gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H | ].

      iAssert (Ψ allows perform e0
                 << fun o => ▷ EWP (stop CResume (l, o)) @ E <| Ψ |> {{ Φ }} >>)%I
        with "[HP HH]" as "HΨ".
      { iApply (monotonic_prot with "[HH] HP").
        iIntros (?) "Hwp"; cbn. iNext.
        rename σ into σ'.
        ewp_unfold_head.
        intro_state.
        ewp_mask_intro "Hmod".
        iDestruct (gen_heap_valid with "Hsi HH") as %Hl.
        unfold stop.
        construct_wp_nonret.
        eapply invert_step_resume in Hstep; [ destruct Hstep | eexact Hl ]; subst.
        rewrite try2_inject2_right.
        iDestruct (gen_heap_update with "Hsi HH") as ">(Hsi & HH)";
          iFrame.
        by ewp_mask_elim. }

      iSpecialize ("Hsh" with "HΨ").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iFrame.
      unfold cont; simpl. iApply "Hsh". }

    { (* [StepHandleFork] *)
      admit. }

    { (* [StepHandleJoin] *)
      admit. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iApply ("IH" with "H Hsh"). }
  Admitted.

  (* Specification for [Handle] follows the specification for shallow handlers. *)
  Lemma ewp_handle_ret E Ψ (Φ : outcome2 A X -> _) (a : val) h:
    EWP (h (O3Ret a)) @ E <| Ψ |> {{ Φ }} -∗
    EWP (Handle (ret a) h) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hhandle".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    - iFrame. ewp_mask_intro "Hmod"; ewp_mask_elim; done.
    - exfalso. eapply invert_can_step_Ret; unfold can_step; eauto.
  Qed.

  Lemma ewp_handle_throw E Ψ (Φ : outcome2 A X -> _) (e : exn) h:
    EWP (h (O3Throw e)) @ E <| Ψ |> {{ Φ }} -∗
    EWP (Handle (throw e) h) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hhandle".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    - iFrame. ewp_mask_intro "Hmod"; ewp_mask_elim; done.
    - exfalso. eapply invert_can_step_Throw; unfold can_step; eauto.
  Qed.

  (* Inversion for [Handle] *)
  Lemma ewp_handle_inv {B Y} E k l w (c : _ -> micro B Y) Ψ Φ:
    isCont l k -∗
    EWP Handle (k w) c @ E <| Ψ |> {{ Φ }} -∗
    EWP Handle (stop CResume (l, w)) c @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hl H".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap.gen_heap_valid with "Hsi Hl")  as "%".

    inversion Hstep; subst.
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_resume in H1; [ destruct H1 | eauto ]; subst.

    (* Update the ghost heap. *)
    iMod (gen_heap.gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right. done.
  Qed.

  (* Variant inversion rule for [Handle] *)
  Lemma ewp_handle_inv' k l w (c : _ -> micro A X) Ψ Φ:
    l ↦ K k -∗
    ▷ (l ↦ Shot -∗
        EWP Handle (k w) c <| Ψ |> {{ Φ }}) -∗
    EWP Handle (stop CResume (l, w)) c <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hl H".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap.gen_heap_valid with "Hsi Hl")  as "%".

    inversion Hstep; subst.
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_resume in H1; [ destruct H1 | eauto ]; subst.

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

  Lemma is_handleable_try_None {B X'} m (f : A -> micro B X') (h : X -> micro B X'):
    is_handleable m = None ->
    is_handleable (try m f h) = None.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H0; done.
  Qed.

  Lemma is_handleable_try2_None {B X'} m (f : _ -> micro B X'):
    is_handleable m = None ->
    is_handleable (try2 m f) = None.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H0; done.
  Qed.

  Lemma is_concurrent_try2_None {B X'} (m : micro A X)
    (f : outcome2 A X -> micro B X'):
    is_handleable m = None ∧ is_concurrent m = None ->
    is_concurrent (try2 m f) = None.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct_code; simpl in *; try done.
    destruct x. try done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)

  Lemma ewp_try2 {B X'} E m (f : _ -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => EWP (f v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP (try2 m f) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "Hwp".
    ewp_case_is_handleable m.
    (* Case: [m1] is [ret _]. *)
    (* The result is immediate. *)
    { iPoseProof (ewp_ret_inv with "[$]") as "Hret"; cbn.
      by iApply ewp_fupd. }

    (* Case : [m1] is [throw _]; trivial  *)
    { ewp_unfold (throw (A := A) e); by iApply ewp_fupd. }

    (* Case : [m1] is [crash]; trivial  *)
    { iClear "IH".
      by setoid_rewrite (ewp_unfold (crash _)); rewrite /ewp_pre /=. }

    (* Case : [m1] is [Perform _ _]. *)
    { cbn.
      ewp_unfold_all. iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[] Hwp").
      iIntros (?) "HΨ"; iNext;
      by iSpecialize ("IH" with "HΨ"). }

    ewp_case_is_concurrent m.
    (* Case: [m1] is [Fork _ _]. *)
    { cbn.
      ewp_unfold_all. iMod "Hwp".
      iIntros "!> !>" (t).
      iDestruct ("Hwp" $! t) as "[Hcall Hk]"; iFrame.
      iApply ("IH" with "Hk"). }

    (* Case: [m1] is [Join _ _]. *)
    { cbn.
      ewp_unfold_all. iMod "Hwp".
      iIntros "!> !>".
      iApply ("IH" with "Hwp"). }

    (* Since [m] is neither handleable nor concurrent,
       neither is [try m f h]. *)
    pose proof (is_handleable_try2_None m f Hhm) as Hhandletry2.
    pose proof (conj Hhm Hhm0) as Hconj.
    pose proof (is_concurrent_try2_None m f Hconj) as Hconctry2.

    ewp_unfold_all.
    rewrite Hhm; rewrite Hhandletry2.
    rewrite Hhm0; rewrite Hconctry2.

    (* Process a step of computation. *)
    intro_state. spec_state.
    iModIntro. construct_wp_nonret.

    (* Get more information out of [e2]; *)
    apply invert_step_try2 in Hstep0; auto; destruct Hstep0 as (?&Hstep0&->).

    (* Can use information from above to get [wp] about stepped computation *)
    spec_step.
    ewp_mask_elim. iDestruct "Hwp" as ">(SI & Hwp)"; iFrame.
    iModIntro.

    (* Apply induction hypothesis  *)
    by iApply ("IH" with "Hwp").
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

  (* ------------------------------------------------------------------------ *)

  (* The following lemmas offer reasoning rules for each of the system calls,
     that is, for computations of the form [Stop c x y]. They are simple
     consequences of the operational behavior of these system calls. *)

  (* [CAlloc]. *)

  (* The standard memory allocation rule of Separation Logic. *)

  Lemma ewp_alloc' {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          pointsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤ -∗
          EWP (continue k l) @ E <| Ψ |> {{ φ }}) ⊢
      EWP (Stop CAlloc v k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_step.
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH HM]]"; first done.
    ewp_mask_elim. iFrame. by iApply "H"; iFrame.
  Qed.

  Lemma ewp_alloc {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          pointsto l (DfracOwn 1) (V v) -∗
          EWP (continue k l) @ E <| Ψ |>  {{ φ }}) ⊢
    EWP (Stop CAlloc v k) @ E <| Ψ |>  {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_alloc'; iNext.
    iIntros (l) "(Hl & _)".
    iApply ("H" with "Hl").
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma ewp_store {B Y} E l v v' (k : _ → micro B Y) φ Ψ :
    pointsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        pointsto l (DfracOwn 1) (V v') -∗
        EWP (continue k #()) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CStore (l, v') k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%";
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* [CLoad]. *)

  (* The standard memory load rule of Separation Logic. *)

  Lemma ewp_load {B Y} E l v dq (k: _ → micro B Y) φ Ψ:
    pointsto l dq (V v) ⊢
    ▷ (
        pointsto l dq (V v) -∗
        EWP (continue k v) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CLoad l k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.

    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* [CResume]. *)

  (* Resuming a continuation from a location in the store. *)

  Lemma ewp_resume {B Y} E l o sk (k: _ → micro B Y) φ ψ :
    isCont l sk ⊢
    (isShot l -∗
     ▷   EWP (try2 (sk o) k) @ E <| ψ |> {{ φ }}) -∗
    EWP (Stop CResume (l, o) k) @ E <| ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_resume in Hstep; [ destruct Hstep | eauto ]; subst.

    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iSpecialize ("Hwp" with "Hl").
    ewp_mask_elim.
    iFrame.
  Qed.

  Lemma ewp_resume_crash {B Y} E l o (k: _ → micro B Y) ψ φ :
    pointsto l (DfracOwn 1) Shot -∗
    (∀ s, EWP (Crash s) @ E <| ψ |> {{ φ }}) -∗
    EWP (Stop CResume (l, o) k) @ E <| ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hcrash".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_resume_shot in Hstep; eauto. destruct Hstep as (-> & s & ->).

    (* Update the ghost heap. *)
    ewp_mask_elim.
    iFrame.
    eauto.
  Qed.

  (* [CWrap]. *)

  (* Installing a handler with branches [bs] on top of a continuation
     that is located in the store at location [l]. *)

  Lemma ewp_wrap_deep {B Y} E l η bs (k: _ -> micro B Y) φ ψ :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs)) -∗
     ▷ EWP (continue k l') @ E <| ψ |> {{ φ }}) -∗
    EWP (Stop CWrap (true, l, η, bs) k) @ E <| ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* The reduction step must be a successful step. *)
    eapply invert_step_wrap_deep in Hstep as (l' & ? & ? & ?); subst.

    (* Allocate a new location in the heap. *)
    iMod (gen_heap.gen_heap_alloc with "Hsi") as "(Hsi & Hl' & _)"; first done.
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim.
    iFrame "Hsi".
    done.
  Qed.

  Lemma ewp_wrap_shallow {B Y} E l η bs (k: _ -> micro B Y) φ ψ :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs)) -∗
     ▷ EWP (continue k l') @ E <| ψ |> {{ φ }}) -∗
    EWP (Stop CWrap (false, l, η, bs) k) @ E <| ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* The reduction step must be a successful step. *)
    eapply invert_step_wrap_shallow in Hstep as (l' & ? & ? & ?); subst.

    (* Allocate a new location in the heap. *)
    iMod (gen_heap.gen_heap_alloc with "Hsi") as "(Hsi & Hl' & _)"; first done.
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim.
    iFrame "Hsi".
    done.
  Qed.

  (* Par combinator *)

  Lemma ewp_Par {E A1 A2 A3 X' Y} (m1 : micro A1 X') (m2 : micro A2 X')
    (k: outcome2 (A1 * A2) X' → micro A3 Y) φ φ1 φ2 (Ψ : iEff Σ) :
    EWP m1 @ E <| Ψ |> {{ φ1 }} ⊢
      EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
      (∀ e, φ1 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ e, φ2 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ a1 a2,
          φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗
            EWP (k (O2Ret (a1, a2))) @ E <| Ψ |> {{ φ }}) -∗
      EWP (Par m1 m2 k) @ E <| Ψ |> {{ φ }}.
  Proof.
    clear A X.
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    { (* Case: [StepParRetRet].. *)
      ewp_invert; iRename "HΦ" into "HΦ2"; ewp_invert; iFrame.
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iSpecialize ("Hjoin" with "HΦ HΦ2"); by iFrame. }

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

    { (* [ParPerformLeft] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      iPoseProof (ewp_perform_inv with "[$]") as "H1".
      iApply ewp_fupd. iMod "H1"; iModIntro.
      iApply ewp_stop_perform.
      iApply (monotonic_prot with "[H2 Hexn1 Hexn2 Hjoin] H1").
      iIntros (?) "Hk".
      iNext.
      iApply ("IH" with "Hk H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParPerformRight] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      iPoseProof (ewp_perform_inv with "[$]") as "H2".
      iApply ewp_fupd. iMod "H2"; iModIntro.
      iApply ewp_stop_perform.
      iApply (monotonic_prot with "[H1 Hexn1 Hexn2 Hjoin] H2").
      iIntros (?) "H2".
      iNext.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [StepParForkLeft] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      admit. }

    { (* [StepParForkRight] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      admit. }

    { (* [StepParJoinLeft] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      admit. }

    { (* [StepParJoinRight] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      admit. }

    { (* [ParLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H1") as ">H1".
      ewp_mask_elim. iMod "H1" as "[$ H1]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParRight] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H2") as ">H2".
      ewp_mask_elim. iMod "H2" as "[$ H2]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }
  Admitted.

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

  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma ewp_flip {E} u (k: _ → micro A X) {φ} Ψ :
      ▷(EWP continue k true @ E <| Ψ |> {{ φ }} ∧ EWP continue k false @ E <| Ψ |> {{ φ }})
      ⊢ EWP (Stop CFlip u k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn;
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
    destruct b.
    { iApply (bi.and_elim_l with "H"). }
    { iApply (bi.and_elim_r with "H"). }
  Qed.

End ewp_rules.

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
    iIntros "Hwp".
    try ewp_unfold_head; try intro_state;
      (* Introduce mask for entering into WP *)
      ewp_mask_intro "Hmod".
    try construct_wp_nonret; destruct_step.
    ewp_mask_elim;
      (* Frame state interp *)
      try iFrame; cbn.
    iApply (ewp_try2 with "Hwp").
  Qed.

  Lemma ewp_eval_ret E η e Ψ (φ : _ -> iPropI Σ):
    ▷ EWP eval η e @ E <| Ψ |>
      {{ fun v => EWP inject2 v @ E <| Ψ |> {{ φ }} }} ⊢
      EWP stop CEval (η, e) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    iApply ewp_eval.
    iNext. iApply (ewp_mono with "Hwp"); iIntros (?) "H"; done.
  Qed.

  Lemma ewp_choose {A} E (m1 m2 : micro A exn) {φ} Ψ :
      ▷(EWP m1 @ E <| Ψ |> {{ φ }} ∧ EWP m2 @ E <| Ψ |> {{ φ }})
      ⊢ EWP (choose m1 m2) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_bind_exn.
    iApply ewp_flip.
    iSplit; iApply ewp_value.
    - iApply (bi.and_elim_l with "H").
    - iApply (bi.and_elim_r with "H").
  Qed.

  Lemma nh_nc_can_step {A E} (m : micro A E) σ :
    is_handleable m = None ->
    is_concurrent m = None ->
    can_step (σ, m).
  Proof.
    intros Hh Hc.
    destruct m; try discriminate Hh; try discriminate Hc.
    - apply can_step_handle.
    - apply can_step_stop. destruct c; try discriminate Hh; try done.
      destruct x; discriminate Hc.
    - apply can_step_par.
  Qed.

  Lemma ewp_simp {A X} E (m : micro A X) ms Ψ φ:
    simp m ms →
    EWP ms @ E <| Ψ |> {{ φ }} ⊢
      EWP m @ E <| Ψ |> {{ φ }}.
  Proof.
    (* Proceed by Löb induction. *)
    iLöb as "IH" forall (m ms).
    (* Introduce the hypotheses. *)
    iIntros (Hsimp) "Hwp".

    destruct (is_handleable m) eqn: Hmh.
    { destruct m; inversion Hmh; subst; try solve [inversion Hsimp];
        clarify_simp; subst; try done.
      inversion Hmh. destruct c; inversion H0; subst.
      clarify_simp. ewp_unfold_all.
      iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[] Hwp").
      iIntros (w) "Hw". iNext.
      iApply ("IH" $! _ _ (H1 w) with "Hw"). }

    destruct (is_concurrent m) eqn: Hmc.
    { destruct m; inversion Hmh; inversion Hmc; subst; try solve [inversion Hsimp];
        clarify_simp; subst; try done.
      destruct c0; inversion H0; subst; try discriminate.
      - clarify_simp.
        destruct x.
        ewp_unfold_all.
        iMod "Hwp". iModIntro. iNext.
        iIntros (t).
        iDestruct ("Hwp" $! t) as "[Hcall Hk]"; iFrame.
        iApply ("IH" with "[] Hk").
        iPureIntro. apply H1.
      - clarify_simp.
        ewp_unfold_all.
        iMod "Hwp"; iModIntro; iNext.
        iApply ("IH" with "[] Hwp").
        iPureIntro. apply H1. }

    assert (∀ σ, can_step (σ, m)) as Hcanstep.
    { intros σ; apply nh_nc_can_step; auto. }

    (* Examine [ms] on whether it is a [ret]. *)
    ewp_case_is_handleable ms.

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh. rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh. rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Case : [ms] is [crash _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh. rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Case : [ms] is [Perform _]. *)
    { ewp_unfold_head. rewrite Hmh. rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.

      eapply simp_perform_step_diagram in Hsimp; eauto.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    rename Hhm into Hmsh.
    ewp_case_is_concurrent ms.
    (* Case: [ms] is [Fork _]. *)
    { ewp_unfold_head. rewrite Hmh. rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.
      eapply simp_fork_step_diagram in Hsimp; eauto.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      iApply ("IH" with "[//] Hwp"). }

    (* Case: [ms] is [Join _] *)
    { ewp_unfold_head; rewrite Hmh; rewrite Hmc.
      intro_state. ewp_mask_intro "Hmod".
      iSplit.
      { iPureIntro. apply Hcanstep. }
      intro_step.
      eapply simp_join_step_diagram in Hsimp; eauto.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      iApply ("IH" with "[//] Hwp"). }

    rename Hhm into Hmsc.
    ewp_unfold_head. rewrite Hmh. rewrite Hmc.
    intro_state.

    iAssert (|={E}=> ⌜ can_step (σ, m) ⌝
                      ∗ EWP ms @ E <| Ψ |> {{ φ }}
                      ∗ state_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".

    { iApply ((fupd_plain_keep_l E ⌜can_step (σ, m)⌝
                 (EWP ms @ E <| Ψ |>  {{ φ }} ∗ state_interp σ))%I
               with "[$Hwp $Hsi]").
      iIntros "[??]".
      iMod (ewp_can_step' with "[$][$]") as "%Hdisj".

      iModIntro; iPureIntro; apply nh_nc_can_step; auto. }

    ewp_mask_intro "Hmod".
    construct_wp_nonret.

    simp_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { ewp_cleanup_mod. ewp_mask_elim. iFrame.
      iApply ("IH" with "[//] Hwp"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    ewp_unfold ms. rewrite Hmsh. rewrite Hmsc. iMod "Hmod". spec_state. spec_step.
    ewp_mask_elim.
    iDestruct "Hwp" as ">(SI & Hwp)"; iFrame.
    iModIntro; iApply ("IH" with "[//] Hwp").
  Qed.

  Lemma pure_ewp {A E} E' Ψ (φ : A → Prop) (ψ : E → Prop) m :
    pure_wp m φ ψ →
    ⊢ EWP m @ E' <| Ψ |> {{ RET a => ⌜φ a⌝ | EXN e => ⌜ψ e⌝ }}.
  Proof.
    iIntros (Hm).
    iLöb as "IH" forall (m Hm).
    iApply ewp_unfold; rewrite /ewp_pre /=.

    destruct (is_handleable m) as [ h | ] eqn:R.
    - (* [m] is handleable *)
      destruct h as [ a | e | | eff f ].
      + (* [ret]'s satisfy [φ] *)
        destruct m as [| | | |???[]|]; discriminate || injection R as ->.
        by eapply invert_pure_wp_ret in Hm.
      + (* [throw]'s satisfy [ψ] *)
        destruct m as [| | | |???[]|]; discriminate || injection R as ->.
        by eapply invert_pure_wp_throw in Hm.
      + (* [crash]'s satisfy [ψ] *)
        destruct m as [| | | |???[]|]; try discriminate.
        by eapply invert_pure_wp_crash in Hm.
      + (* [perform]'s are not immediately pure *)
        destruct m as [| | | |???[]|]; discriminate || injection R as -> ->.
        by apply invert_pure_wp_stop in Hm.

    - (* [m] is not handleable *)
      destruct (is_concurrent m) as [ c | ] eqn:R'.
      (* [m] is concurrent: *)
      { destruct m as [| | | |???[]|]; try discriminate;
          by apply invert_pure_wp_stop in Hm. }
      (* [m] is not concurrent *)
      intro_state.
      ewp_mask_intro "Hmod".
      iSplit.
      + (* so [m] can step because it is [pure] *)
        destruct (pure_wp_progress m Hm) as [(a, ->)|[(e, ->)|]]; auto; discriminate.
      + (* and no step can change [σ] or escape [pure] *)
        intro_step.
        ewp_cleanup_mod. ewp_mask_elim.
        destruct (pure_wp_preservation Hm Hstep) as (Hm' & <-).
        iFrame.
        by iApply "IH".
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

Section ewp_eval.

  Context `{!osirisGS Σ}.

  Lemma ewp_module η sitems (Q : val -> iProp Σ) :
    EWP (eval_sitems (η, []) sitems) {{ ensures '(_, δ), Q (VStruct δ) }} -∗
      EWP (eval_mexpr η (MStruct sitems)) {{ ensures v, Q v }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr. iApply ewp_bind.
    iApply (ewp_mono with "Hsitems").
    iIntros ([ ηδ | e ]); [ simpl | done ].
    destruct ηδ; iIntros "HQ".
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitems_cons ηδ sitem sitems E ψ Q (φ : env * env -> iProp Σ) :
    EWP eval_sitem ηδ sitem @ E <| ψ |> {{ ensures ηδ, φ ηδ }} -∗
      (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| ψ |> {{ Q }}) -∗
      EWP eval_sitems ηδ (sitem :: sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply ewp_bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

  Lemma ewp_sitems_nil ηδ E ψ Q :
    Q (O2Ret ηδ) -∗
      EWP eval_sitems ηδ [] @ E <| ψ |> {{ Q }}.
  Proof.
    simpl_eval_sitems.
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitem_letrec_singleton (spec : val -> iProp Σ) η δ x af E ψ :
    spec (VCloRec η [RecBinding x af] x) -∗
      EWP eval_sitem (η, δ) (ILetRec [RecBinding x af]) @ E <| ψ |>
      {{ ensures '(η0, δ0),
          ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem. iApply ewp_value. simpl.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

  Lemma ewp_struct_let η δ bs Q Ψ :
    EWP (eval_bindings η bs) {{ ensures η, Ψ η }} -∗
      (∀ η', Ψ η' -∗ Q (O2Ret (η' ++ η, η' ++ δ))) -∗
      EWP (eval_sitem (η, δ) (ILet bs)) {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hbindings").
    iIntros ([ | ]); [ simpl | done ].
    iIntros. iApply ewp_value.
    by iApply "Hmono".
  Qed.

  Lemma prove_ewp_Par {A X A1 A2 X'} m1 m2 (k : outcome2 (A1 * A2) X' -> micro A X) φ1 φ2 E ψ Q :
    EWP m1 @ E <|ψ|> {{ ensures v, φ1 v }} -∗
    EWP m2 @ E <|ψ|> {{ ensures v, φ2 v }} -∗
    (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗ EWP k (O2Ret (v1, v2)) @ E <|ψ|> {{ Q }}) -∗
    EWP (Par m1 m2 k) @ E <|ψ|> {{ Q }}.
  Proof.
    iIntros "Hm1 Hm2 Hk".
    iApply (ewp_Par with "Hm1 Hm2"); simpl; try iIntros (e) "[]".
    iApply "Hk".
  Qed.

  Lemma ewp_struct_let_single spec η δ name e :
    EWP (eval η e) {{ ensures v, spec v }} -∗
      EWP (eval_sitem (η, δ) (ILet [Binding (PVar name) e]))
      {{ ensures '(η', δ'),
          ∃ v : val, spec v ∧ ⌜η' = (name, v) :: η ∧ δ' = (name, v) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem; simpl_eval_bindings. iApply ewp_bind.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "Hspec").
    { by iApply ewp_value. }
    iIntros (v ?) "Hspec ->". simpl_eval_pat; unfold widen; simpl.
    rewrite try_ret. iApply ewp_value. simpl. iApply ewp_value.
    iExists v.
    iFrame. iPureIntro; auto.
  Qed.

  Lemma ewp_sitem_extend η δ es E ψ (Q : env * env -> iProp Σ) :
    EWP eval_type_extensions es @ E <| ψ |>
      {{ ensures δ', Q (δ' ++ η, δ' ++ δ) }} -∗
      EWP eval_sitem (η, δ) (IExtend es) @ E <| ψ |> {{ ensures v, Q v }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl; iIntros "HQ" | done ].
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitems_extend sitems η δ x E ψ Q :
    (∀ ηδ', (∃ l, ⌜ηδ' = ((x, VLoc l) :: η, (x, VLoc l) :: δ)⌝ ∗ l ↦ V #()) -∗
              EWP eval_sitems ηδ' sitems @ E <| ψ |> {{ Q }}) -∗
      EWP eval_sitems (η, δ) ((IExtend [x]) :: sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (ewp_sitems_cons).
    { iApply (ewp_sitem_extend).
      iApply ewp_alloc.
      iIntros "!>" (l) "Hl".
      rewrite /continue. iApply ewp_value.
      Unshelve.
      2: (apply (λ ηδ,
              (∃ l, ⌜ηδ = ((x, VLoc l) :: η, (x, VLoc l):: δ)⌝ ∗ l ↦ V VUnit)%I)).
      iExists l; iFrame. iPureIntro; reflexivity. }
    iApply "Hcov".
  Qed.

  Lemma ewp_sitem_open η δ me E ψ Q φ δ' :
    EWP eval_mexpr η me @ E <| ψ |> {{ ensures v, ⌜ v = VStruct δ' ⌝ ∗ φ δ' }} -∗
    ( ∀ δ', φ δ' -∗ Q (O2Ret (δ' ++ η, δ)) ) -∗
    EWP eval_sitem (η, δ) (IOpen me) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply ewp_bind. iApply ewp_bind.
    iApply (ewp_mono with "Hme").
    iIntros ([|]); [ simpl | done ].
    iIntros "[-> Hφ]".
    iApply ewp_try. repeat iApply ewp_value.
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma ewp_type_extension_cons e es E ψ Q :
    ▷ (∀ l, l ↦ V #() -∗
          EWP eval_type_extensions es @ E <| ψ |>
            {{ ensures δ, Q (O2Ret ((e, VLoc l) :: δ)) }}) -∗
    EWP eval_type_extensions (e :: es) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hes". simpl.
    iApply ewp_alloc.
    iModIntro.
    iIntros "%l Hl".
    iApply ewp_bind. iApply ewp_value. iApply ewp_bind.
    iSpecialize ("Hes" with "Hl").
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl | done ]; iIntros "HQ".
    by iApply ewp_value.
  Qed.

  Lemma ewp_type_extension_nil E ψ Q :
    Q (O2Ret []) -∗
    EWP eval_type_extensions [] @ E <| ψ |> {{ Q }}.
  Proof. iIntros "HQ". simpl. by iApply ewp_value. Qed.

  Lemma ewp_sitem_let_singleton_var (spec : val -> iProp Σ) η δ x e E ψ Q :
    EWP eval η e @ E <| ψ |> {{ ensures v, spec v }} -∗
      (∀ v, spec v -∗ Q (O2Ret ((x, v) :: η, (x, v) :: δ))) -∗
      EWP eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "He HQ".
    simpl_eval_sitem. simpl_eval_bindings.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_value. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    simpl_eval_pat. iApply ewp_value.
    by iApply "HQ".
  Qed.

  Lemma ewp_sitems_let_singleton_var (spec : val -> iProp Σ) sitems η δ x e E ψ Q :
    EWP eval η e @ E <| ψ |> {{ ensures v, spec v }} -∗
      (∀ ηδ', (∃ v, ⌜ηδ' = ((x, v) :: η, (x, v) :: δ)⌝ ∗ spec v) -∗
                EWP eval_sitems ηδ' sitems @ E <| ψ |> {{ Q }}) -∗
      EWP eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "He Hcov".
    simpl_eval_sitems; simpl_eval_bindings; simpl.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_value. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    unfold widen; simpl_eval_pat; simpl.
    iApply "Hcov".
    iExists v1. by iFrame.
  Qed.

End ewp_eval.


(** *General tactics *)
(* These tactics are declared here because they depende on
   1. Lemmas defined in [basic_rules.v] such as [ewp_value]
   2. The [simp] tactic, which is defined in [simp_tactics.v]  *)

(* Start proof mode. *)
Ltac Start_proof := iStartProof.

(* Try to simplify the goal using the [simp] relation *)
Ltac Simp :=
  iApply ewp_simp; first try solve [simp].

(* Hoare-style rules that correspond to [rule] lemmas *)
Ltac Try := iApply ewp_try.

Ltac Ret := repeat iApply ewp_value.

Ltac Throw := iApply ewp_throw.

Ltac Par :=
  lazymatch goal with
  | |- environments.envs_entails _ (ewp_def _ (Par (ret _) (ret _) _) _ _) =>
      iApply ewp_simp; first simp
  | |- environments.envs_entails _ (ewp_def _ (Par _ (Ret _) _) _ _) =>
      iApply ewp_simp; first simp
  | |- environments.envs_entails _ (ewp_def _ (Par (ret _) _ _) _ _) =>
      iApply ewp_simp; first simp
  | |- environments.envs_entails _ (ewp_def _ (Par _ _ _) _ _) =>
      iApply ewp_Par
  | _ => fail "The goal must be a par to apply [ewp_par]."
  end; try done.

Ltac Bind := first [ iApply ewp_fmap | iApply ewp_bind ].
