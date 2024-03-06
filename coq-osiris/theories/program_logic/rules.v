Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp ewp_tactics.
From osiris.semantics Require Import step code simplification.

(* ------------------------------------------------------------------------ *)

Section ewp_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  (* Values *)
  Lemma ewp_value E Ψ Φ v :
    Φ (O2Ret v) -∗ EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_ret_inv E Ψ Φ v :
    EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Ret v).
  Proof. Admitted.

  Lemma ewp_throw E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_throw_inv E Ψ Φ v :
    EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Throw v).
  Proof. Admitted.

  Lemma ewp_crash_inv E Ψ Φ :
    EWP (Crash : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ False.
  Proof. Admitted.

  Lemma ewp_outcome2 E Ψ Φ v :
    Φ v -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.
  Lemma ewp_outcome2_inv E Ψ Φ v :
    EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
  Proof. Admitted.

  Lemma ewp_outcome2_fupd E Ψ Φ v :
    (|={E}=> Φ v) -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

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
    destruct (is_handleable m) eqn: Hmh.
    { destruct m; inversion Hmh; subst; try solve [inversion Hstep];
        destruct c; inversion H1; subst.
      inversion Hstep. }
    iSpecialize ("Hwp" with "Hsi").
    iMod "Hwp". iDestruct "Hwp" as (?) "Hwp".
    iSpecialize ("Hwp" $! _ _ Hstep).
    iMod "Hwp". iModIntro. iModIntro. iNext.
    try iModIntro; auto.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_mono E m φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ φ' }}.
  Proof. Admitted.

  (* TODO: Strong monotonicity principle over ordering on protocols *)

  Lemma ewp_pers_smono E E' Ψ Ψ' Φ Φ' m :
    E ⊆ E' →
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E'}=∗ Φ' v) -∗
    EWP m @ E' <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros (HE) "He #HΦ".
  Admitted.

  Corollary ewp_pers_mono E Ψ Φ Φ' m :
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E}=∗ Φ' v) -∗
    EWP m @ E <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros "He #HΦ".
    by iApply (ewp_pers_smono with "He").
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd E m Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => |={E}=> Φ v }} -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (ewp_pers_mono with "He").
    auto.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)
  Lemma ewp_try {B X'} E m (f : A -> micro B X') (h : X -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{| RET v => EWP (f v) @ E <| Ψ |> {{ Φ }};
                        | EXN v => EWP (h v) @ E <| Ψ |> {{ Φ }}}} -∗
    EWP (try m f h) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

  (** *Bind rule *)
  Lemma ewp_bind {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ RET v, EWP (k v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

End ewp_rules.

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
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ Crash _ _)] =>
          iMod (ewp_crash_inv with "[$]") as "%"
      end
  end.
(* ------------------------------------------------------------------------ *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Implicit Type Ψ : P.
  Import ewp_rules_tactics.

  Notation do v := (stop CPerform v).

  Lemma ewp_perform {B X'} E Ψ v Φ (k : _ -> micro B X'):
    prot_spec Ψ v (fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }}) -∗
    EWP (Stop CPerform v k) @ E <| Ψ |> {{ Φ }}.
  Proof.

    iIntros "HP".
    ewp_unfold_head.
    iApply prot_mono; iFrame.
    iIntros (?) "HΦ". by iNext.
  Qed.

  Lemma ewp_do E Ψ v Φ:
    prot_spec Ψ v Φ ⊢ EWP (do v) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP". iApply ewp_perform.
    iApply prot_mono; iFrame.
    iIntros (?) "HΦ". iNext.
    by iApply ewp_outcome2.
  Qed.

  Lemma ewp_perform_inv {B X'} E Ψ v Φ (k : _ -> micro B X'):
    EWP (Stop CPerform v k) @ E <| Ψ |> {{ Φ }} -∗
    prot_spec Ψ v (fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }}).
  Proof.
    iIntros "HP".

    ewp_unfold_all.
    iApply prot_mono; iFrame.
    iIntros (?) "HΦ". by iNext.
  Qed.

  Definition shallow_handler E Ψ Φ
    (h : Outcome -> microvx) (* Handler for outcomes *)
    (eh : Eff -> C.continuation -> microvx) (* Effect handler *)
    Ψ' Φ' :=
    ((∀ v, Φ v -∗ ▷ EWP (h v) @ E <| Ψ' |> {{ Φ' }}) ∧
    (∀ v k l, prot_spec Ψ v (fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }}) -∗
       mapsto l (DfracOwn 1) (K k) ==∗
       ▷ EWP (eh v l) @ E <| Ψ' |> {{ Φ' }}))%I.

  Definition handler (h : Outcome -> microvx) (eh : Eff -> C.continuation -> microvx) :
    _ -> microvx :=
    fun x =>
      match x with
        | O3Ret v => h (O2Ret v)
        | O3Throw e => h (O2Throw e)
        | O3Perform e c => eh e c
      end.

  (* Specification for handlers (shallow by default) *)
  Lemma ewp_handler E Ψ Φ Ψ' Φ' e h eh:
    EWP e @ E <| Ψ |> {{ Φ }} -∗
    shallow_handler E Ψ Φ h eh Ψ' Φ' -∗
    EWP (Handle e (handler h eh)) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)
    iLöb as "IH" forall (e h eh).

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
      iSpecialize ("Hsh" $! _ _ with "HP").

      iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH _]]"; first done.
      iSpecialize ("Hsh" with "HH"). iMod "Hsh".

      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iFrame. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iApply ("IH" with "H Hsh"). }
  Qed.

  (* Par combinator TODO: For now, the statement maintains the same Ψ .. *)
  Lemma ewp_par {E A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X')
    {k: outcome2 (A1 * A2) X' → micro A X} {φ} φ1 φ2 Ψ :
      EWP m1 @ E <| Ψ |> {{ φ1 }} ⊢
      EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
      ( ∀ e, φ1 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ e, φ2 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ a1 a2,
          φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗
          EWP (k (O2Ret (a1, a2))) @ E <| Ψ |> {{ φ }}) -∗
      EWP (Par m1 m2 k) @ E <| Ψ |> {{ φ }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2 k); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

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
      iApply ewp_perform.
      iApply prot_mono; iFrame.
      iIntros (?) "Hk".
      iNext.
      iApply ("IH" with "Hk H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParPerformRight] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      iPoseProof (ewp_perform_inv with "[$]") as "H2".
      iApply ewp_perform.
      iApply prot_mono; iFrame.
      iIntros (?) "H2".
      iNext.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H1") as ">H1".
      ewp_mask_elim. iMod "H1" as "[$ H1]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParRight] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H2") as ">H2".
      ewp_mask_elim. iMod "H2" as "[$ H2]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }
  Qed.

  Lemma ewp_can_step {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E, ∅}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None⌝.
  Proof.
    iIntros "SI Hwp".
    ewp_unfold_all.
    destruct (is_handleable m) eqn: Hm.
    (* TODO: Clean up *)
    { destruct h; try iMod "Hwp"; try (iApply fupd_mask_intro; first set_solver);
        iIntros "_"; iPureIntro; right; eauto. }
    { iSpecialize ("Hwp" with "SI"). iMod "Hwp".
      iDestruct "Hwp" as (Hwp) "Hwp". iPureIntro; auto. }
  Qed.

  Lemma ewp_can_step' {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None⌝.
  Proof.
    iIntros.
    iPoseProof (ewp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

  Lemma destruct_simp_alloc : forall E X x (k : _ -> micro E X) e,
      simp (Stop CAlloc x k) e -> e = Stop CAlloc x k.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma destruct_simp_load : forall E X x (k : _ -> micro E X) e,
      simp (Stop CLoad x k) e -> e = Stop CLoad x k.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma destruct_simp_store : forall E X x (k : _ -> micro E X) e,
      simp (Stop CStore x k) e -> e = Stop CStore x k.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma destruct_simp_continue : forall E X x (k : _ -> micro E X) e,
      simp (Stop CContinue x k) e -> e = Stop CContinue x k.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma destruct_simp_discontinue : forall E X x (k : _ -> micro E X) e,
      simp (Stop CDiscontinue x k) e -> e = Stop CDiscontinue x k.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma destruct_simp_stop : forall X0 Y E' x (k : _ -> micro A X) x' k' (c : C.code X0 Y E'),
      simp (Stop c x k) (Stop CPerform x' k') ->
      match c with
      | CEval => True
      | CLoop => True
      | CPerform => True
      | _ => False
      end.
  Proof.
    intros; dependent induction H0; eauto.
    destruct c; eauto; clarify_simp.
    - eapply destruct_simp_alloc in H0_; subst.
      specialize (IHsimp2 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); auto.
    - eapply destruct_simp_load in H0_; subst.
      specialize (IHsimp2 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); auto.
    - eapply destruct_simp_store in H0_; subst.
      specialize (IHsimp2 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); auto.
    - eapply destruct_simp_continue in H0_; subst.
      specialize (IHsimp2 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); auto.
    - eapply destruct_simp_discontinue in H0_; subst.
      specialize (IHsimp2 _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl); auto.
  Qed.

  Lemma destruct_simp_handle : forall n h (e :  micro A X),
      simp (Handle n h) e -> e = Handle n h.
  Proof.
    intros; dependent induction H0; eauto.
  Qed.

  Lemma ewp_simp E m ms Ψ φ:
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
      inversion Hmh. destruct c; inversion H1; subst.
      clarify_simp.
      iApply ewp_perform.
      iPoseProof (ewp_perform_inv with "Hwp") as "Hwp".
      iApply prot_mono; iFrame.
      iIntros (w) "Hw". iNext.
      iApply ("IH" $! _ _ (H2 w) with "Hw"). }

    (* Examine [ms] on whether it is a [ret]. *)
    wp_case_is_ret ms Hretms.

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh.
      intro_state. ewp_mask_intro "Hmod".
      iSplitL "".
      { iPureIntro.
        epose proof (invert_simp_final _ Hsimp) as [|];
          [ by prove_final |
            subst; try destruct_is_ret; try destruct_is_throw |
            eauto with can_step ].
        inversion Hmh. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Examine [ms] on whether it is a [throw]. *)
    wp_case_is_throw ms Hthrow_ms.
    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh.
      intro_state. ewp_mask_intro "Hmod".
      iSplitL "".
      { iPureIntro.
        epose proof (invert_simp_final _ Hsimp) as [|];
          [ by prove_final |
            subst; try destruct_is_ret; try destruct_is_throw |
            eauto with can_step ].
        inversion Hmh. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* [ms] is neither a [ret _] or [throw _]. *)
    destruct (is_handleable ms) eqn: Hmh_ms.
    { destruct ms; inversion Hmh_ms; cbn in *; subst.
      - inversion Hretms.
      - inversion Hthrow_ms.
      - destruct c; inversion H1; subst.

        destruct m; try solve [inversion Hmh | clarify_simp]; eauto.

        { apply destruct_simp_handle in Hsimp; inversion Hsimp. }


        ewp_unfold_head. rewrite Hmh.
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

          iModIntro; iPureIntro; destruct Hdisj.
          { eauto using invert_simp_can_step. }

          exfalso. apply H0; auto. }


        + pose proof (destruct_simp_stop _ _ _ _ _ _ _ _ Hsimp);
            destruct c; inversion H0; clear H0; clarify_simp.

          { (* CEval *)

          ewp_unfold_head.
          intro_state. ewp_mask_intro "Hmod".
          construct_wp_nonret.
          destruct_step. cbn in *.
          ewp_mask_elim.

          iFrame.
          iApply ("IH" $! _ _ _ with "Hwp"). Unshelve.
          remember (η, e).
          inversion Hsimp. destruct p; inversion Heqp; subst.
          dependent destruction H2. constructor.
          subst.  admit. }

        { (* CLoop *)

          ewp_unfold_head.
          intro_state. ewp_mask_intro "Hmod".
          construct_wp_nonret.
          destruct_step. cbn in *.
          ewp_mask_elim.

          iFrame.
          iApply ("IH" $! _ _ _ with "Hwp"). Unshelve.
          remember (η, x1, i1, i2, e).
          inversion Hsimp. destruct p; inversion Heqp; subst.
          dependent destruction H2. constructor.
          subst. admit. }

        + admit.
        + admit. }

    ewp_unfold_head. rewrite Hmh.
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

      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simp_can_step. }

      exfalso. apply H0; auto. }

    ewp_mask_intro "Hmod".
    construct_wp_nonret.

    simp_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { ewp_mask_elim. iFrame.
      iApply ("IH" with "[//] Hwp"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    ewp_unfold ms. rewrite Hmh_ms.
    iSpecialize ("Hwp" with "Hsi"). iMod "Hmod".
    iMod "Hwp".
    iDestruct "Hwp" as (?) "Hwp".
    iSpecialize ("Hwp" $! _ _ Hstep).
    iMod "Hwp". iModIntro. iNext.
    iMod "Hwp". iDestruct "Hwp" as "(SI & Hwp)"; iFrame.
    iModIntro.
    iApply ("IH" with "[//] Hwp").

  Admitted.

End wp_handler_rules.

