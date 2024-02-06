Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
From iris.proofmode Require Import proofmode.

From iris.prelude Require Import options.
From iris.base_logic.lib Require Import own.

From osiris.program_logic Require Import wp tactics.
From osiris Require Import syntax semantics.

Section proof.

  Context {R E : Type}.
  Context `{!osirisGS Σ}.

  Implicit Type φ : @value R E → iProp Σ.
  Implicit Type m : micro R E.
  Implicit Type n : micro R E.

  Notation store_interp := (@store_interp R E _ _).
  Notation step := (@step.step R E).

  #[local] Instance invGS_gen_osiris : invGS_gen HasNoLc Σ :=
    (osiris_invGS Σ).

  Lemma wp_step {σ σ' m n φ}:
    step (σ, m) (σ', n) →
    store_interp σ -∗
    £ 1 -∗
    WP m {{ φ }} ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    (store_interp σ' ∗ WP n {{ φ }}).
  Proof.
    intro Hstep.
    iIntros "Hsi H£ Hwp".
    wp_unfold m.
    pose proof (step_not_value Hstep) as ->.
    spec_state "Hwp".
    destruct_wp_nonret. iModIntro.
    eassert (prim_step m σ _ _ _ _).
    { constructor; eauto. }
    iSpecialize ("Hwp" $! _ _ _ H with "H£").
    iMod "Hwp". iModIntro. iNext.
    do 2 iMod "Hwp".
    iMod (@fupd_mask_subseteq _ _ _ ∅) as "Hmod";
    [ set_solver | iModIntro ]. iMod "Hmod". iModIntro.
    iDestruct "Hwp" as "[$ [$ _]]".
    Unshelve. all : solve [exact 1 | exact nil].
  Qed.

  (* Pure values *)
  Definition wp_ret φ (a : R) :
    ipure φ a ⊢ WP (Ret a : micro R E) {{ φ }}.
  Proof.
    iIntros "Hφ"; rewrite wp_unfold; by cbn.
  Qed.
  Definition wp_ret' s a e φ:
    ipure φ a ⊢ WP (Ret a : micro R E) @ s; e {{ φ }}.
  Proof.
    iIntros "Hφ"; rewrite wp_unfold; by cbn.
  Qed.

  (* Cut rule *)
  Lemma wp_bind (m1 : micro R E) (m2 : R -> micro R E) ψ:
    WP m1 {{ lift_ipure (fun (v : R) => WP (m2 v) {{ ψ }}) }} ⊢
    WP (bind m1 m2 : micro R E) {{ ψ }}.
  Proof.
    iLöb as "IH" forall (m1 m2 ψ).
    iIntros "Hwp".
    wp_case_is_ret m1 Hret.
    (* Case: [m1] is [ret _]. *)
    { cbn; rewrite wp_unfold; rewrite /wp_pre /=.
      by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { wp_unfold m1.
      (* Case analysis on [try] *)
      case_eq (is_ret (bind m1 m2)); [
        intros ? Hret';
        apply invert_is_ret_Some in Hret'
      | intros Hret'
      ].
      { apply invert_bind_ret in Hret';
        destruct Hret' as (?&?&?); subst; inversion Hret. }

      case_eq (is_throw m1);
        [intros ? Hthrow;
          apply invert_is_throw_Some in Hthrow | intros Hthrow].
      { rewrite Hthrow; cbn;
        wp_unfold_all; iMod "Hwp"; done. }

      apply is_not_ret_or_throw_to_value in Hret; auto; rewrite Hret.

      wp_unfold (bind m1 m2 : micro R E).
      eapply (to_value_None_bind m1 m2) in Hret; rewrite Hret.
      intro_state;
      iSpecialize ("Hwp" $! _ _ _ _ _ with "Hsi").
      iMod "Hwp"; iDestruct "Hwp" as (?) "Hwp".
      iModIntro.
      iSplitL "".
      { iPureIntro.
        eapply reducible_bind; auto.
        Unshelve. all : eauto. }

      iIntros (????Hstep) "H£".
      apply reducible_not_val in H.
      destruct Hstep as (Hstep&?); subst.

      destruct (invert_step_bind Hstep) as (m'1 & Hstep' & ->).
      { apply to_value_is_not_ret; auto. }

      clear Hstep; rename Hstep' into Hstep.
      eassert (Hstep_m1: prim_step m1 σ κs _ _ []).
      { constructor; eauto. }
      iSpecialize ("Hwp" $! _ _ _ Hstep_m1 with "H£").
      iMod "Hwp". tick_wp; iMod "Hwp" as "[SI [Hwp H]]";
        iModIntro; iFrame.

      by iApply ("IH" with "Hwp"). }
  Qed. (* LATER: See if we can clean up this proof using [wp_try] Proof. *)

  (* Try-catch *)
  Lemma wp_try m (f : R -> micro R E) (h : E -> micro R E) φ :
    WP (m : micro R E)
      {{ | RET x =>
              WP (f x : micro R E) {{ φ }} ;
          | EXN y =>
              WP (h y : micro R E) {{ φ }} }} -∗
    WP (try m f h : micro R E) {{ φ }}.
  Proof.
    iLöb as "IH" forall (m f h φ).
    iIntros "Hwp".
    wp_case_is_ret m Hret.
    (* Case: [m1] is [ret _]. *)
    (* The result is immediate. *)
    { cbn; rewrite wp_unfold; rewrite /wp_pre /=.
      by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { wp_unfold m.

      (* Case analysis on [try] *)
      case_eq (is_ret (try m f h)); [
        intros ? Hret';
        apply invert_is_ret_Some in Hret'
      | intros Hret'
      ].
      { apply invert_try_ret in Hret'.
        destruct Hret' as [(?&?&?) | (?&?&?)]; subst; [ inversion Hret | ].
        cbn; rewrite H0;
          cbn; rewrite wp_unfold; cbn; by iMod "Hwp". }

      case_eq (is_throw m);
        [intros ? Hthrow;
          apply invert_is_throw_Some in Hthrow | intros Hthrow].
      { rewrite Hthrow; cbn.
        wp_unfold_all. destruct (wp.to_value (h e)); [ by iMod "Hwp" |].
        iIntros (?????) "SI". iMod "Hwp".
        iSpecialize ("Hwp" $! _ _ _ _ _ with "SI"); by iMod "Hwp". }

      apply is_not_ret_or_throw_to_value in Hret; auto; rewrite Hret.

      wp_unfold (try m f h : micro R E).
      eapply (to_value_None_try m f h) in Hret; rewrite Hret.

      intro_state;
      iSpecialize ("Hwp" $! _ _ _ _ _ with "Hsi").
      iMod "Hwp"; iDestruct "Hwp" as (?) "Hwp".
      iModIntro.
      iSplitL "".
      { iPureIntro.
        eapply reducible_try; auto.
        Unshelve. all : eauto. }

      iIntros (????Hstep) "H£".
      assert (Hstep' := H).
      apply reducible_not_val in H.

      destruct Hstep as (Hstep & ?); subst.

      destruct (invert_step_try Hstep) as (m'1 & Hstep'' & ->).
      { destruct Hstep' as (?&?&?&?&?); eexists; apply H0. }
      clear Hstep. rename Hstep' into Hstep.

      eassert (Hstep_m: prim_step m σ κs _ _ _).
      { constructor; eauto. }

      iSpecialize ("Hwp" $! _ _ _ Hstep_m with "H£").
      iMod "Hwp". tick_wp; iMod "Hwp" as "[SI [Hwp H]]";
        iModIntro; iFrame.

      by iApply ("IH" with "Hwp"). }
  Qed.

  (* Inversion laws *)
  Lemma invert_wp_ret φ r :
    ∀ σ, store_interp σ -∗
        WP (Ret r : micro R E) {{ φ }} -∗
        |={⊤}=> store_interp σ ∗ φ (Res r).
  Proof.
    iIntros (?) "Hsi Hwp"; wp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_throw φ exn:
    ∀ σ, store_interp σ -∗
        WP (throw exn : micro R E) {{ φ }} -∗
        |={⊤}=> store_interp σ ∗ φ (Exn exn).
  Proof.
    iIntros (?) "Hsi Hwp"; wp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_crash φ:
    ∀ σ, store_interp σ -∗
        WP (crash : micro R E) {{ φ }} -∗
        |={⊤}=> False.
  Proof.
    iIntros (?) "Hsi Hwp".
    wp_unfold_all. spec_state "Hwp".

    destruct_wp_nonret.
    inversion Hcanstep.
    destruct H as (?&?&?&?); inversion H.
    subst. inversion H0.
    Unshelve. all : solve [ exact 1 | exact nil].
  Qed.

  (* Par combinator *)
  Lemma wp_par (m1 m2 : micro R E)
    {k: R * R → micro R E} {z : E → micro R E} {φ} φ1 φ2:
    WP m1 {{ φ1 }} ⊢
    WP m2 {{ φ2 }} -∗
    (∀ e, φ1 (Exn e) -∗ WP (z e) {{ φ }}) -∗
    (∀ e, φ2 (Exn e) -∗ WP (z e) {{ φ }}) -∗
    (∀ a1 a2,
        φ1 (Res a1) -∗ φ2 (Res a2) -∗
        WP (k (a1, a2)) {{ φ }}) -∗
      WP (Par m1 m2 k z : micro R E) {{ φ }}.
  Proof.
    (* We proceed by Löb-Induction after generalizing [m1] and [m2]. *)
    iLöb as "IH" forall (m1 m2); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

    (* As for the other rules, proof starts by stepping in the WP:
      (1) unfold the wp, (2) introduce a valueid state, (3) introduce the head
      modality and (4) enter in the second branch of the WP. *)
    wp_unfold_head; intro_state.
    iMod (@fupd_mask_subseteq _ _ _ ∅) as "Hmod";
    [ set_solver | iModIntro; construct_wp_nonret ].
    { apply can_step_reducible. eauto with step can_step. }

    (* Make a case study over the possible step. In each case, use FupTrans to
      add the modality [ |={E,∅}=> ] in front of the goal. *)
    { iIntros "H£".

      destruct Hstep as (Hstep & ->); iMod "Hmod" as "_".
      inversion Hstep; dependent destruction H7; subst.

    (* We now examine each of the ways in which [Par m1 m2 k z] can step. *)

    { (* Case: [StepParRetRet].
        Both [m1] and [m2] represent valueues [v1] and [v2]. One can consume [H1]
        and [H2] to learn that the valueues respect their postconditions.
        The inversion does not consume the state-interpretation, which can be
        framed behind the modalities. *)
      iMod (invert_wp_ret with "[$][$]") as "[Hsi H2]".
      iMod (invert_wp_ret with "[$][$]") as "[$ H1]".

      (* Introduce the modality [ |={E,∅}=> ]. *)
      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod";
        [ set_solver | iModIntro ].
      (* The later is not exposed in this rule. Hence, it can simply be
        introduced together with the remaining modalities. *)
      iNext.
      iModIntro; iMod "Hmod"; iModIntro.

      repeat red in Hstep.
      (* Finally, use the hypothesis on [k] to finish the proof. *)
      iSpecialize ("Hjoin" with "H1 H2"); by iFrame. }

    (* In the four following cases, one of the branches of the [Par] is either a
      [crash] or [throw _]. Hence, one can consume the corresponding [WP]
      hypothesis to get [ |={E}=> False ]. As the goal is of the form
      [ |={E,∅}=> G ], by FupTrans, it suffices to show [|={E}=> |={E,∅}=> G].
      Then, by monotony of [ |={E}=> ], one can eliminate [False] and finish
      the proof. *)
    1,2: by iMod (invert_wp_crash with "Hsi [$]") as "%".
    1,2: iMod (invert_wp_throw with "Hsi [$]") as "[$ HΨ]";
      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod";
        [ set_solver | iModIntro ]; iNext; iModIntro;
      iMod "Hmod"; iModIntro; cbn; iFrame.
    1:by iApply ("Hexn1" with "HΨ").
    1:by iApply ("Hexn2" with "HΨ").

    { (* Case: [StepParLeft] *)
      (* [m1] steps to [m'1]. Steps preserve the conjunction of the [WP] and the
        state interpretation. Some modalities need to be stripped from the
        result. *)
      iPoseProof (wp_step H0 with "Hsi H£ H1") as ">H1".
      iMod "H1"; iModIntro. (* After stripping modalities, one can
                                        frame the state interpretation. *)
      iNext. iModIntro; do 2 iMod "H1". iModIntro.
      iDestruct "H1" as "[$ H1]"; cbn; iFrame; iSplitR ""; last done.

      (* The induction hypothesis ends the proof. *)
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* Case: [StepParRight]
        This case is similar to the previous one. *)
      iMod (wp_step H0 with "Hsi H£ H2") as ">H2".
      iModIntro. iNext.
      iMod "H2"; iModIntro. (* After stripping modalities, one can
                                        frame the state interpretation. *)
      iMod "H2".
      iDestruct "H2" as "[$ H2]"; cbn; iFrame; iSplitR ""; last done.
      iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). } }
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* Helper (LATER: Move?) *)

  Ltac to_value_is_Some Hm :=
    apply to_value_is_Some in Hm;
    destruct Hm as [ (?&?&?) | (?&?&?) ]; subst.

  Lemma wp_can_step {σ φ} (m : micro R E) {M}:
    store_interp σ -∗
    wp NotStuck M m φ ={M, ∅}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros "SI Hwp".
    wp_unfold_all.
    destruct (wp.to_value m) eqn: Hm.
    { iMod "Hwp". iApply fupd_mask_intro; first set_solver.
      iIntros "_".
      to_value_is_Some Hm; [ iRight; iRight | iRight; iLeft ];
      iPureIntro; eauto. }
    { iSpecialize ("Hwp" $! _ _ _ _ _ with "SI").
      iMod "Hwp".
      iDestruct "Hwp" as"[%c' _]". iPureIntro.
      left. by apply can_step_reducible. }
    Unshelve. all : solve [exact 1 | exact nil].
  Qed.

  Lemma wp_can_step' {σ φ} (m : micro R E) {M}:
    store_interp σ -∗
    wp NotStuck M m φ ={M}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros.
    iPoseProof (wp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* Simplification is sound. *)

  (* That is, as announced in semantics/simplification.v, if [simplify n m ms]
    holds then the safety of the simplified program [ms] implies the safety
    of the more complex original program [ms]. *)

  Local Lemma wp_simplify i (m ms : micro R E) φ :
    WP ms {{ φ }} -∗
    ⌜ simplify i m ms ⌝ -∗
    WP m  {{ φ }}.
  Proof.
    (* Proceed by Löb induction. *)
    iLöb as "IH" forall (i m ms).
    (* Then, perform well-founded induction over [n]. *)
    iInduction i as (? & ?) "IHn"
                            using (well_founded_induction lt_wf)
                            forall (m ms).
    (* Introduce the hypotheses. *)
    iIntros "Hwp" (Hsimp).

    (* Examine [m]. *)
    wp_case_is_ret m Hretm.
    (* If [m] is [ret a], then [ms] is also [ret a], so we are done. *)
    { clarify_simplify. iAssumption. }

    (* Thus, in the following, we assume [m] is not [ret _]. *)
    (* Examine [m] again, on whether it is a [throw]. *)
    wp_case_is_throw m Hthrow.
    { (* If [m] is [throw e], then [ms] is also [throw e], so we are done. *)
      apply destruct_simplify_throw in Hsimp; by subst. }

    (* Begin unfolding the definition of [WP m ...]. *)
    wp_unfold m.

    (* Simplify match on [m]. *)
    pose proof (is_not_ret_or_throw_to_value _ Hretm Hthrow) as ->.
    intro_state.

    (* Examine [ms] on whether it is a [ret]. *)
    wp_case_is_ret ms Hretms.

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is able to step. *)
      iApply fupd_frame_l; iSplit.
      { pose proof (invert_simplify_ret _ _ _ σ Hsimp Hretm) as Hsimpl.
        iPureIntro.
        destruct Hsimpl as (?&Hsimpl); destruct x;
          repeat eexists; apply Hsimpl. }

      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
      iModIntro.
      iIntros (σ' m' obs []) "H£"; subst.
      iMod "Hmod" as "_".

      (* Examine one step of [m] to [m']. The simulation diagram in this case
      tells us that this reduction step takes us closer to [ret a].
      That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
      pose proof (simplify_ret_step_diagram Hsimp H)
        as (n' & ? & ? & ?); subst.
      (* We are then able to use the inner induction hypothesis. *)
      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
      do 3 iModIntro.
      iMod "Hmod"; iModIntro.
      cbn; iFrame.

      iApply ("IHn" with "[//] Hwp [//]"). }

    (* Examine [ms] on whether it is a [throw]. *)
    wp_case_is_throw ms Hthrow_ms.
    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is able to step. *)
      iApply fupd_frame_l; iSplit.
      { pose proof (invert_simplify_throw _ _ _ σ Hsimp Hthrow) as Hsimpl.
        iPureIntro.
        destruct Hsimpl as (?&Hsimpl); destruct x;
          repeat eexists; apply Hsimpl. }

      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
      iModIntro.
      iIntros (σ' m' obs []) "H£"; subst.
      iMod "Hmod" as "_".

      (* Examine one step of [m] to [m']. The simulation diagram in this case
      tells us that this reduction step takes us closer to [ret a].
      That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
      pose proof (simplify_throw_step_diagram Hsimp H)
        as (n' & ? & ? & ?); subst.
      (* We are then able to use the inner induction hypothesis. *)
      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
      do 3 iModIntro.
      iMod "Hmod"; iModIntro.
      cbn; iFrame.

      iApply ("IHn" with "[//] Hwp [//]"). }

    (* [ms] is neither a [ret _] or [throw _]. *)

    (* Then, [WP ms ...] implies than [ms] can step.
    This implies that [m], too, can step. *)

    iAssert (|={⊤}=> ⌜ can_step (σ, m) ⌝
                    ∗ wp NotStuck ⊤ ms φ
                    ∗ store_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".
    { iApply ((fupd_plain_keep_l ⊤ ⌜can_step (σ, m)⌝
                                (wp NotStuck ⊤ ms φ ∗ store_interp σ))%I
              with "[$Hwp $Hsi]").
      iIntros "[??]";
        iMod (wp_can_step' with "[$][$]") as "%Hdisj".
      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simplify_can_step. }
      destruct H; exfalso; eauto. }
    iApply fupd_frame_l; iSplit.
    { iPureIntro; by apply can_step_reducible. }
    iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
    iModIntro. iIntros (σ' m' efs Hstep).
    iMod "Hmod" as "_". destruct Hstep as (Hstep&->).

    (* We now examine an arbitrary step of [m] to [m']. *)
    (* Exploit the main simulation diagram. *)
    pose proof (simplify_step_diagram Hsimp Hstep)
      as (ms' & n' & i' & Hstep' & Hsimp' & Hcases);
      clear Hsimp Hstep.
    destruct_simplify_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod"; first set_solver.
      iIntros "H£".
      do 3 iModIntro.
      iMod "Hmod"; iModIntro.
      iFrame; cbn. iSplitR ""; last done.
      iApply ("IHn" with "[//] Hwp [//]"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    iClear "IHn".
    wp_unfold ms.

    pose proof (is_not_ret_or_throw_to_value _ Hretms Hthrow_ms) as ->.
    spec_state "Hwp". destruct_wp_nonret.

    assert (prim_step ms σ nil ms' m' nil) by (by constructor).

    iSpecialize ("Hwp" $! _ _ _ H0).
    cbn.
    iIntros "H£".
    iSpecialize ("Hwp" with "H£").
    iMod "Hwp". iModIntro; iNext. iMod "Hwp"; iModIntro; iMod "Hwp".
    iModIntro.
    iDestruct "Hwp" as "(SI & Hwp & _)"; iFrame.
    iSplitR ""; last done.
    iApply ("IH" with "Hwp [//]").
    Unshelve.
    all : solve [exact nil | exact 1].
  Qed.

  (* A corollary, for public use: [simp] is sound. *)

  Lemma wp_simp (m m' : micro R E) φ :
    simp m m' →
    WP m' {{ φ }} ⊢
    WP m  {{ φ }}.
  Proof.
    iIntros (Hsimp) "Hwp".
    apply simp_simplify in Hsimp.
    destruct Hsimp as (n & Hsimp).
    iApply (wp_simplify with "Hwp [//]").
  Qed.

End proof.
