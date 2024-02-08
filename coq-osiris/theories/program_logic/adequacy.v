From iris.base_logic.lib Require Import fancy_updates gen_heap ghost_map.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe wp.

(** *Adequacy

   To understand the adequacy result derived from the Iris [adequacy] theorem
   from the default weakest precondition instantiation via [Language] as
   defined in [wp.v], we show that the statement of safety in [safe.v] is
   logically equivalent to it. *)

(* The safety statement proved is stronger than the adequacy statement in
  Iris. *)
Lemma safe_adequate {A X} s (e : micro A X) σ φ :
  safe (σ, e) (λ _ a, φ (Res a)) ->
  adequate s e σ (λ v _, φ v).
Proof.
  intros * Hsafe; constructor.
  { (* [adequacy_result] : if it steps eventually to a value, then it
     satisfies the postcondition φ. *)

    intros * Hsteps; apply erased_steps_nsteps in Hsteps.
    destruct Hsteps as (n & κs & Hstep).

    (* How many steps did it take to get to a value? *)
    clear s; revert e σ κs v2 t2 σ2 φ Hstep Hsafe.

    (* Induction on number of steps *)
    induction n; intros * Hstep Hsafe; cbn in Hstep.
    - (* Zero steps: it is a value already *)
      inversion Hstep; subst.
      specialize (Hsafe 1%nat). cbn in Hsafe.
      destruct Hsafe as [ Hsafe | Hsafe ].
      + destruct Hsafe as (?&?&Houtcome&?);
          unfold of_outcome in Houtcome; destruct v2;
          inversion Houtcome; by subst.
      + destruct Hsafe as (Hbase & Hsafe).
          destruct v2; inversion Hbase; inversion H.
    - (* At least one step *)
      inversion Hstep as [ | m ρ1 ρ2 ρ3 κ κs' Hstep' Hnsteps];
        clear Hstep; subst.
      destruct Hstep'; subst; inversion H; subst.
      destruct t1; inversion H2; subst; cbn in *; cycle 1.
      { (* absurd. *) destruct t1; cbn in H4; inversion H4. }

      destruct H1; subst.
      eapply IHn; first done.
      eapply invert_safe_step; eauto. }

  { (* [adequate_not_stuck]: the expression either steps or is a value *)
    intros * -> Hstep He2; subst.

    apply erased_steps_nsteps in Hstep.
    destruct Hstep as (n & κs & Hstep).

    (* How many steps did it take? *)
    revert e e2 σ κs t2 σ2 φ Hsafe Hstep He2.

    (* Induction on number of steps *)
    induction n; intros * H Hstep He2; cbn in Hstep.
    - (* Zero steps: it is a value already *)
      inversion Hstep; subst.
      specialize (H 1%nat). cbn in H.
      destruct H.
      (* Value *)
      + destruct H as (?&?&?&?); inversion H; subst.
        apply elem_of_list_singleton in He2; subst;
          constructor; eauto.
      + destruct H.
        apply elem_of_list_singleton in He2; subst.
        right; by apply can_step_reducible.

    - (* At least one step *)
      inversion Hstep; subst; clear Hstep.
      destruct H1; subst; inversion H0; subst.
      destruct t1; inversion H4; subst; cbn in *; cycle 1.
      { (* absurd. *) destruct t1; cbn in H6; inversion H6. }

      destruct H3; subst.
      eapply IHn; last done.
      eapply invert_safe_step; eauto. done. }
Qed.

(* Specialized instance of the lemma above.
   TODO: Can we reuse the proof from above to prove this fact? *)
Fact safe_adequate_res {A X} (e : micro A X) σ φ :
  safe (σ, e) (λ _ a, φ a) ->
  adequate NotStuck e σ (λ v _, ∃ x, v = Res x /\ φ x).
Proof.
  intros * Hsafe; constructor.
  { (* [adequacy_result] : if it steps eventually to a value, then it
     satisfies the postcondition φ. *)

    intros * Hsteps; apply erased_steps_nsteps in Hsteps.
    destruct Hsteps as (n & κs & Hstep).

    (* How many steps did it take to get to a value? *)
    revert e σ κs v2 t2 σ2 φ Hstep Hsafe.

    (* Induction on number of steps *)
    induction n; intros * Hstep Hsafe; cbn in Hstep.
    - (* Zero steps: it is a value already *)
      inversion Hstep; subst.
      specialize (Hsafe 1%nat). cbn in Hsafe.
      destruct Hsafe as [ Hsafe | Hsafe ].
      + destruct Hsafe as (?&?&Houtcome&?);
          unfold of_outcome in Houtcome; destruct v2;
          inversion Houtcome; eauto.
      + destruct Hsafe as (Hbase & Hsafe).
          destruct v2; inversion Hbase; inversion H.
    - (* At least one step *)
      inversion Hstep as [ | m ρ1 ρ2 ρ3 κ κs' Hstep' Hnsteps];
        clear Hstep; subst.
      destruct Hstep'; subst; inversion H; subst.
      destruct t1; inversion H2; subst; cbn in *; cycle 1.
      { (* absurd. *) destruct t1; cbn in H4; inversion H4. }

      destruct H1; subst.
      eapply IHn; first done.
      eapply invert_safe_step; eauto. }

  { (* [adequate_not_stuck]: the expression either steps or is a value *)
    intros * _ Hstep He2; subst.

    apply erased_steps_nsteps in Hstep.
    destruct Hstep as (n & κs & Hstep).

    (* How many steps did it take? *)
    revert e e2 σ κs t2 σ2 φ Hsafe Hstep He2.

    (* Induction on number of steps *)
    induction n; intros * H Hstep He2; cbn in Hstep.
    - (* Zero steps: it is a value already *)
      inversion Hstep; subst.
      specialize (H 1%nat). cbn in H.
      destruct H.
      (* Value *)
      + destruct H as (?&?&?&?); inversion H; subst.
        apply elem_of_list_singleton in He2; subst;
          constructor; eauto.
      + destruct H.
        apply elem_of_list_singleton in He2; subst.
        right; by apply can_step_reducible.

    - (* At least one step *)
      inversion Hstep; subst; clear Hstep.
      destruct H1; subst; inversion H0; subst.
      destruct t1; inversion H4; subst; cbn in *; cycle 1.
      { (* absurd. *) destruct t1; cbn in H6; inversion H6. }

      destruct H3; subst.
      eapply IHn; last done.
      eapply invert_safe_step; eauto. done. }
Qed.

(* Adequacy from [iris WP] implies the [safe] predicate. *)
Theorem adequate_safe {A X} (e : micro A X) σ φ :
  adequate NotStuck e σ (λ v _, ∃ x, v = Res x /\ φ x) ->
  safe (σ, e) (λ _ a, φ a).
Proof.
  intros * [] n.
  revert e σ φ adequate_result adequate_not_stuck.

  (* Induction on number of steps taken *)
  induction n; first done; cbn; intros. (* safety of no steps is trivial *)

  (* Duplicate information for inductive case on reducible expressions *)
  pose proof (adequate_not_stuck' := adequate_not_stuck).

  specialize
      (adequate_not_stuck _ _ e eq_refl (rtc_refl _ _)).
  assert (e ∈ [e]) by (apply elem_of_list_singleton; auto).
  specialize (adequate_not_stuck H); clear H.

  (* An expression is not stuck by either
        (1) being a value or (2) being reducible *)
  destruct adequate_not_stuck as [ Hval | Hred ]; cycle 1.

  { (* [Hred] Reducible expression *)
    right; split; [ by apply can_step_reducible | intros].
    destruct c'; eapply IHn; eauto.
    - intros; eauto. eapply adequate_result.
      eapply rtc_l; eauto.
      exists nil. eapply (step_atomic _ _ _ _ nil nil nil); try reflexivity.
      repeat red; eauto.
    - intros; eapply adequate_not_stuck'; eauto.
      eapply rtc_l; eauto.
      exists nil. eapply (step_atomic _ _ _ _ nil nil nil); try reflexivity.
      repeat red; eauto. }

  (* [Hval] Value *)
  inversion Hval; rename H into Hto_val.
  destruct x; cbn in Hto_val; unfold to_outcome in Hto_val;
  destruct e; inversion Hto_val; subst.
  { left; repeat eexists; eauto.
    specialize (adequate_result nil σ (Res r) (rtc_refl _ _)).
    destruct adequate_result as (?&?&?); inversion H; subst; auto. }
  { specialize (adequate_result nil σ (Exn e0) (rtc_refl _ _)).
    destruct adequate_result as (?&?&?); inversion H; subst; auto. }
Qed.

(* Statement of [adequate] (with postconditions on result values) and [safe]
   are logically equivalent. *)
Corollary adequate_safe_equiv {A X} (e : micro A X) σ φ :
  adequate NotStuck e σ (λ v _, ∃ x, v = Res x /\ φ x) <->
  safe (σ, e) (λ _ a, φ a).
Proof.
  split; intro;
    eauto using adequate_safe, safe_adequate_res.
Qed.
