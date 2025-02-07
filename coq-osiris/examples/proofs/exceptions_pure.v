(* This file is a "pure mode" version of exceptions.v, to guide the
  generalization of lemmas about [pure] to non-trivial exceptional postconditions,
  but one should be aware that the current version of exceptions.v is old and
  should not be considered idiomatic (for this see iter.v instead).

TODO: avoid [simp] at least when [eval ...] does not reduce to a value / exn *)

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_exception.

Definition stdlib_with_notfound :=
  ("Not_found", (VLoc (Loc 0))) :: stdlib_env.

(* Calling [head #l] either returns [#h] when [l = h :: t],
   or throws an exception when [l = []]. *)

Definition head_spec head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    pure
      (call head #l)
      (λ h : A, exists t, l = h :: t)
      (λ e, e = VXData (Loc 0) [] ∧ l = []).

(* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
   or returns [None] when [l = []]. *)

Definition catch_head_spec catch_head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
   pure
      (call catch_head #l)
      (λ hopt, hopt = list.head l) ⊥.

Lemma Head_spec :
  pure (eval stdlib_with_notfound (EAnonFun __fun1)) head_spec ⊥.
Proof.
  pure_simp. unfold head_spec; intros.

  (* in both cases, the expr [simp]lifies to a value or exception *)
  destruct l.
  - eapply pure_wp_simp; first by simp_really. apply pure_wp_throw.
    split; eauto.
  - pure_simp.
Qed.

Lemma Catch_head_spec head :
  head_spec head ->
  pure
    (eval (("head", head) :: stdlib_with_notfound)
       (EAnonFun __fun3)) catch_head_spec bottom.
Proof.
  intros Hhead.
  pure_simp; unfold catch_head_spec; intros.
  pure_enter.
  eapply pure_eval_match'_exn.
  - eapply pure_simp. simp. apply Hhead.
  - intros h (t & ->). pure_simp.
  - intros e (-> & ->). pure_simp.
Qed.

Lemma Catch_head2_spec head chead:
  head_spec head ->
  (* FIXME *)
  pure
    (eval (("catch_head", chead) :: ("head", head) ::
      stdlib_with_notfound)
       (EAnonFun __fun5)) catch_head_spec bottom.
Proof.
  intros Hhead.
  pure_simp; unfold catch_head_spec.
  intros. pure_enter.
  (* FIXME: This proof was not so pretty to begin with; but
    we can do better here.

    FIXME: Temporary proof for now; need to repair [pure_tactics]. *)
  (* TODO: Refactor. *)
  eapply (pure_eval_trywith _ _ _ _ (λ ex, l = [] ∧ ex = VXData (Loc 0) [])).
  - (* matched value (or exn) *)
    eapply pure_eval_data; last done. (* TODO Fix [pure_data] tactic. *)
    eapply pure_ret_mono.
    { eapply pure_evals.
      apply Forall2_cons; split; last eapply Forall2_nil; eauto.
      (* Application *)
      eapply pure_eval_app.
      pure_path. pure_path.
      intros * -> -> ; eauto.
      eapply pure_exn_mono; first eapply Hhead.
      intros ? (?&?); eauto. }
    { intros.
      apply Forall2_cons_inv_l in H0.
      destruct H0 as (?&?&?&?&?); subst.
      cbn in *. destruct H0.
      apply Forall2_nil_inv_l in H1; subst.
      by cbn. }
  - intros * (?&?); subst.
    apply pure_eval_try_with_cons, pat_PXData_eq; auto.
    ltac2: (patterns ()). pure_data. cbn.
    exists (nil : list A); eauto. Unshelve. eauto.
Qed.

Lemma exceptions_pure__spec:
  eval_module stdlib_with_notfound __main (λ η, True).
Proof.
  apply module_struct.
  next_item with head_spec.
  { by apply Head_spec. }

  intros [??] (head & Hhead & -> & ->).
  next_item with catch_head_spec.
  { by apply Catch_head_spec. }

  intros [??] (chead & Hchead & -> & ->).
  next_item with catch_head_spec.
  { by apply Catch_head2_spec. }

<<<<<<< variant A
  (* Struct item: [let catch_head l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    pure_enter.
    eapply pure_eval_match'_exn.
    - eapply pure_simp. simp. apply Hhead.
    - intros h (t & ->). pure_simp. reflexivity.
    - intros e (-> & ->). pure_simp. reflexivity.  }
  intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

  (* Struct item: [let catch_head2 l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    pure_enter.
    (* FIXME: This proof was not so pretty to begin with; but
     we can do better here. *)
    (* TODO: Refactor. *)
    eapply pure_eval_match'_exn with (φ' := λ a, a = #(list.head l)) (ζ := λ e, l = [] ∧ e = VXData (Loc 0) []).
    { eapply pure_eval_data'; last done.
      simpl_evals. fold eval. eapply pure_wp_Par_conseq.
      + eapply pure_eval_app. pure_path. pure_path.
      + eapply pure_wp_ret_singleton.
      + intros; returns_eauto. cbn in *.
        eapply pure_wp_ret; subst. destruct Ha_ensures; subst.
        red in H1; subst.
        exists [v]; tauto.
      + intros ? [ (-> & ->)| ]; cbn.
        * eapply pure_wp_throw; eauto.
        * Unshelve.
          2 : { apply (λ e, l = [] ∧ e = VXData (Loc 0) []). }
          eapply pure_wp_throw; eauto. }
    { intros ? ->.
      pure_match.
      pure_path. }
    { intros ? [-> ->]. pure_match. pure_data. encode. } }

>>>>>>> variant B
======= end
  intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

  (* We have gone though all of the struct items, time to conclude. *)
  by eapply structs_nil.
Qed.
