From iris.program_logic Require Import adequacy.
From osiris.program_logic.pure Require Import wp.

(* Requires ewp.v because it contains the iris instance of the language. If this
creates a dependency cycle, we can move the pure adequacy results to
program_logic/adequacy.v or move the language instance to e.g.
lang/iris_instance.v *)
From osiris.program_logic Require Import ewp.


(* Adequacy is an easy consequence of [wp.v]'s preservation. Still, we state it
here the same way as it is done for usual iris developments. *)

Lemma invert_erased_step {A E} (m : micro A E) σ c' :
  erased_step ([m], σ) c' → (∃ σ' m', c' = ([m'], σ') ∧ step (σ, m) (σ', m')).
Proof.
  inversion 1 as [tr S].
  inversion S as [e1 σ1 e2 σ2 efs t1 t2 [=Heq1 <-] -> S'].
  inversion S' as [S'' ->].
  apply eq_sym, app_singleton in Heq1.
  destruct Heq1 as [ [-> Heq1] | [? [=]]].
  destruct t2; [ | congruence]. injection Heq1 as ->.
  eauto.
Qed.

Lemma invert_rtc_erased_step {A E} (m : micro A E) σ c' :
  rtc erased_step ([m], σ) c' → (∃ σ' m', c' = ([m'], σ') ∧ rtc step (σ, m) (σ', m')).
Proof.
  intros S.
  remember ([m], σ) as c.
  revert m σ Heqc.
  induction S as [c | c c' c'' S Ss IH]; intros m σ ->.
  - eexists _, _; repeat constructor.
  - apply invert_erased_step in S.
    destruct S as (σ' & m' & -> & S).
    destruct (IH _ _ eq_refl) as (σ'' & m'' & -> & S').
    eexists σ'', m''. split; auto. econstructor; eauto.
Qed.

Lemma pure_wp_steps {A E} (c c' : config A E) φ ψ :
  rtc step c c' → pure_wp c.2 φ ψ → c'.1 = c.1 ∧ pure_wp c'.2 φ ψ.
Proof.
  induction 1 as [ | (σ, m) (σ', m') c S Ss IHr]; auto.
  intros P.
  destruct (pure_wp_preservation P S) as [P' ->].
  auto.
Qed.

Lemma can_step_reducible {A E} σ (m : micro A E) :
  can_step (σ, m) → reducible m σ.
Proof.
  intros ((σ', m'), S).
  eexists [], m', σ', []; constructor; auto.
Qed.


(** Adequacy for partial correctness *)

Theorem pure_wp_adequacy {A E} (m : micro A E) φ ψ σ :
  pure_wp m φ ψ → adequate NotStuck m σ (λ o σ', σ' = σ ∧ glue2 φ ψ o).
Proof.
  intros P.
  apply adequate_alt.
  intros _tr _σ (σ' & m' & [=->->] & S)%invert_rtc_erased_step.
  destruct (pure_wp_steps _ _ _ _ S P) as [Heq P']. simpl in *; subst.
  split.
  - intros [a | e] [ | ]; try discriminate; injection 1 as ->.
    + by eapply invert_pure_wp_ret in P'.
    + by eapply invert_pure_wp_throw in P'.
  - intros _ _ ->%elem_of_list_singleton.
    destruct m'.
    + left; eauto.
    + left; eauto.
    + by eapply invert_pure_wp_crash in P'.
    + right. apply can_step_reducible, can_step_handle.
    + right. apply can_step_reducible, can_step_stop.
      apply invert_pure_wp_stop in P'. destruct c; auto.
    + right. apply can_step_reducible, can_step_par.
Qed.

(* Special case with no exception allowed *)

Theorem pure_wp_adequacy_ret {A E} (m : micro A E) φ σ :
  pure_wp m φ ⊥ → adequate NotStuck m σ (λ o σ', ∃ a, o = O2Ret a ∧ σ' = σ ∧ φ a).
Proof.
  intros P.
  apply adequate_alt.
  intros _tr _σ (σ' & m' & [=->->] & S)%invert_rtc_erased_step.
  destruct (pure_wp_steps _ _ _ _ S P) as [Heq P']. simpl in *; subst.
  split.
  - intros [a | e] [ | ]; try discriminate; injection 1 as ->.
    + eexists; split; eauto. by eapply invert_pure_wp_ret in P'.
    + by eapply invert_pure_wp_throw in P'.
  - intros _ _ ->%elem_of_list_singleton.
    destruct m'.
    + left; eauto.
    + left; eauto.
    + by eapply invert_pure_wp_crash in P'.
    + right. apply can_step_reducible, can_step_handle.
    + right. apply can_step_reducible, can_step_stop.
      apply invert_pure_wp_stop in P'. destruct c; auto.
    + right. apply can_step_reducible, can_step_par.
Qed.


(** Termination *)

Theorem pure_wp_terminates {A E} (m : micro A E) σ φ ψ :
  pure_wp m φ ψ → sn erased_step ([m], σ).
Proof.
  intros P; generalize P.
  induction 1; constructor; intros _ (σ' & m' & -> & S)%invert_erased_step.
  - inversion S.
  - inversion S.
  - destruct (pure_wp_step_may P S) as [M ->]. auto.
Qed.
