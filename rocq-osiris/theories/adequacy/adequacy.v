From iris.program_logic Require Import adequacy.
From osiris.pure_logic Require Import wp.

(* Requires ewp.v because it contains the iris instance of the language. If this
creates a dependency cycle, we can move the pure adequacy results to
program_logic/adequacy.v or move the language instance to e.g.
lang/iris_instance.v *)
From osiris.program_logic Require Import ewp.
From osiris.program_logic Require Import subjective_step.

Lemma pure_wp_steps {A E} (c c' : config A E) φ ψ :
  rtc step c c' → pure_wp c.2 φ ψ → c'.1 = c.1 ∧ pure_wp c'.2 φ ψ.
Proof.
  induction 1 as [ | (σ, m) (σ', m') c S Ss IHr]; auto.
  intros P.
  destruct (pure_wp_preservation P S) as [P' ->].
  auto.
Qed.

(** Adequacy for partial correctness *)

Theorem pure_wp_adequacy {A E} (m : micro A E) φ Ψ :
  pure_wp m φ Ψ →
  ∀ σ σ' m',
    rtc step (σ, m) (σ', m') →
    (∃ o, outcome2_opt m' = Some o ∧ glue2 φ Ψ o) ∨ can_step (σ', m').
Proof.
  intros P.
  intros σ σ' m' S.
  destruct (pure_wp_steps _ _ _ _ S P) as [Heq P']. simpl in *; subst.
  case (outcome2_opt m') eqn:Houtcome.
  - left; exists o.
    split; first reflexivity.
    destruct m'; inversion Houtcome.
    + by eapply invert_pure_wp_ret in P'.
    + by eapply invert_pure_wp_throw in P'.
  - right.
    destruct m'.
    + inversion Houtcome.
    + inversion Houtcome.
    + by eapply invert_pure_wp_crash in P'.
    + apply can_step_handle.
    + apply can_step_stop.
      apply invert_pure_wp_stop in P'. destruct c; auto.
    + apply can_step_par.
Qed.

(* Special case with no exception allowed *)

Theorem pure_wp_adequacy_ret {A E} (m : micro A E) φ :
  pure_wp m φ ⊥ →
  ∀ σ σ' m',
    rtc step (σ, m) (σ', m') →
    (∃ v, outcome2_opt m' = Some (O2Ret v) ∧ φ v) ∨ can_step (σ', m').
Proof.
  intros P.
  intros σ σ' m' S.
  pose proof (pure_wp_adequacy m φ ⊥ P σ σ' m' S) as Hadequate.
  destruct Hadequate as [ (o & -> & Hpost) | Hcanstep ].
  - left.
    destruct o; try contradiction Hpost.
    eexists; split; [ reflexivity | apply Hpost ].
  - right. apply Hcanstep.
Qed.

(** Termination *)

Theorem pure_wp_terminates {A E} (m : micro A E) σ φ ψ :
  pure_wp m φ ψ → sn step (σ, m).
Proof.
  intros P; generalize P.
  induction 1; constructor; intros (σ', m') S.
  - inversion S.
  - inversion S.
  - destruct (pure_wp_step_may P S) as [M ->]. auto.
Qed.
