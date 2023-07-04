From iris.proofmode Require Import classes proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp.


(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

Lemma tac_change_goal {Σ: gFunctors} Δ (P Q : iProp Σ) :
  (P ⊢ Q) →
  environments.envs_entails Δ P →
  environments.envs_entails Δ Q.
Proof.
  intros H Henv.
  eapply coq_tactics.tac_eval; last done.
  intros Q''; subst Q''. assumption.
Qed.

(* [lem] must be of the form (P -∗ Q). Thanks to the tactic notation it can be
   lemma whose forall quantifiers have been instantiated with [_]. *)
Ltac tac_change_goal lem :=
  simple notypeclasses refine (tac_change_goal _ _ _ lem _).
Tactic Notation "tac_change_goal" uconstr(lem) := (tac_change_goal lem).
