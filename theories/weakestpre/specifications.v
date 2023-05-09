From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics.

Class TC_change_goal `{!osirisGS_gen hlc Σ} (P Q: iProp Σ) Δ :=
      tc_change_goal : environments.envs_entails Δ P →
                       environments.envs_entails Δ Q.

Class pure_unary_spec `{!osirisGS_gen hlc Σ}
      {A B: Type} `{!Encode A} `{!Encode B}
      (f: val) (ff: A → B) :=
  spec:
    ∀ (b: A) s E (φ: val → iProp Σ),
      ▷ (φ  # (ff b)) -∗
      wp s E (call f #b) φ.

Global Instance tc_change_goal_unary_spec `{!osirisGS_gen hlc Σ}
       {A B} `{!Encode A} `{!Encode B}
           f (ff: A → B) `{!pure_unary_spec f ff}
           {Δ φ s E a} :
  TC_change_goal (▷ (φ  # (ff a))) (wp s E (call f #a) φ) Δ :=
  tac_change_goal
      Δ
      (▷ (φ  # (ff a))) (wp s E (call f #a) φ)
      (spec _ _ _ φ).

Global Instance tc_change_goal_unary_bool_bool `{!osirisGS_gen hlc Σ}
       (f: val) (ff: bool → bool) {a Δ φ s E}
       {p: pure_unary_spec f ff}
  : TC_change_goal (▷ (φ (VBool (ff a)))) (wp s E (call f (VBool a)) φ) Δ.
Proof.
  replace (VBool (ff a)) with #(ff a); last reflexivity.
  replace (VBool a) with #a; last reflexivity.
  intros H.
  apply tc_change_goal, H.
Qed.

Global Instance tc_change_goal_unary_Z_Z `{!osirisGS_gen hlc Σ}
       (f: val) (ff: Z → Z) {a Δ φ s E}
       {p: pure_unary_spec f ff}
  : TC_change_goal (▷ (φ (VInt (int.repr (ff a))))) (wp s E (call f (VInt (int.repr a))) φ) Δ.
Proof.
  replace (VInt (int.repr (ff a))) with #(ff a); last reflexivity.
  replace (VInt (int.repr a)) with #a; last reflexivity.
  intros H.
  apply tc_change_goal, H.
Qed.
