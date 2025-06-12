Require Export Coq.Program.Equality.
From stdpp Require Export base strings.
From osiris.logic Require Export void.

(* Logical tautologies. *)

Lemma share_common_conjunct (P Q Q' : Prop) :
  (P →      Q ↔ Q') →
  P ∧ Q  ↔  P ∧ Q'.
Proof.
  tauto.
Qed.

Lemma share_common_hypothesis {X} (Q Q' : X → Prop) :
  (∀ x,          Q x ↔ Q' x) →
  (∀ x, Q x)  ↔  (∀ x, Q' x).
Proof.
  firstorder.
Qed.

(* Rewriting rules that are used to simplify typical goals. *)

Lemma true_iff (P : Prop) :
  (true ↔ P) ↔ P.
Proof.
  simpl. tauto.
Qed.

Lemma false_iff (P : Prop) :
  (false ↔ P) ↔ ¬P.
Proof.
  simpl. tauto.
Qed.

(* Trivial facts about Booleans. *)

Lemma bool_neq b1 b2 :
  b1 ≠ b2 → b1 = negb b2.
Proof.
  destruct b1, b2; simpl; congruence.
Qed.

Lemma bool_neq_false b :
  b ≠ false → b = true.
Proof.
  destruct b; congruence.
Qed.

Lemma bool_neq_true b :
  b ≠ true → b = false.
Proof.
  destruct b; congruence.
Qed.

(* Various commonly useful tactics. *)

(* [destruct_string_eqb] looks for a string equality test [String.eqb c c'] in
   the goal and reasons by cases on the outcome of this test. This produces
   the hypothesis [c = c'] in the first subgoal and the hypothesis [c ≠ c'] in
   the second subgoal. *)

Ltac destruct_string_eqb :=
  match goal with |- context[String.eqb ?c ?c'] =>
    let Heq := fresh "Heq" in
    destruct (String.eqb c c') eqn:Heq;
    [ rewrite String.eqb_eq in Heq
    | rewrite String.eqb_neq in Heq ]
  end.

From Coq Require Import Logic.Classical_Prop.

Ltac eq_dep_inj :=
  repeat
    (match goal with
     | H : existT ?A ?x = existT ?A ?y |- _ =>
         apply Classical_Prop.EqdepTheory.inj_pair2 in H
     end; subst).

Ltac invdep H := inversion H; subst; eq_dep_inj.
