Require Export Coq.Program.Equality.
From stdpp Require Export base strings.

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
