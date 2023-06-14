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
