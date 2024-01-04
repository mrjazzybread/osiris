Lemma ne_irreflexive {A} (x : A) : (x ≠ x) ↔ False.
Proof. tauto. Qed.

Lemma disj_False_left Q : False ∨ Q ↔ Q.
Proof. tauto. Qed.

Lemma disj_False_right Q : Q ∨ False ↔ Q.
Proof. tauto. Qed.

Ltac tauto_simp :=
  repeat rewrite ?ne_irreflexive, ?disj_False_left, ?disj_False_right.

(* This instance allows rewriting inside [ψ]. *)

Global Instance Proper_pat η p v φ :
  Proper (impl ==> impl) (pat η p v φ).
Proof.
  unfold Proper, respectful, impl. eauto using pat_consequence.
Qed.

Global Instance Proper_pat' η p v φ :
  Proper (iff ==> flip impl) (pat η p v φ).
    (* stronger than necessary, but seems useful; TODO *)
Proof.
  unfold Proper, respectful, flip, impl.
  intuition eauto using pat_consequence.
Qed.
