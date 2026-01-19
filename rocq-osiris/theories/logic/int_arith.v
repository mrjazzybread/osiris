From stdpp Require Import numbers.

(* Some properties of integer arithmetic. *)

Local Open Scope Z_scope.

(* [Is_true] is implicit in these statements. Its type is [bool → Prop]. *)

Lemma Zeq_spec (x y : Z) :
  (x =? y) ↔ (x = y).
Proof.
  rewrite Is_true_true, Z.eqb_eq. tauto.
Qed.

Lemma Zne_spec (x y : Z) :
  negb (x =? y) ↔ x ≠ y.
Proof.
  rewrite negb_True, Zeq_spec. tauto.
Qed.

Lemma Zlt_spec (x y : Z) :
  (x <? y) ↔ (x < y).
Proof.
  rewrite Is_true_true, Zlt_is_lt_bool. tauto.
Qed.

Lemma Zle_spec (x y : Z) :
  negb (y <? x) ↔ x ≤ y.
Proof.
  rewrite negb_True, Zlt_spec. lia.
Qed.
