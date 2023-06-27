From osiris Require Import base.
From osiris.lang Require Import lang.

(* This file defines a tactic that is supposed to prove equality goals. *)

Global Hint Extern 1 (_ = _) => congruence : equality.
Global Hint Extern 1 (_ = _) => f_equal : equality.
Global Hint Extern 1 (_ = _) => lia : equality.
Global Hint Extern 1 (_ = _) => rewrite Nat2Z.inj_succ : equality.

Global Hint Extern 1 (_ = _) => rewrite neg_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite add_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite sub_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite mul_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite divs_repr_repr by representable : equality.
Global Hint Extern 1 (_ = _) => rewrite mods_repr_repr by representable : equality.
Global Hint Extern 1 (_ = _) => rewrite eq_repr_repr by representable : equality.
Global Hint Extern 1 (_ = _) => rewrite lt_repr_repr by representable : equality.

Lemma prove_VBool_true_eq_VTrue b :
  b = true →
  VBool b = VTrue.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma prove_VBool_false_eq_VFalse b :
  b = false →
  VBool b = VFalse.
Proof.
  intros. subst. reflexivity.
Qed.

Global Hint Resolve
  prove_VBool_true_eq_VTrue
  prove_VBool_false_eq_VFalse
: equality.

Ltac equality :=
  eauto 3 with equality.

(* --------------------------------------------------------------------------*)

(* Unit tests. *)

(* TODO add more tests; ensure some form of test coverage *)

Goal   VBool (eq (add (repr 0) (repr 1)) (repr 1)) = VTrue.
Proof. equality. Qed.
