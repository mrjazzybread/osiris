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
Global Hint Extern 1 (_ = _) => rewrite divs_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite mods_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite eq_repr_repr : equality.
Global Hint Extern 1 (_ = _) => rewrite lt_repr_repr : equality.

Ltac equality :=
  eauto with equality.
