From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import weakestpre.
From osiris.proofmode Require Import simp.

(* -------------------------------------------------------------------------- *)

(* On reduction. *)

(* Prevent simplifying string comparisons unless both arguments are known. *)
Arguments String.eqb !s1 !s2 : simpl nomatch.

(* Unfold [as_bool] and friends as soon as they are applied to an argument.
   This exposes a [bind] combinator and enables further simplifications. *)
Arguments as_bool m /.
Arguments as_int m /.
Arguments as_loc m /.
Arguments as_record m /.
Arguments as_struct m /.

(* semantics/eval.v *)
Global Arguments lookup_name !η !x : simpl nomatch.
Global Arguments concat !δ η : simpl nomatch.
Global Arguments remove !f !fvs : simpl nomatch.
Global Arguments update !fvs !fvs' : simpl nomatch.
Global Arguments extend δ !p v.
Global Arguments extends δ !ps !vs.
Global Arguments extendfs δ !fps !fvs.

(* -------------------------------------------------------------------------- *)

(* Fix integers. *)

Global Notation "'EInt' z" :=
  (EInt (z)%Z) (at level 0, only parsing).
Global Notation "'PInt' z" :=
  (PInt (z)%Z) (at level 0, only parsing).

(* -------------------------------------------------------------------------- *)

(* Opacity. *)

Global Opaque
       call
       ret_concat
       ret_dconcat
       stuck
       eval
       SIMP
       stuck
       int.signed int.repr int.add int.mul
       assertion_failure
       division_by_zero
       length_mismatch
       match_failure
       missing_field
       missing_variable
       missing_variable_or_field
       structural_equality_error
       structural_ordering_error
       type_mismatch
       SIMP
.
