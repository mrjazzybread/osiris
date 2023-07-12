From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import simp capital_SIMP.

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
Arguments build η xs/.
Arguments lookup_name _ _/.

(* We do not want to unfold [val_as_bool] into a case analysis; that would
   be counter-productive. Note that [val_as_bool] is more problematic than
   [val_as_int] because integer values have their own tag [VInt], whereas
   Boolean values do not. [VBool] is just sugar, not a genuine tag. *)
Global Opaque val_as_bool.

(* semantics/eval.v *)
Arguments lookup_name !η !x : simpl nomatch.
Arguments concat !δ η : simpl nomatch.
Arguments remove !f !fvs : simpl nomatch.
Arguments update !fvs !fvs' : simpl nomatch.
Arguments extend δ !p v.
Arguments extends δ !ps !vs.
Arguments extendfs δ !fps !fvs.

(* -------------------------------------------------------------------------- *)

(* Fix integers. *)

Notation "'EInt' z" :=
  (EInt (z)%Z) (at level 0, only parsing).
Notation "'PInt' z" :=
  (PInt (z)%Z) (at level 0, only parsing).

(* -------------------------------------------------------------------------- *)

(* Opacity. *)

Global Opaque

  (* Evaluator functions. *)
  call
  ret_concat
  ret_dconcat
  eval

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

  (* Judgements. *)
  SIMP

.
