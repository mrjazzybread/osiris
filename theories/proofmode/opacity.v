From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import weakestpre.
From osiris.proofmode Require Import simp.

(* Prevent simplifying string comparisons unless both arguments are known. *)
Arguments String.eqb !s1 !s2 : simpl nomatch.

(* Unfold [as_bool] and friends as soon as they are applied to an argument.
   This exposes a [bind] combinator and enables further simplifications. *)
Arguments as_bool m /.
Arguments as_int m /.
Arguments as_loc m /.
Arguments as_record m /.
Arguments as_struct m /.

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
.
