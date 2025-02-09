From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import specifications.

(* -------------------------------------------------------------------------- *)

(* On reduction. *)

(* Prevent simplifying string comparisons unless both arguments are known. *)
Arguments String.eqb !s1 !s2 : simpl nomatch.
Arguments satisfies_spec : simpl never.

(* Encourage simplifying [continue] and [discontinue], which can often block
   symbolic execution. *)
Arguments continue _ _ _ k a /.
Arguments discontinue _ _ _ k e /.


(* Unfold [as_bool] and friends as soon as they are applied to an argument.
   This exposes a [bind] combinator and enables further simplifications. *)
Arguments as_bool m /.
Arguments as_int m /.
Arguments as_loc E m /.
Arguments as_record m /.
Arguments as_struct E m /.
Arguments lookup_name _ _/.

Arguments val_as_bool !v /.
Arguments val_as_loc _ !v /.
Arguments val_as_cont _ !v /.
Arguments val_as_int !v /.
Arguments val_as_record !v /.
Arguments val_as_struct !v /.

(* semantics/eval.v *)
Arguments lookup_name !η !x : simpl nomatch.
Arguments eval.remove !f !fvs : simpl nomatch. (* FIXME *)
Arguments update !fvs !fvs' : simpl nomatch.
Arguments extend η δ !p v.
Arguments extends η δ !ps !vs.
Arguments extendfs η δ !fps !fvs.
Arguments eval η !e /.
Arguments evals η !es /.
Arguments evalfs η !fes /.
Arguments shallow_match η o !bs all_bs.
Arguments deep_match η !o bs.
Arguments deep_match_go η o !bs /.
Arguments eval_bindings η !bs /.
Arguments eval_mexpr η !me /.
Arguments eval_sitem ηδ !item /.
Arguments eval_sitems ηδ !sitems / : rename.

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
  (* eval *)
  (* evals *)
  (* eval_match *)
  (* eval_sitem *)
  (* eval_sitems *)
  (* eval_bindings *)
  (* extend *)
  (* extends *)
  (* eval_mexpr *)
  (* coerce *)

  encode

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
