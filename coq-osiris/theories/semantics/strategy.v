From osiris Require Import base semantics.code.
(** Order of evaluation *)

(* The order of evaluation in OCaml is not always specified, for example in
function application, local definitions with the [and] keyword, or record
expressions. We implement this unspecified order with non-determinism. When
establishing the correctness of programs, we prove that every execution
theoretically allowed by the official specification is correct. However, when
testing our semantics, we limit non-determinism as much as possible, trying to
mimic existing OCaml implementations.

Another source of non-determinism in our semantics is whether assert expressions
are executed or ignored (with the [-noassert]) option, we handle this here as
well. *)



(* For list of sub-expressions, possibilities are: left to right, right to left,
and interleaving.

A fourth option could be an [Unspecified] order, that would ensure that e.g. in
[e1 + e2] either [e1] is run first then [e2] or [e2] first then [e1], instead of
allowing all the interleavings of the parallel strategy. This would restrict the
possible executions and allow us to prove more programs, such as [let r = ref 0
in let _ = (incr r, incr r) in assert (!r = 2)] which is incorrect using the
parallel strategy. For this one would need to change a few things in particular
n-ary application needs to be treated in a special way, and the semantics would
have more intermediate representations. *)

Variant direction := Left_to_right | Right_to_left | Interleave.



(* [micro] combinators similar to [par] that implement an evaluation order *)

Definition ltr {A1 A2 E} (m1 : micro A1 E) (m2 : micro A2 E) : micro (A1 * A2) E :=
  bind m1 (λ v1 : A1, bind m2 (λ v2 : A2, ret (v1, v2))).

Definition rtl {A1 A2 E} (m1 : micro A1 E) (m2 : micro A2 E) : micro (A1 * A2) E :=
  bind m2 (λ v2 : A2, bind m1 (λ v1 : A1, ret (v1, v2))).


(* Pair monadic operator, evaluating following a strategic direction *)

Definition pair_op (dir : direction) {A1 A2 E} : micro A1 E → micro A2 E → micro (A1 * A2) E :=
  match dir with
  | Left_to_right => ltr
  | Right_to_left => rtl
  | Interleave => par
  end.


(* Module type that packages different options and strategies *)

Variant maybe := Yes | No | Unspecified.

Module Type Strategy.
  (* Order of evaluation of the bodies in (local or not) definitions
     i.e. of [e1], ..., [en] in  [let p1 = e1 and ... and pn = en (in)] *)
  Parameter let_and_order : direction.

  (* Order of evaluation for function application e.g. in [e1 e2] or in
     [e1 + e2] *)
  Parameter fun_app_order : direction.

  (* Order of evaluation for tuples/constructor arguments e.g. in [(e1, e2,
  ...)] or in [Constr (e1, e2)] *)
  Parameter tuple_order : direction.

  (* Order of evaluation for [for] bounds i.e. of [e1], [e2] in
     [for _ = e1 (down)to e2 do _ done] *)
  Parameter for_bounds_order : direction.

  (* Option for asserts: are they run, ignored, or is it unspecified? *)
  Parameter run_asserts : maybe.
End Strategy.


(* Usual evaluation strategy: includes what ocaml{,c,opt} does. Note that it is
not completely deterministic. In particular:

- the order of evaluation of field expressions in record creation and updates is
  still [Interleave]. It is dependent the order of the fields in the record's
  definition, and we do not translate this information (yet); we think it is
  error-prone to rely on it.

- tuples, and EData/EXData arguments are still evaluated using [par] because
  even if it is most of the time right-to-left, it is sometimes left-to-right,
  like in [match e1, e2 with _, _ -> ...]:

    https://github.com/ocaml/ocaml/pull/12440

  which is further complicated because an exception/effect clause makes it
  right-to-left again:

    https://github.com/ocaml/ocaml/pull/12440#issuecomment-1657095485

  and in yet other cases the non-flambda ocamlopt can change the order:

    https://github.com/ocaml/ocaml/pull/12440#issuecomment-1656161139

  which also applies for EData/EXData arguments and not only for tuples. *)

Module UsualStrategy <: Strategy.
  Definition let_and_order := Left_to_right.
  Definition fun_app_order := Right_to_left.
  Definition tuple_order := Interleave.
  Definition for_bounds_order := Left_to_right.
  Definition run_asserts := Yes.
End UsualStrategy.

(* Liberal strategy: the safest option for proofs, i.e. the least specified *)

Module LiberalStrategy <: Strategy.
  Definition let_and_order := Interleave.
  Definition fun_app_order := Interleave.
  Definition tuple_order := Interleave.
  Definition for_bounds_order := Interleave.
  Definition run_asserts := Unspecified.
End LiberalStrategy.
