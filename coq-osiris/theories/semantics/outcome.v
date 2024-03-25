(* The outcome type for computations.

   The type [A] is the type of the result that a computation may return, while
   the type [E] is the type of the exception that a computation may throw. *)

(* When evaluating an OCaml expression, we often instantiate [A] with
   [val] and [E] with [exn]. However, this instantiation is not fixed; it
   is possible for a subcomputation to use another instantiation. *)

(* The type [outcome2 A E] represents the outcome of a computation: either
   a result of type [A], or an exception of type [E]. *)

Inductive outcome2 A E :=
  | O2Ret (a : A)
  | O2Throw (e : E).

Arguments O2Ret     {A E}.
Arguments O2Throw   {A E}.

(* ------------------------------------------------------------------------ *)

(* The type [outcome3 A E] also represents the outcome of a computation,
   but has three branches: an outcome is a result of type [A], an
   exception of type [E], or a pair of an effect and a continuation, whose
   types [eff] and [continuation] are fixed. *)

Inductive outcome3 eff continuation A E :=
  | O3Ret (a : A)
  | O3Throw (e : E)
  | O3Perform (e : eff) (k : continuation).

Arguments O3Ret     {eff continuation A E}.
Arguments O3Throw   {eff continuation A E}.
Arguments O3Perform {eff continuation A E}.

(* An [outcome2 A E] can always be injected as an [outcome3 A E]. *)

Definition outcome2_inject {eff continuation A X} (o : outcome2 A X)
  : outcome3 eff continuation A X :=
  match o with
  | O2Ret a => O3Ret a
  | O2Throw e => O3Throw e
  end.

(* ------------------------------------------------------------------------ *)

(* Auxiliary functions for [outcome2]. *)

(* [continue k a] applies the first arm of the two-armed handler [k]. *)

(* [discontinue k a] applies its second arm. *)

Definition continue {A E R} (k : outcome2 A E -> R) (a : A) : R :=
  k (O2Ret a).

Definition discontinue {A E R} (k : outcome2 A E -> R) (e : E) : R :=
  k (O2Throw e).

(* A pair of functions [f] and [h] out of [A] and [E] can be glued
   to obtain a single function [glue2 f h] out of [outcome2 A E].
   This is typically used to glue the "result" and "exception" arms
   of a two-armed handler. *)

Definition glue2 {A E R} (f : A -> R) (h : E -> R) : outcome2 A E -> R :=
  fun o => match o with O2Ret a => f a | O2Throw e => h e end.

(* TODO prove lemmas about composing [continue] and [discontinue]
   with [glue2]? *)
