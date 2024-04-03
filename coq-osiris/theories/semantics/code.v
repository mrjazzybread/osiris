From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Export outcome micro.

(* This module fixes the specific set of codes that are needed in the Osiris
   project. We use the [micro] monad to define an interpreter for OCaml. We
   need codes that support divergence, global state (a heap), and delimited
   control effects. *)

(* ------------------------------------------------------------------------ *)

(* When an OCaml expression raises an exception or performs an effect,
   the exception or effect itself is an OCaml value. *)

Definition exn := val.
Definition eff := val.

(* A handler is a list of branches, where it can handle a pure, exceptional,
   or effectful computation. *)

Definition handler := list branch.

(* ------------------------------------------------------------------------ *)

(* In the definition of the type [code], which follows, every system
   call is allowed to throw an exception of type [exn]. Some system
   calls can indeed throw such an exception: this includes [CEval],
   [CLoop], [CPerform], [CContinue], and [CDiscontinue]. Some system
   calls, such as [CAlloc], [CLoad], and [CStore], cannot throw an
   exception. Describing them with the type [exn], as opposed to
   [void], is a (convenient) over-approximation. *)

(* [Eval (η, e)] is a request for the computation [eval η e].
   The function [eval] is defined in eval.v.
   The result is a value (or an exception). *)

(* [Loop (η, x, i1, i2, e)] is a request for the computation
   [loop η x v1 v2 e].
   The function [loop] is defined in eval.v.
   The result is a value (or an exception). *)

(* [Alloc v], [Load l], [Store (l, v)] are requests to allocate, read,
   and write a memory location in the heap.
   The result of [CAlloc v] is a memory location.
   The result of [Load l] is a value.
   The result of [CStore (l, v)] is unit. *)

(* [CPerform e] is a request to perform a delimited control effect,
   carrying the value [e] as a payload.
   The result is a value (or an exception).
   Indeed, the value returned by [CPerform e],
   or the exception raised by [CPerform e],
   is determined by whomever decides to continue or discontinue
   the continuation that is captured when this effect is performed. *)

(* [CResume (l, o)] is a request to resume the continuation stored at
   address [l] with an outcome [o].
   Depending on the outcome, the continuation is either continued or
   discontinued.

   The result is a value (or an exception). *)

(* [CInstall (deep, k, η, bs)] retrieves the continuation stored at [k] and installs
    a handler around it at a new location.

    The handler is given by [bs] (list of branches), and is evaluated with
    the environment [η].  *)

(* We used to have a [Flip] effect that would flip a Boolean coin. This has
   been removed and replaced with a primitive [Choose] construct in the
   [micro] monad. See [invert_stack_try_ret] in simplification.v for an
   explanation. *)

Inductive code : Type → Type → Type → Type :=
| CEval  : code (env * expr) val exn
| CLoop  : code (env * var * int * int * expr) val exn
| CAlloc : code val loc exn
| CLoad  : code loc val exn
| CStore : code (loc * val) unit exn
| CPerform  : code val val exn
| CResume : code (loc * outcome2 val exn) val exn
| CInstall : code (bool * loc * env * handler) loc exn
.

(* ------------------------------------------------------------------------ *)

(* Instantiate the monad with this specific type of codes. *)

Module C.
  Definition code := code.
  Definition val := val.
  Definition exn := exn.
  Definition eff := eff.
  Definition continuation := loc.
End C.
Include Make(C).

(* The computational behavior of an OCaml expression is represented in
   Coq by a computation of type [micro val exn]. We use [microvx] as a
   short-hand for this type. *)

Notation microvx :=
  (micro val exn).

(* ------------------------------------------------------------------------ *)

(* The computation [perform v] performs the effect [v]. *)

Definition perform (v : eff) : microvx :=
  stop CPerform v.

(* The computation [install η k bs] installs a handler [bs] for the continuation
  stored at [k], and returns a new location which stores this installation. *)

Definition install deep k η bs : micro loc exn :=
  stop CInstall (deep, k, η, bs).

(* ------------------------------------------------------------------------ *)

(* The left-arrow notation, analogous to Haskell's do notation. *)

Notation "x ← y ; z" :=
  (bind y (λ x, z))
  (format "'[v' x  '←'  y ';' '/' z ']'").

Notation "' x ← y ; z" :=
  (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "'[v' ' x  '←'  y ';' '/' z ']'").

(* ------------------------------------------------------------------------ *)

(* [destruct_code] performs case analysis on a code that appears in
   the hypotheses. *)

Ltac destruct_code :=
  match goal with c: C.code _ _ _ |- _ => destruct c end.
