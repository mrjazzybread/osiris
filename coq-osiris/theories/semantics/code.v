From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import micro.

(* This module fixes the specific set of codes that we need to write an
   interpreter for OCaml. *)

(* ------------------------------------------------------------------------ *)

(* Evaluating an OCaml expression cannot raise a meta-level exception. *)

(* This will change once we model OCaml exceptions. *)

Definition void : Type := (∀ A, A).

(* ------------------------------------------------------------------------ *)

(* [Eval (η, e)] is a request for the computation [eval η e]. *)

(* [Loop (η, x, i1, i2, e)] is a request for the computation
   [loop η x v1 v2 e]. *)

(* [Alloc], [Load], [Store] are requests to allocate, read, write a memory
   location in the heap. *)

(* We used to have a [Flip] effect that would flip a Boolean coin. This has
   been removed and replaced with a primitive [Choose] construct in the
   [micro] monad. See [invert_stack_try_ret] in simplification.v for an
   explanation. *)

Inductive code : Type → Type → Type → Type :=
| CEval  : code (env * expr) val void
| CLoop  : code (env * var * int * int * expr) val void
| CAlloc : code val loc void
| CLoad  : code loc val void
| CStore : code (loc * val) unit void
.

(* ------------------------------------------------------------------------ *)

(* Instantiate the monad with this specific type of codes. *)

Module C.
  Definition code := code.
End C.
Include Make(C).

(* ------------------------------------------------------------------------ *)

(* The left-arrow notation, analogous to Haskell's do notation. *)

Notation "x ← y ; z" :=
  (bind y (λ x, z))
  (format "'[v' x  '←'  y ';' '/' z ']'").

Notation "' x ← y ; z" :=
  (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200,
  format "'[v' ' x  '←'  y ';' '/' z ']'").
