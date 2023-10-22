From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import micro.

(* This module fixes the specific set of codes that we need to write an
   interpreter for OCaml. *)

(* ------------------------------------------------------------------------ *)

(* [Eval (η, e)] is a request for the computation [eval η e]. *)

(* [Loop (η, x, i1, i2, e)] is a request for the computation
   [loop η x v1 v2 e]. *)

(* [Flip] is a request to flip a Boolean coin. *)

(* [Alloc], [Load], [Store] are requests to allocate, read, write a memory
   location in the heap. *)

Inductive code : Type → Type → Type :=
| CEval  : code (env * expr) val
| CLoop  : code (env * var * int * int * expr) val
| CFlip  : code unit bool
| CAlloc : code val loc
| CLoad  : code loc val
| CStore : code (loc * val) unit
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

(* ------------------------------------------------------------------------ *)

(* [flip] flips a coin. *)

Definition flip : micro bool :=
  stop CFlip ().

(* [choose m1 m2] is a non-deterministic choice between the
   computations [m1] and [m2]. *)

Definition choose {A} (m1 m2 : micro A) : micro A :=
  b ← flip ;
  if (b : bool) then m1 else m2.
