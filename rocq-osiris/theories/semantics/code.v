From osiris Require Import base.
From osiris.lang Require Import locations thread_ids lang.
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


(* ------------------------------------------------------------------------ *)

(* In the definition of the type [code], which follows, every system
   call is allowed to throw an exception of type [exn]. Some system
   calls can indeed throw such an exception: this includes [CEval],
   [CLoop], [CPerf], [CContinue], and [CDiscontinue]. Some system
   calls, such as [CFlip], [CAlloc], [CAllocBlock], [CLoad], [CLoadBlock],
   [CExchange], and [CSetBlockTag], cannot throw an exception. Describing
   them with the type [exn], as opposed to [void], is a (convenient)
   over-approximation. *)

(* [Eval (η, e)] is a request for the computation [eval η e].
   The function [eval] is defined in eval.v.
   The result is a value (or an exception). *)

(* [Loop (η, x, i1, i2, e)] is a request for the computation
   [loop η x v1 v2 e].
   The function [loop] is defined in eval.v.
   The result is a value (or an exception). *)

(* [Flip] is a request to flip a Boolean coin. *)

(* [CAlloc v] is a request to allocate a fresh ref cell with initial value [v].
   The result is the location of the new cell. *)

(* [CAllocBlock ls] is a request to allocate a fresh block of memory whose
   fields are the ref cells at locations [ls], initially tagged as mutable.
   The result is a block pointer. *)

(* [CLoad l] is a request to read the value stored at the ref cell at [l].
   The result is the stored value. *)

(* [CLoadBlock l] is a request to read the contents of the block at [l].
   The result is a pair of the mutability tag and the list of ref cell locations. *)

(* [CExchange (l, v')] is a request to overwrite the ref cell at location [l]
   with the value [v'], returning the previously stored value. *)

(* [CSetBlockTag (l, t)] is a request to update the mutability tag of the
   block at [l] to [t]. The result is unit. *)

(* [CCAS (l, seen, v')] is a compare-and-set request. If the ref cell at [l]
   currently stores a value [v] that is physically equal to [seen], then [v]
   is overwritten with [v'] and [true] is returned; otherwise the cell is left
   unchanged and [false] is returned. Physical equality is only defined for
   locations and nullary constructors; the request fails for other argument
   types. *)

(* [CFAA (l, i)] is a fetch-and-add request. It reads the integer [j] stored
   at the ref cell at [l], atomically overwrites it with [i + j], and returns
   the old value [j]. The request fails if [l] does not contain an integer. *)

(* [CPerf e] is a request to perform a delimited control effect,
   carrying the value [e] as a payload.
   The result is a value (or an exception).
   Indeed, the value returned by [CPerf e],
   or the exception raised by [CPerf e],
   is determined by whomever decides to continue or discontinue
   the continuation that is captured when this effect is performed. *)

(* [CResume (l, o)] is a request to resume the continuation stored at
   address [l] with an outcome [o].
   Depending on the outcome, the continuation is either continued or
   discontinued.

   The result is a value (or an exception). *)

(* [CWrap (deep, k, η, bs)] retrieves the continuation stored at [k] and installs
    a handler around it at a new location.

    The handler is given by [bs] (list of branches), and is evaluated with
    the environment [η].  *)

(* [CFork (f, a) is a request to create a new thread, and to evaluate the
   application [f a] inside of it. *)

Inductive code : Type → Type → Type → Type :=
| CEval  : code (env * expr) val exn
| CLoop  : code (env * var * int * int * expr) val exn
| CFlip : code unit bool exn
| CAlloc : code val loc exn
| CAllocBlock : code (mut_tag * list loc) loc exn
| CLoad  : code loc val exn
| CLoadBlock : code loc (mut_tag * list loc) exn
| CExchange : code (loc * val) val exn
| CSetBlockTag : code (loc * mut_tag) unit exn
| CCAS : code (loc * val * val) val exn
| CFAA : code (loc * int) val exn
| CPerf  : code eff val exn
| CResume : code (cont * outcome2 val exn) val exn
| CWrap : code (bool * cont * env * handler) loc exn
| CFork : code (val * val) val exn
| CJoin : code thread val exn
.

Definition is_concurrent_code {v exn eff} (c : code v exn eff) : Prop :=
  match c with
  | CFork | CJoin => True
  | _ => False
  end.

Definition step_through_par_code {v exn eff} (c : code v exn eff) :=
  match c with
  | CPerf | CJoin | CFork => True
  | _ => False
  end.

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

(* The combinator [please_eval] is a request to evaluate the [e]. *)

Definition please_eval η e :=
  stop CEval (η, e).

(* ------------------------------------------------------------------------ *)

(* The computation [perform v] performs the effect [v]. *)

Definition perform (v : eff) : microvx :=
  stop CPerf v.

(* The computation [wrap η k bs] installs a handler [bs] for the continuation
  stored at [k], and returns a new location which stores this installation. *)

Definition wrap (k : cont) η bs : micro loc exn :=
  stop CWrap (true, k, η, bs).

Definition shallow_wrap k η bs : micro loc exn :=
  stop CWrap (false, k, η, bs).

Definition resume (l : cont) (o : outcome2 val exn) :=
  stop CResume (l, o).

(* [handle] is simplify defined as the [Handle] constructor. *)

Definition handle {A E} (m : micro C.val C.exn) (h : _ -> micro A E) :=
  Handle m h.

(* [load_block l] loads the locations stored in the block at location [l].
   [load_block] only crashes on a bad heap state — it never throws — so its
   error type is left polymorphic. *)

Definition load_block {E} (l : loc) : micro (mut_tag * list loc) E :=
  Stop CLoadBlock l (λ o,
    match o with
    | O2Ret r => Ret r
    | O2Throw _ => Crash
    end).

(* [exchange l v] updates the ref cell at location [l] with the value [v],
   and returns the previously stored value. *)

Definition exchange (l : loc) (v : val) :=
  stop CExchange (l, v).

(* [set_tag l t] updates the tag of a block to [t], and returns the location of the block. *)

Definition set_tag (l : loc) (t : mut_tag) :=
  stop CSetBlockTag (l, t).

(* [cas l seen v] updates the ref cell at location [l] with the value [v],
   only if that value currently contains [seen]. *)

Definition cas (l : loc) (seen : val) (v : val) :=
  stop CCAS (l, seen, v).

(* [faa l i] increments the integer stored in the ref cell at location [l]
   by [i], and returns the previously stored value (before incrementing). *)

Definition faa (l : loc) (i : int) :=
  stop CFAA (l, i).

(* ------------------------------------------------------------------------ *)

Definition fork (v1 v2 : val) :=
  stop CFork (v1, v2).

Definition join (t : thread) :=
  stop CJoin t.

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

(* [load l] loads the value stored at location [l].
   [load] only crashes on a bad heap state — it never throws — so its
   error type is left polymorphic. *)

Definition load {E} (l : loc) : micro val E :=
  Stop CLoad l (λ o,
    match o with
    | O2Ret v => Ret v
    | O2Throw _ => Crash
    end).

(* [loadn ls] loads multiple locations [ls], and returns the list of
   the stored valies. *)

Fixpoint loadn {E} (ls : list loc) : micro (list val) E :=
  match ls with
  | [] => ret []
  | l :: ls =>
      v ← load l ;
      vs ← loadn ls ;
      ret (v :: vs)
  end.

(* ------------------------------------------------------------------------ *)

(* [alloc v] allocates a new ref cell with initial value [v] and returns the
   ref cell's location. *)

Definition alloc (v : val) : micro loc exn :=
  stop CAlloc v.

(* [allocn n v] allocates [n] new ref cells with initial value [v] and
   returns the ref cells' locations. *)

Fixpoint allocn (vs : list val) : micro (list loc) exn :=
  match vs with
  | [] => ret []
  | v :: vs =>
      l ← alloc v ;
      ls ← allocn vs ;
      ret (l :: ls)
  end.

(* [alloc_block ls] allocates a new block that stores the list of locations [ls]
   and returns a pointer to it. *)

Definition alloc_block (t : mut_tag) (ls : list loc) : micro loc exn :=
  stop CAllocBlock (t, ls).

(* [store l v] updates the ref cell at location [l] with the value [v],
   and returns unit. *)

Definition store (l : loc) (v : val) :=
  _ ← exchange l v;
  ret VUnit.

(* ------------------------------------------------------------------------ *)

(* [flip] flips a coin. *)

Definition flip : micro bool exn :=
  stop CFlip ().

(* [choose m1 m2] performs a non-deterministic choice between [m1] and
   [m2] and runs the chosen computation, producing a single result. *)

Definition choose {A} (m1 m2 : micro A exn) : micro A exn :=
  b ← flip ; if (b : bool) then m1 else m2.

(* ------------------------------------------------------------------------ *)

(* The combinator [loop] is a request to evaluate the [e]. *)

Definition loop (η : env) (x : var) (i1 : int) (i2 : int) (e : expr) :=
  stop CLoop (η, x, i1, i2, e).


(* ------------------------------------------------------------------------ *)

(* [destruct_code] performs case analysis on a code that appears in
   the hypotheses. *)

Ltac destruct_code :=
  match goal with
  | c: C.code _ _ _ |- _ =>
      match goal with
      | h: is_concurrent_code c |- _ => destruct c; try contradiction h
      | h: step_through_par_code c |- _ => destruct c; try contradiction h
      | _ => destruct c
      end
  | c: code _ _ _ |- _ =>
      match goal with
      | h: is_concurrent_code c |- _ => destruct c; try contradiction h
      | h: step_through_par_code c |- _ => destruct c; try contradiction h
      | _ => destruct c
      end
  end.

(* ------------------------------------------------------------------------ *)

(* [LeibnizEquiv] instances for [val] and [outcome2]. *)

(* N.N.: We need to import [stepindex_finite] in order to enable finite
   step-indexing everywhere. TODO: see if we can instantiate [valO] without
   this import. *)
From iris.algebra Require Import ofe stepindex_finite.

(* N.B.: We need to turn off this [redundant canonical projection] warning;
  As of Coq 8.17.1, the typechecker believes that this instance is redundant
  with [boolO], although that is not the case. *)
Set Warnings "-redundant-canonical-projection".

Canonical Structure valO := leibnizO val.
Canonical Structure outcome2O := leibnizO (outcome2 val exn).
