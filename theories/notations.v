From iris Require Import base_logic.lib.gen_heap.
Require Import free lang.

(* ------------------------------------------------------------------------ *)

(* The left-arrow notation, analogous to Haskell's do notation. *)

Notation "x ← y ; z" :=
  (bind y (λ x, z)).

Notation "' x ← y ; z" :=
  (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200).


(* ------------------------------------------------------------------------ *)

(* Store-related notations *)

Notation "l ↦ v" := (mapsto l (DfracOwn 1) v) (at level 20).


(* ------------------------------------------------------------------------ *)

(* Expression-related notations to make the expressions user-friendly. *)

Notation "'λ' x '→' e" := (EFun x e) (at level 20, only printing).
Notation "'let:' x 'in' e" := (ELet x e) (at level 20, only printing).
Notation "bv ':b:' bvs" := (BiCons bv bvs) (at level 20, only printing).
Notation "bv '.'" := (BiCons bv BiNil) (at level 20, only printing).
Notation "patt '~>' v" := (Binding patt v) (at level 20, only printing).
Notation "x" := (PVar x) (at level 19, only printing).
Notation "x" := (EVar x) (at level 19, only printing).
Notation "x '+I' y " := (EIntAdd x y) (at level 20, only printing).

