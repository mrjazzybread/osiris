From iris Require Import base_logic.lib.gen_heap.
Require Import free.

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

