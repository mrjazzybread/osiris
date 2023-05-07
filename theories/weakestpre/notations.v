From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.
From osiris.semantics Require Import semantics.

(* ------------------------------------------------------------------------ *)

(* Store-related notations. *)

Notation "l ↦ v" :=
  (mapsto l (DfracOwn 1) v) (at level 20).

(* -------------------------------------------------------------------------- *)
(* Notations used to handle n-ary calls. *)
Notation "'WP'  'calln' f v1 v2 .. vn @ s ; E {{ ϕ }}" :=
  (wp s E (call f v1) (fun v => wp s E (call v v2) (.. (fun v =>  wp s E (call v vn) ϕ ) ..)))
    (only printing).



(* -------------------------------------------------------------------------- *)
(* Notations to hide some continuations.
Notation "'WP' Par m m' '...' @ s ; E {{ ϕ }}" :=
  (wp s E (Par m m' _ _) ϕ)
    (only printing). *)
