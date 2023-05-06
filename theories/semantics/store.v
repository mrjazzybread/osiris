From stdpp Require Import countable numbers gmap.
From iris.prelude Require Import prelude options.
From osiris.lang Require Import locations lang.

(* This file defines the physical store. *)

(* The store is a map of locations to values. *)

Definition store : Type := gmap loc val.

(* [store_ref] finds a fresh location to add to its argument.
 * It returns the fresh location and the updated store. *)
Definition store_ref (s: store) (v: val) : loc * store :=
  let l := fresh_loc (dom s) in
  (l, <[l := v]>s).

Lemma store_ref_dom (s: store) (v: val) :
  let '(l, s') := store_ref s v in
  dom s' = (dom s) ∪ {[ l ]} ∧ l ∉ dom s.
Proof.
  split; first set_solver.
  apply fresh_loc_fresh.
Qed.
