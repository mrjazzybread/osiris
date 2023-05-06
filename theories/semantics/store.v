From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

From osiris.lang Require Import lang.
From osiris.semantics Require Import locations.


(* TODO:
   - add the required lemmas so that the types declared below can remain opaque
     to the rest of the development.
   - declare the required instances of [ElemOf] and [Dom] so that the store can
     be seen "as a gmap" (whatever its future definitions might be). *)


(* -------------------------------------------------------------------------- *)
(* The following section defines the physical store *)

Section Store.
  Definition store : Type := gmap loc val.


  (* [store_ref] finds a fresh location to add to its argument.
   * It returns the fresh location and the updated store. *)
  Definition store_ref (s: store) (v: val) : loc * store :=
    let l := fresh_locs (dom s) in
    (l, <[l := v]>s).

  Lemma store_ref_dom (s: store) (v: val) :
    let '(l, s') := store_ref s v in
    dom s' = (dom s) ∪ {[ l ]} ∧ l ∉ dom s.
  Proof.
    split; first set_solver.
    apply fresh_locs_fresh.
  Qed.

  Global Instance val_inhabited: Inhabited val := populate (VTuple VNil).

End Store.

(*Global Opaque fresh_locs.
Global Opaque store.*)
