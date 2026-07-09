From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

Section EmptyCreate.

Variable V : Type.
Variable EqV : EqDecision V.
Variable CountableV : Countable V.

(* The empty relation: no edges. *)

Definition empty : relation V := fun _ _ => False.

(* -------------------------------------------------------------------------- *)

(* In an empty graph, every vertex is its own representative. *)

Instance is_repr_empty (x : V) :
  Repr empty x x.
Proof.
  split.
  - apply rtc_refl.
  - constructor. intros y Hy. exact Hy.
Qed.

(* The empty relation is a disjoint set forest. *)

Instance is_dsf_empty :
  DSF empty (∅ : gset V).
Proof.
  split.
  - constructor. intros x y [].
  - constructor. intros x y1 y2 [] [].
  - constructor. intros x. exists x. apply is_repr_empty.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [F] is a disjoint set forest with respect to some domain [D1], then it
   is also a disjoint set forest with respect to a larger domain [D2]. In
   other words, introducing new isolated vertices preserves the validity of
   a forest. *)

Lemma is_dsf_covariant_in_D (D1 D2 : gset V) F :
  DSF F D1 ->
  D1 ⊆ D2 ->
  DSF F D2.
Proof.
  intros [Hconf Hfunc Hdef] Hsub.
  constructor.
  - constructor. intros x y HF.
    destruct (confined x y HF) as [Hx Hy].
    split; eapply elem_of_subseteq; eauto.
  - exact Hfunc.
  - exact Hdef.
Qed.

(* -------------------------------------------------------------------------- *)

(* In particular, adding a single isolated vertex is permitted.

   (We drop the original's [dsf_per_create], which characterizes how
   [dsf_per] changes after [create] via TLC's [per_add_node]/[per_single];
   it isn't needed by UnionFind.v's [Inv_make], which only needs [is_dsf]
   preservation, and we haven't ported those PER combinators.) *)

Lemma is_dsf_create (D : gset V) (x : V) (F : relation V) :
  DSF F D ->
  DSF F (D ∪ {[x]}).
Proof.
  intros Hdsf.
  eapply is_dsf_covariant_in_D; eauto.
  set_solver.
Qed.

End EmptyCreate.
