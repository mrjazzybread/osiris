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

Lemma is_repr_empty :
  forall x, is_repr V empty x x.
Proof.
  intros x. split.
  - apply rtc_refl.
  - intros y Hy. exact Hy.
Qed.

(* The empty relation is a disjoint set forest. *)

Lemma is_dsf_empty :
  is_dsf V EqV CountableV (∅ : gset V) empty.
Proof.
  unfold is_dsf. split; [|split].
  - intros x y [].
  - intros x y1 y2 [] [].
  - intros x. exists x. apply is_repr_empty.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [F] is a disjoint set forest with respect to some domain [D1], then it
   is also a disjoint set forest with respect to a larger domain [D2]. In
   other words, introducing new isolated vertices preserves the validity of
   a forest. *)

Lemma is_dsf_covariant_in_D :
  forall (D1 D2 : gset V) F,
  is_dsf V EqV CountableV D1 F ->
  D1 ⊆ D2 ->
  is_dsf V EqV CountableV D2 F.
Proof.
  intros D1 D2 F [Hconf [Hfunc Hdef]] Hsub.
  split; [|split].
  - intros x y HF. destruct (Hconf x y HF) as [Hx Hy].
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

Lemma is_dsf_create :
  forall (D : gset V) x F,
  is_dsf V EqV CountableV D F ->
  is_dsf V EqV CountableV (D ∪ {[x]}) F.
Proof.
  intros D x F Hdsf.
  eapply is_dsf_covariant_in_D; eauto.
  set_solver.
Qed.

End EmptyCreate.
