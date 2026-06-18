From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

(* The union of two separate disjoint set forests is again a disjoint set
   forest. This is obvious, of course, but takes some work.

   This is a scoped-down port: we only keep what UnionFind.v's [UF_join]
   needs ([is_dsf_join], [is_repr_join_direct_1], [is_repr_join_direct_2]),
   dropping [descendants_join_1]/[descendants_join_2] (needed only for the
   amortized-complexity analysis) and the unnamed anonymous [Goal] (not used
   anywhere). We also restate the relation-level equalities ([path_join],
   [edge_union_inversion_*]) pointwise as [<->] rather than as propositional
   equalities of functions/relations, to avoid needing functional
   extensionality, consistently with the rest of this port. *)

Section Join.

Variable V : Type.
Variable EqV : EqDecision V.
Variable CountableV : Countable V.
Variable D1 D2 : gset V.
Variable F1 F2 : relation V.

Hypothesis disjointness : D1 ## D2.
Hypothesis hdsf1 : is_dsf V EqV CountableV D1 F1.
Hypothesis hdsf2 : is_dsf V EqV CountableV D2 F2.

Definition union : relation V := fun x y => F1 x y \/ F2 x y.

(* If [x] is in [D1], then its [union]-edges are exactly its [F1]-edges. *)

Lemma edge_union_inversion_1:
  forall x, x ∈ D1 -> forall y, union x y <-> F1 x y.
Proof.
  intros x HxD1 y. split.
  - intros [HF1 | HF2]; [exact HF1|].
    exfalso. destruct (proj1 hdsf2 x y HF2) as [Hx2 _]. set_solver.
  - intros HF1. left. exact HF1.
Qed.

Lemma edge_union_inversion_2:
  forall x, x ∈ D2 -> forall y, union x y <-> F2 x y.
Proof.
  intros x HxD2 y. split.
  - intros [HF1 | HF2]; [|exact HF2].
    exfalso. destruct (proj1 hdsf1 x y HF1) as [Hx1 _]. set_solver.
  - intros HF2. right. exact HF2.
Qed.

(* Every [F1]-path (resp. [F2]-path) is a [union]-path. *)

Lemma path_union_of_1:
  forall x y, rtc F1 x y -> rtc union x y.
Proof.
  intros x y Hpath. induction Hpath as [x|x x' y HF1 Hpath IH].
  - apply rtc_refl.
  - eapply rtc_l; [left; exact HF1 | exact IH].
Qed.

Lemma path_union_of_2:
  forall x y, rtc F2 x y -> rtc union x y.
Proof.
  intros x y Hpath. induction Hpath as [x|x x' y HF2 Hpath IH].
  - apply rtc_refl.
  - eapply rtc_l; [right; exact HF2 | exact IH].
Qed.

(* Every [union]-path out of a point of [D1] is an [F1]-path; symmetrically
   for [D2]. *)

Lemma path_union_inversion_left:
  forall x y, rtc union x y -> x ∈ D1 -> rtc F1 x y.
Proof.
  intros x y Hpath. induction Hpath as [x|x x' y Hu Hpath IH]; intros HxD1.
  - apply rtc_refl.
  - assert (HF1 : F1 x x').
    { destruct Hu as [HF1 | HF2]; [exact HF1|].
      exfalso. destruct (proj1 hdsf2 x x' HF2) as [Hx2 _]. set_solver. }
    assert (Hx'D1 : x' ∈ D1) by (destruct (proj1 hdsf1 x x' HF1) as [_ Hx']; exact Hx').
    eapply rtc_l; [exact HF1 | apply IH; exact Hx'D1].
Qed.

Lemma path_union_inversion_right:
  forall x y, rtc union x y -> x ∈ D2 -> rtc F2 x y.
Proof.
  intros x y Hpath. induction Hpath as [x|x x' y Hu Hpath IH]; intros HxD2.
  - apply rtc_refl.
  - assert (HF2 : F2 x x').
    { destruct Hu as [HF1 | HF2]; [|exact HF2].
      exfalso. destruct (proj1 hdsf1 x x' HF1) as [Hx1 _]. set_solver. }
    assert (Hx'D2 : x' ∈ D2) by (destruct (proj1 hdsf2 x x' HF2) as [_ Hx']; exact Hx').
    eapply rtc_l; [exact HF2 | apply IH; exact Hx'D2].
Qed.

(* To be a root in [union F1 F2] is to be a root in both [F1] and [F2]. *)

Lemma is_root_join:
  forall x, is_root V union x <-> (is_root V F1 x /\ is_root V F2 x).
Proof.
  unfold is_root, union. intros x. split.
  - intros H. split; intros y Hc; eapply H; eauto.
  - intros [H1 H2] y [HF1 | HF2]; [eapply H1 | eapply H2]; eauto.
Qed.

(* A representative of [x] in [F1], where [x] is in [D1], remains a
   representative of [x] in [union F1 F2]. *)

Lemma is_repr_join_direct_1:
  forall x y, is_repr V F1 x y -> x ∈ D1 -> is_repr V union x y.
Proof.
  intros x y [Hp Hr] HxD1. split.
  - apply path_union_of_1. exact Hp.
  - apply is_root_join. split; [exact Hr|].
    assert (HyD1 : y ∈ D1).
    { destruct (sticky_path V EqV CountableV D1 F1 hdsf1 x y Hp) as [Hfwd _]. apply Hfwd. exact HxD1. }
    eapply only_roots_outside_D; eauto.
Qed.

(* A representative of [x] in [F2], where [x] is outside [D1], remains a
   representative of [x] in [union F1 F2]. (We don't need [x ∈ D2]: if [x] is
   outside both domains, [is_repr F2 x y] already forces [y = x], and [x] is
   trivially a root of [F1] too.) *)

Lemma is_repr_join_direct_2:
  forall x y, is_repr V F2 x y -> x ∉ D1 -> is_repr V union x y.
Proof.
  intros x y [Hp Hr] HxD1. split.
  - apply path_union_of_2. exact Hp.
  - apply is_root_join. split; [|exact Hr].
    destruct (decide (x ∈ D2)) as [HxD2 | HxD2].
    + assert (HyD2 : y ∈ D2).
      { destruct (sticky_path V EqV CountableV D2 F2 hdsf2 x y Hp) as [Hfwd _]. apply Hfwd. exact HxD2. }
      eapply only_roots_outside_D; eauto.
    + assert (Hrootx2 : is_root V F2 x) by (eapply only_roots_outside_D; eauto).
      assert (Hxy : x = y) by (eapply a_path_out_of_a_root_is_trivial; eauto).
      subst y. eapply only_roots_outside_D; eauto.
Qed.

(* The final result: the union of two disjoint disjoint-set-forests, over
   the union of their domains, is again a disjoint-set-forest. *)

Lemma is_dsf_join:
  is_dsf V EqV CountableV (D1 ∪ D2) union.
Proof.
  split; [|split].
  - intros x y [HF1 | HF2].
    + destruct (proj1 hdsf1 x y HF1) as [Hx Hy]. set_solver.
    + destruct (proj1 hdsf2 x y HF2) as [Hx Hy]. set_solver.
  - intros x y1 y2 Hu1 Hu2.
    destruct Hu1 as [HF11 | HF21]; destruct Hu2 as [HF12 | HF22].
    + destruct hdsf1 as [_ [Hfunc1 _]]. eapply Hfunc1; eauto.
    + exfalso. destruct (proj1 hdsf1 x y1 HF11) as [Hx1 _].
      destruct (proj1 hdsf2 x y2 HF22) as [Hx2 _]. set_solver.
    + exfalso. destruct (proj1 hdsf2 x y1 HF21) as [Hx2 _].
      destruct (proj1 hdsf1 x y2 HF12) as [Hx1 _]. set_solver.
    + destruct hdsf2 as [_ [Hfunc2 _]]. eapply Hfunc2; eauto.
  - intros x. destruct (decide (x ∈ D1)) as [HxD1 | HxD1].
    + destruct hdsf1 as [_ [_ Hdef1]]. destruct (Hdef1 x) as [y Hy].
      exists y. eapply is_repr_join_direct_1; eauto.
    + destruct hdsf2 as [_ [_ Hdef2]]. destruct (Hdef2 x) as [y Hy].
      exists y. eapply is_repr_join_direct_2; eauto.
Qed.

End Join.
