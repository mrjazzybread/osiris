From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

(* The union of two separate disjoint set forests is again a disjoint set
   forest. This is obvious, of course, but takes some work. *)

Section Join.

Context {V : Type}.
Context {EqV : EqDecision V}.
Context {CountableV : Countable V}.
Variable D1 D2 : gset V.
Variable F1 F2 : relation V.

Hypothesis disjointness : D1 ## D2.
Hypothesis hdsf1 : DSF F1 D1.
Hypothesis hdsf2 : DSF F2 D2.

Instance relation_union : Union (relation V) := λ f1 f2, fun a b => f1 a b ∨ f2 a b.
Definition union : relation V := F1 ∪ F2.

(* If [x] is in [D1], then its [union]-edges are exactly its [F1]-edges. *)

Lemma edge_union_inversion_1 (x y : V) :
  x ∈ D1 -> union x y <-> F1 x y.
Proof.
  intros HxD1. split.
  - intros [HF1 | HF2]; [exact HF1|].
    exfalso. destruct hdsf2 as [[Hconf] _ _]. specialize (Hconf x y HF2).
    set_solver.
  - intros HF1. left. exact HF1.
Qed.

Lemma edge_union_inversion_2 (x y : V) :
  x ∈ D2 -> union x y <-> F2 x y.
Proof.
  intros HxD2. split.
  - intros [HF1 | HF2]; [|exact HF2].
    exfalso. destruct hdsf1 as [[Hconf] _ _]. specialize (Hconf x y HF1).
    set_solver.
  - intros HF2. right. exact HF2.
Qed.

(* Every [F1]-path (resp. [F2]-path) is a [union]-path. *)

Lemma path_union_of_1 (x y : V) :
  rtc F1 x y -> rtc union x y.
Proof.
  intros Hpath. induction Hpath as [x|x x' y HF1 Hpath IH].
  - apply rtc_refl.
  - eapply rtc_l; [left; exact HF1 | exact IH].
Qed.

Lemma path_union_of_2 (x y : V) :
  rtc F2 x y -> rtc union x y.
Proof.
  intros Hpath. induction Hpath as [x|x x' y HF2 Hpath IH].
  - apply rtc_refl.
  - eapply rtc_l; [right; exact HF2 | exact IH].
Qed.

(* Every [union]-path out of a point of [D1] is an [F1]-path; symmetrically
   for [D2]. *)

Lemma path_union_inversion_left (x y : V) :
  rtc union x y -> x ∈ D1 -> rtc F1 x y.
Proof.
  intros Hpath. induction Hpath as [x |x x' y Hu Hpath IH]; intros HxD1.
  - apply rtc_refl.
  - assert (HF1 : F1 x x').
    { destruct Hu as [HF1 | Hf2]; [exact HF1|].
      exfalso. destruct hdsf2 as [[Hconf] _ _]. specialize (Hconf x x' Hf2).
      set_solver. }
    eapply rtc_l.
    + apply HF1.
    + apply IH.
      destruct hdsf1 as [[Hconf] _ _]. eapply Hconf. apply HF1.
Qed.

Lemma path_union_inversion_right (x y : V) :
  rtc union x y -> x ∈ D2 -> rtc F2 x y.
Proof.
  intros Hpath. induction Hpath as [x|x x' y Hu Hpath IH]; intros HxD2.
  - apply rtc_refl.
  - assert (HF2 : F2 x x').
    { destruct Hu as [HF1 | HF2]; [|exact HF2].
      exfalso. destruct hdsf1 as [[Hconf] _ _]. specialize (Hconf x x' HF1).
      set_solver. }
    eapply rtc_l.
    + apply HF2.
    + apply IH.
      destruct hdsf2 as [[Hconf] _ _]. eapply Hconf. apply HF2.
Qed.

(* To be a root in [union F1 F2] is to be a root in both [F1] and [F2]. *)

Lemma is_root_join (x : V) :
  Root union x <-> (Root F1 x ∧ Root F2 x).
Proof.
  split.
  - intros [HF]. split; constructor; intros y Hc; apply (HF y).
    + by left.
    + by right.
  - intros [[H1] [H2]].
    constructor; intros y [|]; [eapply H1 | eapply H2]; eauto.
Qed.

(* A representative of [x] in [F1], where [x] is in [D1], remains a
   representative of [x] in [union F1 F2]. *)

Lemma is_repr_join_direct_1 (x y : V):
  Repr F1 x y -> x ∈ D1 -> Repr union x y.
Proof.
  intros [Hp Hr] HxD1. split.
  - apply path_union_of_1. exact Hp.
  - apply is_root_join. split; [exact Hr|].
    eapply (only_roots_outside_D D2 F2); eauto.
    destruct (sticky_path D1 F1 hdsf1 x y Hp) as [Hfwd _].
    set_solver.
Qed.

(* A representative of [x] in [F2], where [x] is outside [D1], remains a
   representative of [x] in [union F1 F2]. (We don't need [x ∈ D2]: if [x] is
   outside both domains, [Repr F2 x y] already forces [y = x], and [x] is
   trivially a root of [F1] too.) *)

Lemma is_repr_join_direct_2 (x y : V) :
  Repr F2 x y -> x ∉ D1 -> Repr union x y.
Proof.
  intros [Hp Hr] HxD1. constructor.
  - apply path_union_of_2. exact Hp.
  - apply is_root_join. split; [|exact Hr].
    destruct (decide (x ∈ D2)) as [HxD2 | HxD2].
    + eapply only_roots_outside_D; eauto.
      destruct (sticky_path D2 F2 _ x y Hp) as [Hfwd _].
      set_solver.
    + assert (x = y) as ->.
      { eapply a_path_out_of_a_root_is_trivial; eauto.
        eapply only_roots_outside_D; eauto. }
      eapply only_roots_outside_D; eauto.
Qed.

(* The final result: the union of two disjoint disjoint-set-forests, over
   the union of their domains, is again a disjoint-set-forest. *)

Lemma is_dsf_join:
  DSF (F1 ∪ F2) (D1 ∪ D2).
Proof.
  pose proof hdsf1 as [[Hconf1] _ _].
  pose proof hdsf2 as [[Hconf2] _ _].
  constructor; constructor.
  - intros x y [HF1 | HF2]; set_solver.
  - intros x y1 y2 Hu1 Hu2.
    destruct Hu1 as [HF11 | HF21]; destruct Hu2 as [HF12 | HF22].
    + destruct hdsf1 as [_ [Hfunc1] _]. eapply Hfunc1; eauto.
    + exfalso. set_solver.
    + exfalso. set_solver.
    + destruct hdsf2 as [_ [Hfunc2] _]. eapply Hfunc2; eauto.
  - intros x. destruct (decide (x ∈ D1)) as [HxD1 | HxD1].
    + destruct hdsf1 as [_ _ [Hdef1]]. destruct (Hdef1 x) as [y Hy].
      exists y. eapply is_repr_join_direct_1; eauto.
    + destruct hdsf2 as [_ _ [Hdef2]]. destruct (Hdef2 x) as [y Hy].
      exists y. eapply is_repr_join_direct_2; eauto.
Qed.

End Join.
