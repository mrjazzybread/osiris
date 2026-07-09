From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

(* -------------------------------------------------------------------------- *)

(* We consider what happens when one performs one step of path compression:
   given an edge from [x] to [y] and a path from [y] to [z], we replace the
   edge from [x] to [y] with an edge from [x] to [z]. *)

(* The first batch of lemmas below doesn't depend on the [F x y]/[path F y z]
   hypotheses; this is what UnionFind.v's [Mem_compress] needs. The second
   batch (introduced once [y]/[D]/[is_dsf_F]/[y_path_z] come into scope)
   characterizes how [compress] interacts with the specific edge [x -> y] and
   the path beyond it; this is what [find_spec_inductive]'s iterated
   compression argument (UnionFind05IteratedCompression.v) needs. We drop
   [compress_preserves_is_equiv]/[_dsf_per]/[_descendants_of_roots] and
   [ancestors_compress], which aren't needed by [find]. *)

Section PathCompression.

Context {V : Type}.
Context {EqV : EqDecision V}.
Context {CountableV : Countable V}.
Context {F : relation V}.
Variable x z : V.

(* Path compression is performed as follows: every edge out of [x] is
   removed, and a new edge from [x] to [z] is installed. *)

Definition compress : relation V :=
  fun a b => (F a b /\ a <> x) \/ (a = x /\ b = z).

(* We have a new edge from [x] to [z]. *)

Lemma compress_x_z:
  compress x z.
Proof. right. split; reflexivity. Qed.

(* Every existing edge whose source is not [x] is preserved. *)

Lemma compress_preserves_other_edges:
  forall v w,
  F v w ->
  v <> x ->
  compress v w.
Proof. intros v w HF Hneq. left. split; assumption. Qed.

(* Conversely, every [compress]-edge whose source is not [x] is an old edge. *)

Lemma compress_preserves_other_edges_converse:
  forall v w,
  compress v w ->
  v <> x ->
  F v w.
Proof.
  intros v w Hc Hneq. destruct Hc as [[HF _] | [Heq _]].
  - exact HF.
  - exfalso. apply Hneq. exact Heq.
Qed.

(* Every root other than [x] remains a root. *)

Lemma compress_preserves_roots_other_than_x (r : V) :
  r <> x ->
  Root F r ->
  Root compress r.
Proof.
  intros Hneq Hroot.
  constructor; intros w Hcomp.
  destruct Hcomp as [[HF _] | [Heq _]].
  - eapply Hroot; eauto.
  - apply Hneq. exact Heq.
Qed.

Lemma compress_preserves_roots_converse (r : V) :
  Root compress r ->
  Root F r.
Proof.
  intros Hroot.
  constructor; intros y HF.
  destruct (decide (r = x)) as [-> | Hneq].
  - eapply Hroot. right. split; reflexivity.
  - eapply Hroot. left. split; [exact HF | exact Hneq].
Qed.

(* -------------------------------------------------------------------------- *)

(* The following hypotheses are introduced only now, as they are not needed
   by the above lemmas. *)

Variable y : V.
Hypothesis x_edge_y : F x y.
Variable D : gset V.
Hypothesis is_dsf_F : DSF F D.
Hypothesis y_path_z : rtc F y z.

(* Every path out of [y] is preserved. *)

Lemma compress_preserves_paths_out_of_y:
  forall v w,
  rtc F v w ->
  rtc F y v ->
  rtc compress v w.
Proof.
  intros v w Hvw. induction Hvw as [ v | v v' w HFvv' Hv'w IH ]; intros Hyv.
  - apply rtc_refl.
  - assert (Hxv : x <> v).
    { intro Heq. subst v.
      eapply (edge_no_return_path D F _ x y); eauto. }
    eapply rtc_l.
    + eapply compress_preserves_other_edges; eauto.
    + apply IH. eapply rtc_r; eauto.
Qed.

(* Every path out of [z] is preserved. *)

Lemma compress_preserves_paths_out_of_z:
  forall v w,
  rtc F v w ->
  rtc F z v ->
  rtc compress v w.
Proof.
  intros v w Hvw Hzv. apply compress_preserves_paths_out_of_y; [exact Hvw|].
  eapply rtc_trans; eauto.
Qed.

(* Every path to a root is preserved. *)

Lemma compress_preserves_paths_to_roots:
  forall v r,
  rtc F v r ->
  Root F r ->
  rtc compress v r.
Proof.
  intros v r Hpath. induction Hpath as [ v | v v' r HFvv' Hv'r IH ]; intros Hrootr.
  - apply rtc_refl.
  - destruct (decide (v = x)) as [-> | Hneq].
    + assert (Hv'y : v' = y).
      { destruct is_dsf_F as [_ Hfunc _]. eapply functional; eauto. }
      subst v'.
      eapply rtc_l.
      * apply compress_x_z.
      * apply compress_preserves_paths_out_of_z; [ | apply rtc_refl].
        apply repr_path. eapply is_repr_is_equiv_is_repr; eauto.
        split; eauto. eapply path_is_equiv; eauto.
    + eapply rtc_l; eauto using compress_preserves_other_edges.
Qed.

(* [is_repr] is preserved (forward direction). *)

Lemma compress_preserves_is_repr_direct (v r : V) :
  Repr F v r ->
  Repr compress v r.
Proof.
  intros [Hp Hr]. split.
  - apply compress_preserves_paths_to_roots; assumption.
  - destruct (decide (r = x)) as [-> | Hneq].
    + exfalso. eapply a_root_has_no_parent; eauto.
    + apply compress_preserves_roots_other_than_x; assumption.
Qed.

(* The structure of a disjoint set forest is preserved. *)

Instance is_dsf_compress:
  DSF compress D.
Proof.
  destruct is_dsf_F as [Hconf Hfunc Hdef].
  constructor; constructor.
  - intros a b Hc. destruct Hc as [[HF Hneq]|[-> ->]].
    + exact (confined a b HF).
    + split.
      * apply (confined x y x_edge_y).
      * eapply (sticky_path D F _ y z).
        apply y_path_z. apply (confined _ _ x_edge_y).
  - intros a b1 b2 Hc1 Hc2.
    destruct Hc1 as [[HF1 Hneq1]|[Ha1 Hb1]]; destruct Hc2 as [[HF2 Hneq2]|[Ha2 Hb2]].
    + eapply functional; eauto.
    + exfalso. apply Hneq1. exact Ha2.
    + exfalso. apply Hneq2. exact Ha1.
    + congruence.
  - intro v. destruct (defined v) as [r Hr]. exists r. apply compress_preserves_is_repr_direct. exact Hr.
Qed.

(* [is_repr] is preserved, pointwise, in both directions. (Stated as an
   [<->] rather than as a propositional equality of relations, to avoid
   needing functional/propositional extensionality.) *)

Lemma compress_preserves_is_repr (v r : V) :
  Repr F v r <-> Repr compress v r.
Proof.
  split.
  - apply compress_preserves_is_repr_direct.
  - intros Hcr. destruct is_dsf_F as [_ _ Hdef]. destruct (defined v) as [r' Hr'].
    assert (Heq : r = r').
    { eapply (functional_is_repr D compress); eauto.
      + apply is_dsf_compress.
      + apply compress_preserves_is_repr_direct. assumption. }
    subst r'. exact Hr'.
Qed.

(* The agreement between [R] and [is_repr F] is preserved when one applies
   [compress] to [F]. Note that [R] is unchanged, as it should be. *)

Lemma compress_R_compress_agree (R : V → V) :
  rel_incl R (Repr F) ->
  rel_incl R (Repr compress).
Proof.
  intros Hincl. constructor; intros w. apply compress_preserves_is_repr. apply Hincl.
Qed.

(* No new paths are created. *)

Lemma compress_preserves_paths_converse (u w : V) :
  rtc compress u w ->
  rtc F u w.
Proof.
  intros Hpath. induction Hpath as [ u | u u' w Hc Hpath IH ].
  - apply rtc_refl.
  - destruct Hc as [[HF Hneq] | [-> ->]].
    + eapply rtc_l; eauto.
    + eapply rtc_trans; [eapply rtc_l; [exact x_edge_y | exact y_path_z] | exact IH].
Qed.

End PathCompression.

Arguments compress {_} F.

(* -------------------------------------------------------------------------- *)

(* Two independent steps of path compression commute. (Stated pointwise as
   an [<->], rather than as a propositional equality of relations, to avoid
   needing functional/propositional extensionality.) *)

Lemma compress_compress `{F : relation V} (x1 z1 x2 z2 : V) :
  x1 <> x2 ->
  ∀ a b,
  compress (compress F x1 z1) x2 z2 a b <-> compress (compress F x2 z2) x1 z1 a b.
Proof.
  unfold compress. intros Hneq a b. split; intros H; intuition congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas have weak hypotheses -- they do not rely on the
   hypotheses of the above section -- and this can be convenient. *)

(* Path compression preserves every path whose origin [y] is not a descendant
   of [x]. *)

Lemma compress_preserves_paths_weak `{F : relation V} (x y z r : V) :
  rtc F y r ->
  ~ rtc F y x ->
  rtc (compress F x z) y r.
Proof.
  intros Hpath. induction Hpath as [ y | y y' r HF Hpath IH ]; intros Hnopath.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply compress_preserves_other_edges; [exact HF|].
      intro Heq. subst y. apply Hnopath. apply rtc_refl.
    + apply IH. intro Hc. apply Hnopath. eapply rtc_l; eauto.
Qed.

(* Path compression preserves the representative of every vertex [y] that is
   not a descendant of [x]. *)

Lemma compress_preserves_is_repr_weak `{F : relation V} (x y z r : V) :
  Repr F y r ->
  ~ rtc F y x ->
  Repr (compress F x z) y r.
Proof.
  intros [Hp Hr] Hnopath.
  assert (r <> x). { intro. subst. tauto. }
  split.
  - apply compress_preserves_paths_weak; assumption.
  - apply compress_preserves_roots_other_than_x; assumption.
Qed.

(* Analogous lemmas, in the reverse direction. *)

Lemma compress_preserves_paths_weak_converse `{Fxz : relation V} (y r : V) :
  rtc Fxz y r ->
  ∀ (F : relation V) x z,
  Fxz = compress F x z ->
  ~ rtc F y x ->
  rtc F y r.
Proof.
  intros Hpath. induction Hpath as [ y | y y' r HF Hpath IH ]; intros F x z -> Hnopath.
  - apply rtc_refl.
  - assert (HF' : F y y').
    { eapply compress_preserves_other_edges_converse; eauto.
      intro Heq. subst y. apply Hnopath. apply rtc_refl. }
    eapply rtc_l; eauto.
    eapply IH; [reflexivity|]. intro Hc. apply Hnopath. eapply rtc_l; eauto.
Qed.

Lemma compress_preserves_is_repr_weak_converse `{EqDecision V} {F : relation V} (x y z r : V) :
  Repr (compress F x z) y r ->
  ~ rtc F y x ->
  Repr F y r.
Proof.
  intros [Hp Hr] Hnopath. constructor.
  - eapply compress_preserves_paths_weak_converse; [exact Hp | reflexivity | exact Hnopath].
  - eapply (compress_preserves_roots_converse x z r); exact Hr.
Qed.
