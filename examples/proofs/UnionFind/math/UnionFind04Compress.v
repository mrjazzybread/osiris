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

Variable V : Type.
Variable EqV : EqDecision V.
Variable CountableV : Countable V.
Variable F : relation V.
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

Lemma compress_preserves_roots_other_than_x:
  forall r,
  r <> x ->
  is_root V F r ->
  is_root V compress r.
Proof.
  intros r Hneq Hroot w Hcomp.
  destruct Hcomp as [[HF _] | [Heq _]].
  - eapply Hroot; eauto.
  - apply Hneq. exact Heq.
Qed.

Lemma compress_preserves_roots_converse:
  forall r,
  is_root V compress r ->
  is_root V F r.
Proof.
  intros r Hroot w HF.
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
Hypothesis is_dsf_F : is_dsf V EqV CountableV D F.
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
      exact (edge_no_return_path V EqV CountableV D F is_dsf_F x y x_edge_y Hyv). }
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
  is_root V F r ->
  rtc compress v r.
Proof.
  intros v r Hpath. induction Hpath as [ v | v v' r HFvv' Hv'r IH ]; intros Hrootr.
  - apply rtc_refl.
  - destruct (decide (v = x)) as [-> | Hneq].
    + assert (Hv'y : v' = y).
      { destruct is_dsf_F as [_ [Hfunc _]]. eapply Hfunc; eauto. }
      subst v'.
      assert (Hyr : is_repr V F y r) by (split; assumption).
      assert (Hequiv_yz : is_equiv V F y z) by (eapply path_is_equiv; eauto).
      assert (Hzr : is_repr V F z r) by (eapply is_repr_is_equiv_is_repr; eauto).
      eapply rtc_l.
      * apply compress_x_z.
      * apply compress_preserves_paths_out_of_z; [apply Hzr | apply rtc_refl].
    + eapply rtc_l; eauto using compress_preserves_other_edges.
Qed.

(* [is_repr] is preserved (forward direction). *)

Lemma compress_preserves_is_repr_direct:
  forall v r,
  is_repr V F v r ->
  is_repr V compress v r.
Proof.
  intros v r [Hp Hr]. split.
  - apply compress_preserves_paths_to_roots; assumption.
  - destruct (decide (r = x)) as [-> | Hneq].
    + exfalso. eapply a_root_has_no_parent; eauto.
    + apply compress_preserves_roots_other_than_x; assumption.
Qed.

(* The structure of a disjoint set forest is preserved. *)

Lemma is_dsf_compress:
  is_dsf V EqV CountableV D compress.
Proof.
  destruct is_dsf_F as [Hconf [Hfunc Hdef]].
  split; [|split].
  - intros a b Hc. destruct Hc as [[HF Hneq]|[-> ->]].
    + exact (Hconf a b HF).
    + split.
      * exact (proj1 (Hconf x y x_edge_y)).
      * assert (Hy_in_D : y ∈ D) by exact (proj2 (Hconf x y x_edge_y)).
        destruct (sticky_path V EqV CountableV D F is_dsf_F y z y_path_z) as [Hfwd _].
        apply Hfwd. exact Hy_in_D.
  - intros a b1 b2 Hc1 Hc2.
    destruct Hc1 as [[HF1 Hneq1]|[Ha1 Hb1]]; destruct Hc2 as [[HF2 Hneq2]|[Ha2 Hb2]].
    + eapply Hfunc; eauto.
    + exfalso. apply Hneq1. exact Ha2.
    + exfalso. apply Hneq2. exact Ha1.
    + congruence.
  - intro v. destruct (Hdef v) as [r Hr]. exists r. apply compress_preserves_is_repr_direct. exact Hr.
Qed.

(* [is_repr] is preserved, pointwise, in both directions. (Stated as an
   [<->] rather than as a propositional equality of relations, to avoid
   needing functional/propositional extensionality.) *)

Lemma compress_preserves_is_repr:
  forall v r,
  is_repr V F v r <-> is_repr V compress v r.
Proof.
  intros v r. split.
  - apply compress_preserves_is_repr_direct.
  - intros Hcr. destruct is_dsf_F as [_ [_ Hdef]]. destruct (Hdef v) as [r' Hr'].
    assert (Hcr' : is_repr V compress v r') by (apply compress_preserves_is_repr_direct; exact Hr').
    assert (Heq : r = r').
    { eapply (functional_is_repr V EqV CountableV D compress is_dsf_compress); eauto. }
    subst r'. exact Hr'.
Qed.

(* The agreement between [R] and [is_repr F] is preserved when one applies
   [compress] to [F]. Note that [R] is unchanged, as it should be. *)

Lemma compress_R_compress_agree:
  forall R,
  fun_in_rel V R (is_repr V F) ->
  fun_in_rel V R (is_repr V compress).
Proof.
  intros R Hincl w. apply compress_preserves_is_repr. apply Hincl.
Qed.

(* No new paths are created. *)

Lemma compress_preserves_paths_converse:
  forall u w,
  rtc compress u w ->
  rtc F u w.
Proof.
  intros u w Hpath. induction Hpath as [ u | u u' w Hc Hpath IH ].
  - apply rtc_refl.
  - destruct Hc as [[HF Hneq] | [-> ->]].
    + eapply rtc_l; eauto.
    + eapply rtc_trans; [eapply rtc_l; [exact x_edge_y | exact y_path_z] | exact IH].
Qed.

End PathCompression.

(* -------------------------------------------------------------------------- *)

(* Two independent steps of path compression commute. (Stated pointwise as
   an [<->], rather than as a propositional equality of relations, to avoid
   needing functional/propositional extensionality.) *)

Lemma compress_compress:
  forall V (F : relation V) (x1 z1 x2 z2 : V),
  x1 <> x2 ->
  forall a b,
  compress V (compress V F x1 z1) x2 z2 a b <-> compress V (compress V F x2 z2) x1 z1 a b.
Proof.
  unfold compress. intros V F x1 z1 x2 z2 Hneq a b. split; intros H; intuition congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas have weak hypotheses -- they do not rely on the
   hypotheses of the above section -- and this can be convenient. *)

(* Path compression preserves every path whose origin [y] is not a descendant
   of [x]. *)

Lemma compress_preserves_paths_weak:
  forall V (F : relation V) x y z r,
  rtc F y r ->
  ~ rtc F y x ->
  rtc (compress V F x z) y r.
Proof.
  intros V F x y z r Hpath. induction Hpath as [ y | y y' r HF Hpath IH ]; intros Hnopath.
  - apply rtc_refl.
  - eapply rtc_l.
    + apply compress_preserves_other_edges; [exact HF|].
      intro Heq. subst y. apply Hnopath. apply rtc_refl.
    + apply IH. intro Hc. apply Hnopath. eapply rtc_l; eauto.
Qed.

(* Path compression preserves the representative of every vertex [y] that is
   not a descendant of [x]. *)

Lemma compress_preserves_is_repr_weak:
  forall V (F : relation V) x y z r,
  is_repr V F y r ->
  ~ rtc F y x ->
  is_repr V (compress V F x z) y r.
Proof.
  intros V F x y z r [Hp Hr] Hnopath.
  assert (r <> x). { intro. subst. tauto. }
  split.
  - apply compress_preserves_paths_weak; assumption.
  - apply compress_preserves_roots_other_than_x; assumption.
Qed.

(* Analogous lemmas, in the reverse direction. *)

Lemma compress_preserves_paths_weak_converse:
  forall V (Fxz : relation V) y r,
  rtc Fxz y r ->
  forall (F : relation V) x z,
  Fxz = compress V F x z ->
  ~ rtc F y x ->
  rtc F y r.
Proof.
  intros V Fxz y r Hpath. induction Hpath as [ y | y y' r HF Hpath IH ]; intros F x z -> Hnopath.
  - apply rtc_refl.
  - assert (HF' : F y y').
    { eapply compress_preserves_other_edges_converse; eauto.
      intro Heq. subst y. apply Hnopath. apply rtc_refl. }
    eapply rtc_l; eauto.
    eapply IH; [reflexivity|]. intro Hc. apply Hnopath. eapply rtc_l; eauto.
Qed.

Lemma compress_preserves_is_repr_weak_converse:
  forall V (EqV : EqDecision V) (F : relation V) x y z r,
  is_repr V (compress V F x z) y r ->
  ~ rtc F y x ->
  is_repr V F y r.
Proof.
  intros V EqV F x y z r [Hp Hr] Hnopath. split.
  - eapply compress_preserves_paths_weak_converse; [exact Hp | reflexivity | exact Hnopath].
  - eapply (compress_preserves_roots_converse V EqV F x z r); exact Hr.
Qed.
