From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

(* -------------------------------------------------------------------------- *)

(* We consider what happens when one installs a new link from [x] to [y],
   where [x] and [y] are distinct roots and are in the domain D.

   We drop the original's rank-based linking (link_by_rank_F/K/R,
   new_repr_by_rank) and the descendants/cardinality lemmas that supported
   its amortized-complexity analysis (descendants_link_1, descendants_link_2,
   card_descendants_link_2_le, etc.); those existed purely to bound the cost
   of [union], which this port
   isn't redoing. We also drop the PER-algebra characterization
   (is_equiv_per_add_edge, per_add_edge_confine, dsf_per_add_edge) and the
   "converse" lemmas (is_root_link_converse, is_root_link_not_x,
   x_no_longer_a_root, path_link_*_converse), none of which UnionFind.v's
   Inv/Mem layer needs. *)

Section Link.

Variable V : Type.
Variable EqV : EqDecision V.
Variable CountableV : Countable V.
Variable D : gset V.
Variable F : relation V.
Variable x y : V.

Hypothesis is_dsf_F:  is_dsf V EqV CountableV D F.
Hypothesis x_in_D:    x ∈ D.
Hypothesis y_in_D:    y ∈ D.
Hypothesis is_root_x: is_root V F x.
Hypothesis is_root_y: is_root V F y.
Hypothesis distinct:  x <> y.

(* The link is installed as follows: we add the single edge [x -> y] to [F]. *)

Definition per_single (a b : V) : Prop := a = x /\ b = y.

Definition link : relation V := fun a b => F a b \/ per_single a b.

(* This does install an edge from [x] to [y]. *)

Lemma link_appears:
  link x y.
Proof. right. split; reflexivity. Qed.

(* This preserves every pre-existing edge. *)

Lemma link_previous:
  forall w z,
  F w z ->
  link w z.
Proof. intros w z HF. left. exact HF. Qed.

(* Installing the new link preserves [functional]. *)

Lemma functional_link:
  functional V link.
Proof.
  destruct is_dsf_F as [_ [Hfunc _]].
  intros a b1 b2 H1 H2.
  destruct H1 as [HF1 | [Ha1 Hb1]]; destruct H2 as [HF2 | [Ha2 Hb2]].
  - eapply Hfunc; eauto.
  - subst a. exfalso. eapply is_root_x; eauto.
  - subst a. exfalso. eapply is_root_x; eauto.
  - subst. reflexivity.
Qed.

(* Every vertex that could reach [x] can now reach [y]. *)

Lemma path_link_1:
  forall w,
  rtc F w x ->
  rtc link w y.
Proof.
  apply (rtc_ind_l (R:=F) (fun w => rtc link w y) x).
  - apply rtc_once. apply link_appears.
  - intros a b HF Hpath IH. eapply rtc_l; [apply link_previous; exact HF | exact IH].
Qed.

(* Every pre-existing path is preserved. *)

Lemma path_link_2:
  forall w z,
  rtc F w z ->
  rtc link w z.
Proof.
  intros w z Hpath.
  apply (rtc_ind_l (R:=F) (fun w => rtc link w z) z).
  - apply rtc_refl.
  - intros a b HF Hpath' IH. eapply rtc_l; [apply link_previous; exact HF | exact IH].
  - exact Hpath.
Qed.

(* Every root other than [x] remains a root. *)

Lemma is_root_link:
  forall z,
  is_root V F z ->
  x <> z ->
  is_root V link z.
Proof.
  intros z Hrootz Hneq w Hlink.
  destruct Hlink as [HF | [Heq Heq2]].
  - eapply Hrootz; eauto.
  - exact (Hneq (eq_sym Heq)).
Qed.

(* Every vertex whose representative was [x] now has representative [y]. *)

Lemma is_repr_link_1:
  forall w,
  is_repr V F w x ->
  is_repr V link w y.
Proof.
  intros w [Hpath Hrootx].
  split.
  - apply path_link_1. exact Hpath.
  - apply is_root_link; [exact is_root_y | exact distinct].
Qed.

(* Every vertex whose representative was some vertex [r] other than [x] still
   has representative [r]. *)

Lemma is_repr_link_2:
  forall w r,
  is_repr V F w r ->
  r <> x ->
  is_repr V link w r.
Proof.
  intros w r [Hpath Hrootr] Hneq.
  split.
  - apply path_link_2. exact Hpath.
  - apply is_root_link; [exact Hrootr | intro Heq; apply Hneq; exact (eq_sym Heq)].
Qed.

(* Installing the new link preserves [defined]. *)

Lemma defined_link:
  defined V (is_repr V link).
Proof.
  destruct is_dsf_F as [_ [_ Hdef]].
  intros w. destruct (Hdef w) as [r Hr].
  destruct (decide (r = x)) as [-> | Hneq].
  - exists y. apply is_repr_link_1. exact Hr.
  - exists r. apply is_repr_link_2; [exact Hr | exact Hneq].
Qed.

(* Installing the new link preserves [is_dsf]. *)

Lemma is_dsf_link:
  is_dsf V EqV CountableV D link.
Proof.
  destruct is_dsf_F as [Hconf _].
  split; [|split].
  - intros a b [HF | [-> ->]].
    + exact (Hconf a b HF).
    + split; assumption.
  - exact functional_link.
  - exact defined_link.
Qed.

(* -------------------------------------------------------------------------- *)

(* If one wishes to reason in terms of the function [R], which maps every
   vertex to its representative, here is how the effect of a link operation
   is described: every vertex in the equivalence class of [x] (as seen by
   [R]) gets remapped to [y]; everything else is unchanged. *)

Definition link_R (R : V -> V) : V -> V :=
  fun t => if decide (R t = R x) then y else R t.

(* The agreement between [R] and [is_repr F] is preserved when one
   applies [link_R] and [link] to [R] and [F], respectively. *)

Lemma link_R_link_agree:
  forall R,
  fun_in_rel V R (is_repr V F) ->
  fun_in_rel V (link_R R) (is_repr V link).
Proof.
  intros R Hincl w.
  assert (HRx : R x = x) by (eapply is_root_R_self; eauto).
  assert (HRy : R y = y) by (eapply is_root_R_self; eauto).
  unfold link_R. destruct (decide (R w = R x)) as [Heq | Hneq].
  - apply is_repr_link_1.
    assert (Hxx : is_repr V F x x) by (apply is_root_is_repr; exact is_root_x).
    assert (Heqv : is_equiv V F x w).
    { eapply same_R_incl_is_equiv; eauto. }
    eapply is_repr_is_equiv_is_repr; eauto.
  - apply is_repr_link_2; [apply Hincl |].
    intro Hc. apply Hneq. rewrite Hc. symmetry. exact HRx.
Qed.

End Link.
