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

Context {V : Type}.
Context {EqV : EqDecision V}.
Context {CountableV : Countable V}.
Variable D : gset V.
Variable F : relation V.
Variable x y : V.

Hypothesis is_dsf_F:  DSF F D.
Hypothesis x_in_D:    x ∈ D.
Hypothesis y_in_D:    y ∈ D.
Hypothesis is_root_x: Root F x.
Hypothesis is_root_y: Root F y.
Hypothesis distinct:  x <> y.

(* The link is installed as follows: we add the single edge [x -> y] to [F]. *)

Definition per_single (a b : V) : Prop := a = x /\ b = y.

Definition link : relation V := fun a b => F a b \/ per_single a b.

(* This does install an edge from [x] to [y]. *)

Lemma link_appears:
  link x y.
Proof. right. split; reflexivity. Qed.

(* This preserves every pre-existing edge. *)

Lemma link_previous (w z : V) :
  F w z ->
  link w z.
Proof. intros HF. left. exact HF. Qed.

(* Installing the new link preserves [functional]. *)

Instance functional_link:
  Functional link.
Proof.
  destruct is_dsf_F as [_ Hfunc _].
  constructor.
  intros a b1 b2 H1 H2.
  destruct H1 as [HF1 | [Ha1 Hb1]]; destruct H2 as [HF2 | [Ha2 Hb2]].
  - eapply (functional F); eauto.
  - subst a. exfalso. eapply is_root_x; eauto.
  - subst a. exfalso. eapply is_root_x; eauto.
  - subst. reflexivity.
Qed.

(* Every vertex that could reach [x] can now reach [y]. *)

Lemma path_link_1 (w : V) :
  rtc F w x ->
  rtc link w y.
Proof.
  apply (rtc_ind_l (R:=F) (fun w => rtc link w y) x).
  - apply rtc_once. apply link_appears.
  - intros a b HF Hpath IH. eapply rtc_l; [apply link_previous; exact HF | exact IH].
Qed.

(* Every pre-existing path is preserved. *)

Lemma path_link_2 (w z : V) :
  rtc F w z ->
  rtc link w z.
Proof.
  intros Hpath.
  apply (rtc_ind_l (R:=F) (fun w => rtc link w z) z).
  - apply rtc_refl.
  - intros a b HF Hpath' IH. eapply rtc_l; [apply link_previous; exact HF | exact IH].
  - exact Hpath.
Qed.

(* Every root other than [x] remains a root. *)

Lemma is_root_link (z : V) :
  Root F z ->
  x <> z ->
  Root link z.
Proof.
  intros Hrootz Hneq.
  constructor. intros w Hlink.
  destruct Hlink as [HF | [Heq Heq2]].
  - eapply Hrootz; eauto.
  - exact (Hneq (eq_sym Heq)).
Qed.

(* Every vertex whose representative was [x] now has representative [y]. *)

Lemma is_repr_link_1 (w : V) :
  Repr F w x ->
  Repr link w y.
Proof.
  intros [Hpath Hrootx].
  split.
  - apply path_link_1. exact Hpath.
  - apply is_root_link; [exact is_root_y | exact distinct].
Qed.

(* Every vertex whose representative was some vertex [r] other than [x] still
   has representative [r]. *)

Lemma is_repr_link_2 (w r : V) :
  Repr F w r ->
  r <> x ->
  Repr link w r.
Proof.
  intros [Hpath Hrootr] Hneq.
  split.
  - apply path_link_2. exact Hpath.
  - apply is_root_link; [exact Hrootr | intro Heq; apply Hneq; exact (eq_sym Heq)].
Qed.

(* Installing the new link preserves [defined]. *)

Instance defined_link:
  Defined (Repr link).
Proof.
  destruct is_dsf_F as [_ _ Hdef].
  constructor. intros w.
  destruct (defined w) as [r Hr].
  destruct (decide (r = x)) as [-> | Hneq].
  - exists y. apply is_repr_link_1. exact Hr.
  - exists r. apply is_repr_link_2; [exact Hr | exact Hneq].
Qed.

(* Installing the new link preserves [is_dsf]. *)

Instance is_dsf_link:
  DSF link D.
Proof.
  destruct is_dsf_F as [Hconf _ _].
  constructor.
  - constructor. intros a b [HF | [-> ->]].
    + exact (confined a b HF).
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

Lemma link_R_link_agree (R : V → V) :
  rel_incl R (Repr F) ->
  rel_incl (link_R R) (Repr link).
Proof.
  intros Hincl. constructor. intros w.
  assert (HRx : R x = x) by (eapply is_root_R_self; eauto).
  assert (HRy : R y = y) by (eapply is_root_R_self; eauto).
  unfold link_R. destruct (decide (R w = R x)) as [Heq | Hneq].
  - apply is_repr_link_1.
    assert (Hxx : Repr F x x) by (apply is_root_is_repr; exact is_root_x).
    assert (Heqv : is_equiv F x w).
    { eapply same_R_incl_is_equiv; eauto. }
    eapply is_repr_is_equiv_is_repr; eauto.
  - apply is_repr_link_2; [apply Hincl |].
    intro Hc. apply Hneq. rewrite Hc. symmetry. exact HRx.
Qed.

End Link.
