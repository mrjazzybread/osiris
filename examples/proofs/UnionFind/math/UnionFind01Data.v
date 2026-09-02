From osiris Require Import osiris.
From stdpp Require Import relations propset.

Require Export UnionFind00Update.

(* Definition of disjoint set forests. *)

Section DisjointSetForest.

(* -------------------------------------------------------------------------- *)

(* A type of vertices. *)

Context {V : Type}.
Context {EqV : EqDecision V}.
Context {CountableV : Countable V}.

(* We restrict our attention to a certain set of vertices, the domain
   of the forest. Keeping track of [D] allows us to distinguish an
   isolated vertex from a vertex that does not exist at all. *)

Variable D : gset V.

(* [F] can also be viewed as a directed graph over vertices of type [V]. In
   the following, we define a disjoint set forest (dsf, for short) as a
   directed graph that satisfies certain properties. *)

Variable F : relation V.

(* -------------------------------------------------------------------------- *)

(* A handful of generic relation/set predicates, standing in for what TLC's
   LibRelation/LibContainer/LibPer provided. Kept local to this file for now;
   we can hoist them to a shared buffer file once a second file needs them. *)

Class Functional (R : relation V) :=
  { functional : ∀ x y1 y2, R x y1 → R x y2 → y1 = y2 }.

Class Defined (R : relation V) :=
  { defined : ∀ x, ∃ y, R x y }.

Class Confined (Dom : gset V) (R : relation V) :=
  { confined : ∀ x y, R x y → x ∈ Dom ∧ y ∈ Dom }.

(* [sticky Dom R] says that membership of [Dom] is preserved (in both
   directions) across an [R]-edge. *)

Definition sticky (Dom : gset V) (R : relation V) :=
  forall x y, R x y -> (x ∈ Dom <-> y ∈ Dom).

Definition confine (Dom : gset V) (R : relation V) : relation V :=
  fun x y => x ∈ Dom /\ R x y /\ y ∈ Dom.

Definition per (R : relation V) :=
  (forall x y, R x y -> R y x) /\
  (forall x y z, R x y -> R y z -> R x z).

Definition per_dom (R : relation V) : propset V :=
  {[ x | R x x ]}.

Definition set_finite (X : propset V) :=
  exists Y : gset V, forall x, x ∈ X -> x ∈ Y.

(* A vertex [x] is a root if it has no successor. *)

Class Root {V} (F : relation V) x :=
  { is_root : ∀ y, ~ F x y }.

(* [path] is the reflexive-transitive closure of [F]. stdpp's [rtc] is
   defined left-recursively (peeling the first edge), which is exactly the
   recursion direction TLC's [rtclosure_ind_l]/[rtclosure_inv_l] needed a
   dedicated lemma for; here plain [induction]/[destruct] already gives us
   that shape for free. *)

Local Abbreviation path := rtc.

(* The descendants of [r] are the vertices [x] such that there exists a path
   from [x] to [r]. Since [F] need not be decidable, this can fail to be
   finite as a subset of [V], so we represent it as a predicate ([propset])
   rather than as a [gset]. *)

Definition descendants r : propset V :=
  {[ x | path F x r ]}.

(* In a functional graph (i.e., a graph where every vertex has at most one
   successor), the vertex [r] is the representative for the vertex [x] iff
   there is a path from [x] to [r] and [r] is a root. In other words, there
   exists a maximal path from [x] to [r]. *)

Class Repr x r :=
  { repr_path : path F x r;
    repr_root : Root F r }.
Arguments repr_path : clear implicits.
Arguments repr_root : clear implicits.

(* A graph is a disjoint set forest with domain [D] iff every edge begins and
   ends within [D] and the graph is functional (i.e., every vertex has at most
   one successor) and acyclic (i.e., every vertex has a representative). *)

Class DSF D :=
  { dsf_confined : Confined D F;
    dsf_functional : Functional F;
    dsf_defined : Defined Repr }.

(* Two vertices are equivalent if they have a common representative. *)

Definition is_equiv x y :=
  exists r, Repr x r /\ Repr y r.

(* The partial equivalence relation (PER) encoded by this disjoint set forest
   is the restriction of [is_equiv] to the domain [D]. *)

Definition dsf_per : relation V :=
  confine D is_equiv.

(* -------------------------------------------------------------------------- *)

(* In the following, we assume that [F] is a disjoint set forest with
   domain [D]. *)

Instance is_dsf_confined `{is_dsf_F : DSF D} : Confined D F.
Proof. destruct is_dsf_F. apply _. Qed.
Instance is_dsf_functional `{is_dsf_F : DSF D} : Functional F.
Proof. destruct is_dsf_F. apply _. Qed.
Instance is_dsf_defined_is_repr `{is_dsf_F : DSF D} : Defined Repr.
Proof. destruct is_dsf_F. apply _. Qed.

Hypothesis is_dsf_F :
  DSF D.

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_root], [is_repr], [is_equiv]. *)

(* A root has no parent. *)

Lemma a_root_has_no_parent (x y : V) :
  Root F x ->
  F x y ->
  False.
Proof.
  intros [Hroot] HF. exact (Hroot y HF).
Qed.

(* Hence, a path out of a root must be a trivial path. *)

Lemma a_path_out_of_a_root_is_trivial (x y : V) :
  Root F x ->
  path F x y ->
  x = y.
Proof.
  intros Hroot Hpath. induction Hpath as [ x | x x' y HF Hpath IH ].
  - reflexivity.
  - exfalso. eapply a_root_has_no_parent; eauto.
Qed.

(* The relation [is_repr] is functional, i.e., a vertex has at most
   one representative. *)

Instance functional_is_repr:
  Functional Repr.
Proof.
  constructor.
  intros x r1 r2 [Hp1 Hr1] [Hp2 Hr2].
  revert r2 Hp2 Hr2.
  revert Hr1.
  induction Hp1.
  - intros Hroot r2 Hp2 Hr2.
    eapply a_path_out_of_a_root_is_trivial; eauto.
  - intros Hr1 r2 Hp2 Hr2.
    destruct Hp2 as [ | x y'' r2 HF' Hp2' ].
    + exfalso. eapply a_root_has_no_parent; eauto.
    + assert (y = y'') as <- by (eapply is_dsf_functional; eauto).
      eapply IHHp1; eauto.
Qed.

(* [exploit_functional R] finds two hypotheses [R x y1] and [R x y2] in the
   context and uses functionality of [R] (looked up in the [functional] hint
   database) to unify [y1] and [y2]. *)

Ltac exploit_functional R :=
  match goal with
  | h1 : R ?x ?y1, h2 : R ?x ?y2 |- _ =>
      let Hfun := fresh "Hfun" in
      assert (Functional R) as Hfun by (apply _);
      assert (y1 = y2) as <- by (eapply Hfun; eauto);
      clear h2
  end.

(* Two equivalent vertices must have the same representative. *)

Instance is_repr_is_equiv_is_repr (x y r : V) :
  Repr x r ->
  is_equiv x y ->
  Repr y r.
Proof.
  intros Hxr [r' [Hxr' Hyr']].
  exploit_functional Repr.
  exact Hyr'.
Qed.

Lemma is_repr_is_equiv_is_repr_bis (x y rx ry : V) :
  Repr x rx ->
  is_equiv x y ->
  Repr y ry ->
  rx = ry.
Proof.
  intros Hxrx [r [Hxr Hyr]] Hyry.
  exploit_functional Repr.
  exploit_functional Repr.
  reflexivity.
Qed.

(* [is_equiv] is an equivalence relation. *)

Lemma is_equiv_refl (x : V) :
  is_equiv x x.
Proof.
  destruct (defined x) as [r Hr].
  exists r. auto.
Qed.

Lemma is_equiv_sym (x y : V):
  is_equiv x y ->
  is_equiv y x.
Proof.
  intros [r [Hx Hy]]. exists r. auto.
Qed.

Lemma is_equiv_trans (x y z : V) :
  is_equiv x y ->
  is_equiv y z ->
  is_equiv x z.
Proof.
  intros [r1 [Hxr1 Hyr1]] [r2 [Hyr2 Hzr2]].
  exists r1. split; [assumption|].
  exploit_functional Repr.
  assumption.
Qed.

(* Two vertices that are connected by a path must be equivalent. *)

Lemma path_is_equiv (x y : V) :
  path F x y ->
  is_equiv x y.
Proof.
  intros Hpath.
  destruct (defined y) as [r [Hyr Hrootr]].
  exists r. split.
  - split; [eapply rtc_trans; eauto | exact Hrootr].
  - split; [exact Hyr | exact Hrootr].
Qed.

(* [is_equiv] coincides with the reflexive-symmetric-transitive closure of
   [F], i.e. stdpp's [rtsc F]. (Renamed from the original [is_equiv_rstclosure]
   and restated pointwise as an [<->] rather than a relation [=], so that we
   don't need functional/propositional extensionality.) *)

Lemma is_equiv_iff_rstclosure (x y : V) :
  is_equiv x y <-> rtsc F x y.
Proof.
  split.
  - intros [r [[Hxr _] [Hyr _]]].
    transitivity r.
    + apply rtc_rtsc_rl. exact Hxr.
    + symmetry. apply rtc_rtsc_rl. exact Hyr.
  - intros Hrtsc. induction Hrtsc as [ x | x x' y Hstep Hrtsc IH ].
    + apply is_equiv_refl.
    + assert (is_equiv x x') as Hxx'.
      { destruct Hstep as [HF | HF].
        - eapply path_is_equiv. eapply rtc_once. exact HF.
        - eapply is_equiv_sym. eapply path_is_equiv. eapply rtc_once. exact HF. }
      eapply is_equiv_trans; eauto.
Qed.

(* A representative is a root. *)

Instance is_repr_is_root (x r : V):
  Repr x r ->
  Root F r.
Proof.
  intros [_ Hroot]. exact Hroot.
Qed.

(* A root is its own representative. *)

Instance is_root_is_repr (r : V) :
  Root F r ->
  Repr r r.
Proof.
  intros Hroot. split; [apply rtc_refl | exact Hroot].
Qed.

(* A vertex is equivalent to its representative. *)

Lemma is_repr_equiv_root (x r : V) :
  Repr x r ->
  is_equiv x r.
Proof.
  intros Hxr. exists r. split; [exact Hxr | eapply is_root_is_repr, is_repr_is_root, Hxr].
Qed.

(* [dsf_per] is indeed a partial equivalence relation. *)

Lemma per_dsf_per:
  per dsf_per.
Proof.
  unfold per, dsf_per, confine. split.
  - intros x y (Hx & Hxy & Hy). split; [exact Hy | split; [apply is_equiv_sym; exact Hxy | exact Hx]].
  - intros x y z (Hx & Hxy & Hy) (Hy' & Hyz & Hz). split; [exact Hx | split; [eapply is_equiv_trans; eauto | exact Hz]].
Qed.

(* Its domain is indeed [D]. (Restated pointwise rather than as a [propset]
   equality, since comparing a [propset] to a [gset] by [=] would need an
   extensionality axiom we're avoiding for now.) *)

Lemma per_dom_dsf_per:
  forall x,
  x ∈ per_dom dsf_per <-> x ∈ D.
Proof.
  unfold per_dom, dsf_per, confine. intros x. rewrite elem_of_PropSet.
  split.
  - intros (Hx & _ & _). exact Hx.
  - intros Hx. split; [exact Hx | split; [apply is_equiv_refl | exact Hx]].
Qed.

(* There is a path from the parent [y] of a non-root vertex [x]
   to the representative [z] of [x]. *)

Lemma path_from_parent_to_repr_F (x y z : V) :
  Repr x z ->
  F x y ->
  path F y z.
Proof.
  intros Hxz HF.
  eapply repr_path.
  eapply is_repr_is_equiv_is_repr; eauto.
  eapply path_is_equiv. eapply rtc_once. exact HF.
Qed.

(* -------------------------------------------------------------------------- *)

(* Everything takes place within [D]. *)

Lemma sticky_path:
  sticky D (path F).
Proof.
  unfold sticky. intros x y Hpath.
  induction Hpath as [ x | x x' y HF Hpath IH ].
  - tauto.
  - destruct (confined _ _ HF) as [Hx Hx'].
    assert (Hy : y ∈ D) by (apply IH; exact Hx').
    split; intros _; assumption.
Qed.

Lemma sticky_is_repr:
  sticky D Repr.
Proof.
  unfold sticky. intros x y [Hp _]. eapply sticky_path; eauto.
Qed.

Lemma sticky_is_equiv:
  sticky D is_equiv.
Proof.
  unfold sticky. intros x y [r [Hxr Hyr]].
  pose proof (sticky_is_repr _ _ Hxr) as Hx.
  pose proof (sticky_is_repr _ _ Hyr) as Hy.
  tauto.
Qed.

Lemma is_equiv_in_D_direct (x y : V) :
  is_equiv x y ->
  x ∈ D ->
  y ∈ D.
Proof.
  intros Heq Hx. destruct (sticky_is_equiv _ _ Heq) as [Hxy _]. apply Hxy. exact Hx.
Qed.

(* TLC proves this classically (via [not_forall_not_eq]), but here it is
   constructive: every vertex has a representative ([defined is_repr]), so a
   non-root [x] has a non-empty path to its representative, whose first edge
   [F x y] lands [x] in [D] by [confined]. *)
Lemma non_root_in_D (x: V) :
  ~ Root F x ->
  x ∈ D.
Proof.
  intros Hnroot.
  destruct (defined x) as [r [Hpath Hrootr]].
  destruct Hpath as [|x' y r' HF Hyr].
  - contradiction.
  - destruct (confined _ _ HF) as [Hx _]. exact Hx.
Qed.

Instance only_roots_outside_D (x : V) :
  x ∉ D ->
  Root F x.
Proof.
  intros Hout.
  constructor. intros y HF.
  destruct (confined _ _ HF) as [Hx _].
  contradiction.
Qed.

(* -------------------------------------------------------------------------- *)

(* If we are in a cycle and make one step, then we are still in a cycle. *)

Lemma one_step_in_a_cycle:
  forall x z,
  tc F x z ->
  x = z ->
  forall y,
  F x y ->
  tc F y y.
Proof.
  intros x z Hcycle.
  induction Hcycle.
  - intros -> y0 HFy0.
    assert (y = y0) as <- by (eapply is_dsf_functional; eauto).
    apply tc_once. assumption.
  - intros -> y0 HFy0.
    assert (y = y0) as <- by (eapply is_dsf_functional; eauto).
    eapply tc_r; eauto.
Qed.

(* Thus, a path cannot leave a cycle. *)

Lemma cannot_escape_a_cycle:
  forall x,
  tc F x x ->
  forall z,
  path F x z ->
  tc F z z.
Proof.
  intros x Hcycle z Hpath.
  revert Hcycle.
  induction Hpath as [ x | x x' z HF Hpath IH ]; intros Hcycle.
  - exact Hcycle.
  - eapply IH. eapply one_step_in_a_cycle; eauto.
Qed.

(* Thus, the fact every vertex has a representative contradicts the
   existence of a cycle. *)

Lemma acyclicity:
  forall x,
  tc F x x ->
  False.
Proof.
  intros x Hcycle.
  destruct (defined x) as [z [Hpath Hrootz]].
  pose proof (cannot_escape_a_cycle _ Hcycle _ Hpath) as Hcyclez.
  inversion Hcyclez; subst.
  - eapply a_root_has_no_parent; eauto.
  - eapply a_root_has_no_parent; eauto.
Qed.

(* If there is a non-empty path from [x] to [y], then [x] and [y] must be distinct. *)

Lemma paths_have_distinct_endpoints:
  forall x y,
  tc F x y ->
  x <> y.
Proof.
  intros x y Htc ->. eapply acyclicity; eauto.
Qed.

(* If there is an edge from [x] to [y], then [x] and [y] must be distinct. *)

Lemma edges_have_distinct_endpoints:
  forall x y,
  F x y ->
  x <> y.
Proof.
  intros x y HF. eapply paths_have_distinct_endpoints. apply tc_once. exact HF.
Qed.

(* An edge can never be followed by a path leading back to its source
   (otherwise, together with the edge, this path would form a cycle). *)

Lemma edge_no_return_path:
  forall x y,
  F x y ->
  path F y x ->
  False.
Proof.
  intros x y HF Hpath. eapply acyclicity. eapply tc_rtc_r; [apply tc_once, HF | exact Hpath].
Qed.

(* -------------------------------------------------------------------------- *)

(* Descendants. *)

(* [x] is a descendant of a root [r] iff [r] is the representative of [x]. *)

Lemma descendant_of_a_root:
  forall x r,
  Root F r ->
  (x ∈ descendants r <-> Repr x r).
Proof.
  intros x r Hroot. unfold descendants. rewrite elem_of_PropSet.
  split; [ by constructor | apply repr_path ].
Qed.

(* Two distinct roots have disjoint sets of descendants. *)

Lemma disjoint_descendants (x y : V) :
  Root F x ->
  Root F y ->
  x <> y ->
  descendants x ## descendants y.
Proof.
  intros Hx Hy Hneq v Hvx Hvy.
  rewrite (descendant_of_a_root v x Hx) in Hvx.
  rewrite (descendant_of_a_root v y Hy) in Hvy.
  exploit_functional Repr.
  contradiction.
Qed.

(* If [x] is in [D], then the set of its descendants is a subset of [D].
   (Stated pointwise rather than via [\c]/[⊆], since a [propset] and a
   [gset] aren't the same type.) *)

Lemma descendants_subset_D:
  forall x,
  x ∈ D ->
  forall v, v ∈ descendants x -> v ∈ D.
Proof.
  intros x Hx v Hv. unfold descendants in Hv. rewrite elem_of_PropSet in Hv.
  destruct (sticky_path _ _ Hv) as [_ Hbwd]. apply Hbwd. exact Hx.
Qed.

(* If a vertex [r] lies outside the domain, then a path that reaches [r]
   or leaves [r] must be trivial. (TLC's [kpath] becomes stdpp's [nsteps],
   which has the same left-recursive shape.) *)

Lemma only_trivial_paths_outside_D:
  forall k x r,
  nsteps F k x r ->
  x ∉ D \/ r ∉ D ->
  k = 0 /\ x = r.
Proof.
  intros k x r Hsteps.
  induction Hsteps as [ x | k x y r HF Hsteps IH ]; intros Hout.
  - split; reflexivity.
  - exfalso.
    destruct (confined _ _ HF) as [HxD HyD].
    pose proof (rtc_nsteps_2 _ _ _ Hsteps) as Hpathyr.
    destruct (sticky_path _ _ Hpathyr) as [Hfwd _].
    pose proof (Hfwd HyD) as HrD.
    destruct Hout as [Hout | Hout]; contradiction.
Qed.

(* If a vertex [r] lies outside the domain, then its set of descendants is
   reduced to itself. Stated with [≡] rather than [=]: comparing [propset]s
   by Leibniz equality would need an extensionality axiom we are avoiding
   for now, whereas [≡] is the pointwise-iff equivalence and needs none. *)

Lemma descendants_outside:
  forall r,
  r ∉ D ->
  descendants r ≡ {[ r ]}.
Proof.
  intros r Hout x. unfold descendants.
  rewrite elem_of_PropSet.
  rewrite elem_of_singleton.
  split.
  - intros Hpath. destruct (rtc_nsteps_1 _ _ Hpath) as [k Hsteps].
    destruct (only_trivial_paths_outside_D _ _ _ Hsteps (or_intror Hout)) as [_ Heq].
    exact Heq.
  - intros ->. apply rtc_refl.
Qed.

(* Every set of descendants is finite. ([D] is already a [gset], hence
   always finite, so unlike the original we don't need a [finite D]
   hypothesis here.) *)

Lemma finite_descendants:
  forall x,
  set_finite (descendants x).
Proof.
  intros x.
  destruct (decide (x ∈ D)) as [Hin | Hout].
  - exists D. apply descendants_subset_D. exact Hin.
  - exists {[x]}. intros v Hv. unfold descendants in Hv. rewrite elem_of_PropSet in Hv.
    destruct (rtc_nsteps_1 _ _ Hv) as [k Hsteps].
    destruct (only_trivial_paths_outside_D _ _ _ Hsteps (or_intror Hout)) as [_ Heq].
    apply elem_of_singleton_2. exact Heq.
Qed.

(* -------------------------------------------------------------------------- *)

(* Ancestors. *)

(* The ancestors of [x] are the vertices that lie along the path from [x]
   to its representative. *)

Definition ancestors x : propset V :=
  {[ y | path F x y ]}.

(* If [x] is in [D], then the set of its ancestors is a subset of [D]. *)

Lemma ancestors_subset_D:
  forall x,
  x ∈ D ->
  forall y, y ∈ ancestors x -> y ∈ D.
Proof.
  intros x Hx y Hy. unfold ancestors in Hy. rewrite elem_of_PropSet in Hy.
  destruct (sticky_path _ _ Hy) as [Hfwd _]. apply Hfwd. exact Hx.
Qed.

(* If a vertex [r] lies outside the domain, then its set of ancestors is
   reduced to itself. *)

Lemma ancestors_outside:
  forall r,
  r ∉ D ->
  ancestors r ≡ {[r]}.
Proof.
  intros r Hout x. unfold ancestors.
  rewrite elem_of_PropSet.
  rewrite elem_of_singleton.
  split.
  - intros Hpath. destruct (rtc_nsteps_1 _ _ Hpath) as [k Hsteps].
    destruct (only_trivial_paths_outside_D _ _ _ Hsteps (or_introl Hout)) as [_ Heq].
    symmetry. exact Heq.
  - intros ->. apply rtc_refl.
Qed.

(* Every set of ancestors is finite. ([D] is already a [gset], so unlike the
   original we don't need a [finite D] hypothesis here.) *)

Lemma finite_ancestors:
  forall x,
  set_finite (ancestors x).
Proof.
  intros x.
  destruct (decide (x ∈ D)) as [Hin | Hout].
  - exists D. apply ancestors_subset_D. exact Hin.
  - exists {[x]}. intros v Hv. unfold ancestors in Hv. rewrite elem_of_PropSet in Hv.
    destruct (rtc_nsteps_1 _ _ Hv) as [k Hsteps].
    destruct (only_trivial_paths_outside_D _ _ _ Hsteps (or_introl Hout)) as [_ Heq].
    apply elem_of_singleton_2. symmetry. exact Heq.
Qed.

(* If there is an edge from [x] to [y], then the ancestors of [x] are the
   union of the ancestors of [y] and [x] itself. This is a disjoint union,
   because the graph is acyclic. *)

Lemma ancestors_of_parent_inclusion:
  forall x y,
  F x y ->
  forall v, v ∈ ancestors y -> v ∈ ancestors x.
Proof.
  intros x y HF v Hv. unfold ancestors in *.
  rewrite elem_of_PropSet in Hv.
  rewrite elem_of_PropSet.
  eapply rtc_l; eauto.
Qed.

Lemma ancestors_of_parent:
  forall x y,
  F x y ->
  ancestors x ≡ ancestors y ∪ {[x]}.
Proof.
  intros x y HF v.
  unfold ancestors.
  rewrite elem_of_union.
  rewrite elem_of_PropSet.
  rewrite elem_of_PropSet.
  rewrite elem_of_singleton.
  split.
  (* An ancestor of [x] is either an ancestor of [y] or [x] itself. *)
  - intros Hpath. destruct Hpath as [ x | x x' v HF' Hpath ].
    + right. reflexivity.
    + assert (x' = y) as -> by (eapply is_dsf_functional; eauto).
      left. exact Hpath.
  (* An ancestor of [y] is an ancestor of [x], and [x] is an ancestor of itself. *)
  - intros [Hpath | ->].
    + eapply rtc_l; eauto.
    + apply rtc_refl.
Qed.

Lemma ancestors_of_parent_disjoint:
  forall x y,
  F x y ->
  x ∉ ancestors y.
Proof.
  intros x y HF Hin. unfold ancestors in Hin. rewrite elem_of_PropSet in Hin.
  eapply acyclicity. eapply tc_rtc_r.
  - apply tc_once. exact HF.
  - exact Hin.
Qed.

(* A root has no ancestors but itself. *)

Lemma ancestors_of_root (x : V) :
  Root F x ->
  ancestors x ≡ {[x]}.
Proof.
  intros Hroot v. unfold ancestors. rewrite elem_of_PropSet. rewrite elem_of_singleton.
  split.
  - intros Hpath. symmetry. eapply a_path_out_of_a_root_is_trivial; eauto.
  - intros ->. apply rtc_refl.
Qed.

(* There is at most one root ancestor. *)

Lemma at_most_one_root_ancestor (x y z : V) :
  Repr x z ->
  y ∈ ancestors x ->
  y <> z ->
  ~ Root F y.
Proof.
  intros Hxz Hy Hneq Hrooty.
  unfold ancestors in Hy. rewrite elem_of_PropSet in Hy.
  assert (Repr x y) as Hxy.
  { split; [exact Hy | exact Hrooty]. }
  exploit_functional Repr.
  contradiction.
Qed.

(* A hereditary property holds of every ancestor. *)

Lemma hereditary_property:
  forall (P : V -> Prop),
  (forall x y, P x -> F x y -> P y) ->
  forall x,
  P x ->
  forall y,
  y ∈ ancestors x ->
  P y.
Proof.
  intros P Hstep x Hx y Hy. unfold ancestors in Hy. rewrite elem_of_PropSet in Hy.
  revert Hx. induction Hy as [ x | x x' y HF Hy IH ]; intros Hx.
  - exact Hx.
  - apply IH. eapply Hstep; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The relation [is_repr] is defined and functional, so it is the graph of a
   function [R] which maps every vertex to its representative. One may wish
   to present the end user with a specification expressed in terms of [R]. *)

(* We assume that the relation [R] is given and agrees with [is_repr]. *)

Variable R : V -> V.

Class rel_incl  (f : V -> V) (Rel : relation V) :=
  { fun_in_rel : forall x, Rel x (f x) }.

Definition rel_in_fun (Rel : relation V) (f : V -> V) :=
  forall x y, Rel x y -> f x = y.

(* [Idempotent] lives in UnionFind00Update.v, next to the class-update
   algebra that rests on it, so that the concurrent development can use it
   without the disjoint-set-forest layer. *)

(* The function [R] and the relation [is_repr] coincide. *)

Hypothesis R_incl_is_repr : rel_incl R Repr.

Lemma is_repr_incl_R:
  rel_in_fun Repr R.
Proof.
  intros x y Hxy.
  pose proof (fun_in_rel x) as HRx.
  exploit_functional Repr.
  reflexivity.
Qed.

(* [x] and [y] have the same image through [R] if and only if they are
   equivalent. In other words, the relation [is_equiv] coincides with
   the relation [fun x y => R x = R y]. *)

Lemma same_R_incl_is_equiv (x y : V) :
  R x = R y ->
  is_equiv x y.
Proof.
  intros Heq.
  pose proof (fun_in_rel x) as Hx.
  pose proof (fun_in_rel y) as Hy.
  rewrite Heq in Hx.
  exists (R y). split; assumption.
Qed.

Lemma is_equiv_incl_same_R (x y : V) :
  is_equiv x y ->
  R x = R y.
Proof.
  intros [r [Hxr Hyr]].
  pose proof (is_repr_incl_R _ _ Hxr) as Hx.
  pose proof (is_repr_incl_R _ _ Hyr) as Hy.
  congruence.
Qed.

(* [x] is a root if and only if [R x = x]. *)

Lemma is_root_R_self (x : V) :
  Root F x ->
  R x = x.
Proof.
  intros Hroot.
  eapply is_repr_incl_R; eauto. apply _.
Qed.

Lemma R_self_is_root (x : V) :
  R x = x ->
  Root F x.
Proof.
  intros Heq.
  specialize (fun_in_rel x).
  rewrite Heq. apply _.
Qed.

(* [R] is the identity outside [D]. *)

Lemma R_is_identity_outside_D (x : V) :
  x ∉ D ->
  R x = x.
Proof.
  intros Hout. eapply is_root_R_self. eapply only_roots_outside_D. exact Hout.
Qed.

(* [R] is sticky. *)

Lemma sticky_R:
  forall x,
  x ∈ D ->
  R x ∈ D.
Proof.
  intros x Hx.
  pose proof (fun_in_rel x) as H.
  destruct (sticky_is_repr _ _ H) as [Hfwd _].
  apply Hfwd. exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)

End DisjointSetForest.

Arguments Repr {V} F x r.
Arguments Confined {V EqV CountableV} Dom R.
Arguments confined {V EqV CountableV Dom R Confined}.
Arguments Functional {V} R.
Arguments functional {V} R {Functional}.
Arguments Defined {V} R.
Arguments defined {V R Defined}.
Arguments DSF {V EqV CountableV} F D.

(* [R] is idempotent. *)

Global Instance idempotent_R `{@DSF V HeqV CountableV F D} R :
  rel_incl R (Repr F) →
  Idempotent R.
Proof.
  intros R_incl_is_repr.
  constructor.
  intros x.
  destruct (decide (x ∈ D)) as [Hin | Hout].
  - eapply is_root_R_self; eauto.
    eapply is_repr_is_root. eapply R_incl_is_repr.
  - f_equal.
    eapply R_is_identity_outside_D; eauto.
Qed.
