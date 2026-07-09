From osiris Require Import osiris.
From stdpp Require Import relations propset.
From Stdlib.Logic Require Import FunctionalExtensionality PropExtensionality.
Require Import UnionFind01Data UnionFind04Compress UnionFind05IteratedCompression.

(* This file supports a "framing" argument for [find]'s functional-correctness
   proof: when [find] recurses on some vertex [e'], we want to avoid handing
   over the caller's own vertex [e]'s heap cell to the recursive call (doing so
   would lose track of which record backs [e]'s content once the call
   returns). Instead we carve out of [D]/[F]/[M] the sub-structure consisting
   only of the vertices reachable from [e'] (i.e. [e']'s own path to its
   root), call [find] with that restricted view, and keep [e]'s own resources
   untouched on the side. Since [e] is never reachable from [e'] (no cycles),
   it is guaranteed not to belong to this restricted set. *)

(* Every [bw_ipc] derivation gives rise to a finite set of vertices reachable
   from its starting point, forward-closed under [F]. *)

Definition closed `{EqDecision V, Countable V} (D : gset V) (F : relation V) :=
  ∀ x y, x ∈ D → F x y → y ∈ D.

Definition restrict `{EqDecision V, Countable V} (F : relation V) (D : gset V) :=
  λ x y, F x y ∧ x ∈ D.

Lemma bw_ipc_reach_dom `{EqDecision V, Countable V} (F : relation V) :
  Functional F ->
  ∀ start lsteps Fres,
  bw_ipc F start lsteps Fres ->
  ∃ D : gset V,
    start ∈ D ∧
    (∀ x, x ∈ D -> rtc F start x) ∧
    closed D F.
Proof.
  intros Hfunc start lsteps Fres Hbw.
  induction Hbw as [ x Hroot | ].
  - exists {[x]}. split; [set_solver|]. split.
    + intros ? Hin. apply elem_of_singleton in Hin. subst. apply rtc_refl.
    + intros ? y Hin HF. apply elem_of_singleton in Hin. subst.
      exfalso. eapply Hroot. exact HF.
  - destruct IHHbw as (D2 & Hw & Hreach & Hclosed).
    exists ({[x]} ∪ D2). split; [set_solver|]. split.
    + intros ? Hin. apply elem_of_union in Hin as [Hin | Hin].
      * apply elem_of_singleton in Hin. subst. apply rtc_refl.
      * eapply rtc_l; eauto.
    + intros pa pb Hin HF. apply elem_of_union in Hin as [Hin | Hin].
      * apply elem_of_singleton in Hin. subst.
        assert (pb = y) as ->. { eapply (functional F); eauto. }
        apply elem_of_union; right; exact Hw.
      * apply elem_of_union; right; eapply Hclosed; eauto.
Qed.

(* A forward-closed subset [D2] of [D], together with [F] restricted to
   edges whose source lies in [D], is again a disjoint set forest. *)

Lemma is_dsf_restrict `{EqDecision V, Countable V} (D : gset V) (F : relation V) (D2 : gset V) :
  DSF F D ->
  D2 ⊆ D ->
  closed D2 F ->
  DSF (restrict F D2) D2.
Proof.
  intros [Hconf Hfunc Hdef] Hsub Hclosed.
  constructor; constructor.
  - intros ?? [HF Hin]. split; [exact Hin | eapply Hclosed; eauto].
  - intros ??? [HF1 _] [HF2 _]. eapply functional; eauto.
  - intros x. destruct (decide (x ∈ D2)) as [HD2|HD2]; last first.
    { exists x. split; [apply rtc_refl|].
      constructor. intros y [_ Hin]. contradiction. }
    destruct (defined x) as [r [Hpath Hrootr]].
    exists r. constructor.
    + clear Hrootr. revert HD2. induction Hpath; intros HD2.
      * apply rtc_refl.
      * eapply rtc_l. split; eauto. apply IHHpath; eauto.
    + constructor. intros y [HF _]. apply (is_root y), HF.
Qed.

(* A representative within the unrestricted relation, reached from a vertex
   inside the forward-closed set [D], remains a representative within the
   restricted relation. *)

Lemma is_repr_restrict `{EqDecision T, Countable T} (F : relation T) (D : gset T) x r :
  Repr F x r ->
  x ∈ D ->
  closed D F ->
  Repr (restrict F D) x r.
Proof.
  intros [Hpath Hroot] Hin Hclosed.
  constructor.
  - revert Hin. induction Hpath; intros Hin.
    + apply rtc_refl.
    + eapply rtc_l. split; eauto. apply IHHpath; eauto.
  - constructor. intros ? [HF _]. eapply Hroot, HF.
Qed.

(* [bw_ipc] transfers from [F] to [F] restricted to a forward-closed set
   [D] containing the starting vertex: the recursive descent performed by
   [find] never leaves [], so it never needs an edge excluded by the
   restriction. *)

Lemma bw_ipc_restrict `{EqDecision T, Countable T} (F : relation T) (D : gset T) :
  closed D F ->
  forall start lsteps Fres,
  start ∈ D ->
  bw_ipc F start lsteps Fres ->
  bw_ipc (restrict F D) start lsteps (restrict Fres D).
Proof.
  intros Hclosed start lsteps Fres Hstart Hbw.
  revert Hstart.
  induction Hbw as [ ? Hroot | ]; intros Hstart.
  - apply BWIPCBase. constructor. intros ? [HF _]. eapply Hroot, HF.
  - eapply (BWIPCStep _ x y z _ (restrict F' D)).
    + split; eassumption.
    + eapply is_repr_restrict; eauto.
    + apply IHHbw. eapply Hclosed; eauto.
    + subst F''. unfold compress. apply functional_extensionality; intro a.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; unfold restrict.
      * intros [[Hcase|Hcase] Hadom2]; tauto.
      * intros [[HF0ab Hneq]|[-> ->]]; tauto.
Qed.

(* [bw_ipc] never touches an edge whose source isn't reachable from its
   starting vertex: needed to show that the part of [F] compressed by a
   recursive call agrees with the original [F] outside the call's own
   reachable set. *)

Lemma bw_ipc_outside_unchanged `{EqDecision V, Countable V} (F : relation V) start lsteps Fres :
  bw_ipc F start lsteps Fres ->
  ∀ x, ~ rtc F start x ->
  ∀ y, Fres x y <-> F x y.
Proof.
  intros Hbw.
  induction Hbw as [x Hroot | x y z]; intros v1 Hnotreach v2.
  - tauto.
  - subst. unfold compress.
    assert (Hne : v1 <> x) by (intro Heq; subst v1; apply Hnotreach; apply rtc_refl).
    assert (Hnotreach_w : ~ rtc F y v1).
    { intro Hc. apply Hnotreach. eapply rtc_l; eassumption. }
    rewrite (IHHbw v1 Hnotreach_w v2).
    tauto.
Qed.

(* A forward-closed predicate containing the starting vertex contains every
   vertex reachable from it. *)

Lemma rtc_forward_closed_in `{EqDecision V, Countable V} (F : relation V) (D : gset V) start :
  start ∈ D ->
  closed D F ->
  ∀ x, rtc F start x -> x ∈ D.
Proof.
  intros Hstart Hclosed x Hpath.
  induction Hpath.
  - assumption.
  - apply IHHpath. eapply Hclosed; eassumption.
Qed.
