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

Lemma bw_ipc_reach_dom :
  forall T (EqT : EqDecision T) (CountableT : Countable T) (Frel : relation T),
  functional T Frel ->
  forall ystart lsteps Fres,
  bw_ipc T Frel ystart lsteps Fres ->
  exists D2 : gset T,
    ystart ∈ D2 /\
    (forall pa, pa ∈ D2 -> rtc Frel ystart pa) /\
    (forall pa pb, pa ∈ D2 -> Frel pa pb -> pb ∈ D2).
Proof.
  intros T EqT CountableT Frel Hfunc ystart lsteps Fres Hbw.
  induction Hbw as [y0 Hroot | y0 w z l0 F0 F0' HFy0w Hrepr Hbw0 IH HFeq].
  - exists {[y0]}. split; [set_solver|]. split.
    + intros pa Ha. apply elem_of_singleton in Ha. subst pa. apply rtc_refl.
    + intros pa pb Ha HFab. apply elem_of_singleton in Ha. subst pa.
      exfalso. eapply Hroot. exact HFab.
  - destruct IH as (D2' & Hw & Hreach & Hclosed).
    exists ({[y0]} ∪ D2'). split; [set_solver|]. split.
    + intros pa Ha. apply elem_of_union in Ha as [Ha | Ha].
      * apply elem_of_singleton in Ha. subst pa. apply rtc_refl.
      * eapply rtc_l; [exact HFy0w | exact (Hreach pa Ha)].
    + intros pa pb Ha HFab. apply elem_of_union in Ha as [Ha | Ha].
      * apply elem_of_singleton in Ha. subst pa.
        assert (pb = w) as -> by (eapply Hfunc; eauto).
        apply elem_of_union; right; exact Hw.
      * apply elem_of_union; right; eapply Hclosed; eauto.
Qed.

(* A forward-closed subset [Dom2] of [Dom], together with [F] restricted to
   edges whose source lies in [Dom2], is again a disjoint set forest. *)

Lemma is_dsf_restrict :
  forall T (EqT : EqDecision T) (CountableT : Countable T) (Dom : gset T) (Frel : relation T) (Dom2 : gset T),
  is_dsf T EqT CountableT Dom Frel ->
  Dom2 ⊆ Dom ->
  (forall pa pb, pa ∈ Dom2 -> Frel pa pb -> pb ∈ Dom2) ->
  is_dsf T EqT CountableT Dom2 (fun pa pb => Frel pa pb /\ pa ∈ Dom2).
Proof.
  intros T EqT CountableT Dom Frel Dom2 [Hconf [Hfunc Hdef]] Hsub Hclosed.
  split; [|split].
  - intros pa pb [HF Ha]. split; [exact Ha | eapply Hclosed; eauto].
  - intros pa pb1 pb2 [HF1 _] [HF2 _]. eapply Hfunc; eauto.
  - intros pa. destruct (decide (pa ∈ Dom2)) as [HaDom2|HaDom2]; last first.
    { exists pa. split; [apply rtc_refl|]. intros pb [_ Ha]. exact (HaDom2 Ha). }
    assert (Hpa_Dom : pa ∈ Dom) by (eapply Hsub; eauto).
    destruct (Hdef pa) as [r [Hpath Hrootr]].
    assert (Hpath2 : rtc (fun pa0 pb0 => Frel pa0 pb0 /\ pa0 ∈ Dom2) pa r).
    { clear Hrootr. revert HaDom2. induction Hpath as [pa0 | pa0 pa1 r0 HF0 Hpath0 IH]; intros HaDom2.
      - apply rtc_refl.
      - assert (pa1 ∈ Dom2) by (eapply Hclosed; eauto).
        eapply rtc_l; [split; eauto | apply IH; eauto]. }
    exists r. split; [exact Hpath2|].
    intros pb [HFrb _]. eapply Hrootr; exact HFrb.
Qed.

(* A representative within the unrestricted relation, reached from a vertex
   inside the forward-closed set [Dom2], remains a representative within the
   restricted relation. *)

Lemma is_repr_restrict :
  forall T (EqT : EqDecision T) (CountableT : Countable T) (Frel : relation T) (Dom2 : gset T) pv pr,
  is_repr T Frel pv pr ->
  pv ∈ Dom2 ->
  (forall pa pb, pa ∈ Dom2 -> Frel pa pb -> pb ∈ Dom2) ->
  is_repr T (fun pa pb => Frel pa pb /\ pa ∈ Dom2) pv pr.
Proof.
  intros T EqT CountableT Frel Dom2 pv pr [Hpath Hrootr] HvDom2 Hclosed.
  split.
  - revert HvDom2. induction Hpath as [pv0 | pv0 pv1 pr0 HF0 Hpath0 IH]; intros HvDom2.
    + apply rtc_refl.
    + assert (pv1 ∈ Dom2) by (eapply Hclosed; eauto).
      eapply rtc_l; [split; eauto | apply IH; eauto].
  - intros pb [HFrb _]. eapply Hrootr; exact HFrb.
Qed.

(* [Mem] and [pointsto_M] are specific to UnionFind.v (they're stated over
   [elem := loc] and Osiris's [pointsto_M]/[lcontent]), so the analogous
   restriction/splitting lemmas for them live in UnionFind.v itself, next to
   their definitions, rather than here. *)

(* [bw_ipc] transfers from [F] to [F] restricted to a forward-closed set
   [Dom2] containing the starting vertex: the recursive descent performed by
   [find] never leaves [Dom2], so it never needs an edge excluded by the
   restriction. *)

Lemma bw_ipc_restrict :
  forall T (EqT : EqDecision T) (CountableT : Countable T) (Frel : relation T) (Dom2 : gset T),
  (forall pa pb, pa ∈ Dom2 -> Frel pa pb -> pb ∈ Dom2) ->
  forall ystart lsteps Fres,
  ystart ∈ Dom2 ->
  bw_ipc T Frel ystart lsteps Fres ->
  bw_ipc T (fun pa pb => Frel pa pb /\ pa ∈ Dom2) ystart lsteps
    (fun pa pb => Fres pa pb /\ pa ∈ Dom2).
Proof.
  intros T EqT CountableT Frel Dom2 Hclosed ystart lsteps Fres HystartDom2 Hbw.
  revert HystartDom2.
  induction Hbw as [y0 Hroot | y0 w z l0 F0 F0' HFy0w Hrepr Hbw0 IH HFeq]; intros HystartDom2.
  - apply BWIPCBase. intros pb [HFpb _]. eapply Hroot; exact HFpb.
  - assert (HwDom2 : w ∈ Dom2) by (eapply Hclosed; eauto).
    eapply (BWIPCStep T _ y0 w z l0 (fun pa pb => F0 pa pb /\ pa ∈ Dom2)).
    + split; assumption.
    + eapply is_repr_restrict; eauto.
    + apply IH; exact HwDom2.
    + subst F0'. unfold compress. apply functional_extensionality; intro a.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split.
      * intros [[Hcase|Hcase] Hadom2]; tauto.
      * intros [[HF0ab Hneq]|[-> ->]].
        all: tauto.
Qed.

(* [bw_ipc] never touches an edge whose source isn't reachable from its
   starting vertex: needed to show that the part of [F] compressed by a
   recursive call agrees with the original [F] outside the call's own
   reachable set. *)

Lemma bw_ipc_outside_unchanged :
  forall T (EqT : EqDecision T) (CountableT : Countable T) (Frel : relation T) ystart lsteps Fres,
  bw_ipc T Frel ystart lsteps Fres ->
  forall pa, ~ rtc Frel ystart pa ->
  forall pb, Fres pa pb <-> Frel pa pb.
Proof.
  intros T EqT CountableT Frel ystart lsteps Fres Hbw.
  induction Hbw as [y0 Hroot | y0 w z l0 F0 F0' HFy0w Hrepr Hbw0 IH HFeq]; intros pa Hnotreach pb.
  - tauto.
  - subst F0'. unfold compress.
    assert (Hpa_ne_y0 : pa <> y0) by (intro Heq; subst pa; apply Hnotreach; apply rtc_refl).
    assert (Hnotreach_w : ~ rtc Frel w pa).
    { intro Hc. apply Hnotreach. eapply rtc_l; [exact HFy0w | exact Hc]. }
    rewrite (IH pa Hnotreach_w pb).
    tauto.
Qed.

(* A forward-closed predicate containing the starting vertex contains every
   vertex reachable from it. *)

Lemma rtc_forward_closed_in :
  forall T (Frel : relation T) (Dom2 : T -> Prop) ystart,
  Dom2 ystart ->
  (forall pa pb, Dom2 pa -> Frel pa pb -> Dom2 pb) ->
  forall pa, rtc Frel ystart pa -> Dom2 pa.
Proof.
  intros T Frel Dom2 ystart Hystart Hclosed pa Hpath.
  induction Hpath as [pa0 | pa0 pa1 pa2 HF01 Hpath01 IH].
  - exact Hystart.
  - apply IH. eapply Hclosed; [exact Hystart | exact HF01].
Qed.
