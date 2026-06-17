From osiris Require Import osiris.
From stdpp Require Import relations propset.
From Stdlib.Logic Require Import FunctionalExtensionality PropExtensionality.
Require Import UnionFind01Data UnionFind04Compress.

(* We now define an inductive predicate that encodes the process of performing
   path compression iteratively along a path, up to the root. [ipc] stands for
   ``iterative path compression''. The predicate [ipc F x l F'] means that in
   the initial state [F], performing path compression along the path that
   begins at [x] leads in [l] steps to the final state [F'].

   We define backward and forward variants of this predicate, [bw_ipc] and
   [fw_ipc]. The backward variant corresponds to the one-pass, recursive
   formulation of path compression performed by the actual OCaml [find]
   function (compression happens as the call stack is unwound). The forward
   variant corresponds to a two-pass algorithm (find the representative, then
   compress); it is easier to reason about directly, and we use it as a
   stepping stone to transport facts to [bw_ipc].

   This is a scoped-down port: we drop everything related to the amortized
   complexity analysis (ranks, time credits, [Phi]); we only keep what
   [find]'s functional correctness needs: existence of a compression witness
   ([ipc_defined]), and preservation of [is_dsf] and of the agreement between
   [R] and [is_repr] ([is_dsf_bw_ipc], [bw_ipc_preserves_RF_agreement]). *)

Inductive bw_ipc (V : Type) (F : relation V) : V -> nat -> relation V -> Prop :=
| BWIPCBase :
    forall x,
    is_root V F x ->
    bw_ipc V F x 0 F
| BWIPCStep :
    forall x y z l F' F'',
    F x y ->
    is_repr V F y z ->
    bw_ipc V F y l F' ->
    F'' = compress V F' x z ->
    bw_ipc V F x (S l) F''.

Inductive fw_ipc (V : Type) : relation V -> V -> nat -> relation V -> Prop :=
| FWIPCBase :
    forall F x,
    is_root V F x ->
    fw_ipc V F x 0 F
| FWIPCStep :
    forall F F' x y z l,
    F x y ->
    is_repr V F y z ->
    fw_ipc V (compress V F x z) y l F' ->
    fw_ipc V F x (S l) F'.

(* -------------------------------------------------------------------------- *)

(* A propositional-equality restatement of [compress_compress], obtained via
   functional and propositional extensionality. This is the one place in this
   development where we resort to extensionality, exactly as flagged in
   UnionFind.v: it is a much milder axiom than full classical logic, and it
   lets us [rewrite] across two differently-ordered compressions, which is
   unavoidable here (this commutation fact, in some form, is at the heart of
   [find]'s correctness, regardless of whether we track time complexity). *)

Lemma compress_compress_eq:
  forall V (F : relation V) (x1 z1 x2 z2 : V),
  x1 <> x2 ->
  compress V (compress V F x1 z1) x2 z2 = compress V (compress V F x2 z2) x1 z1.
Proof.
  intros V F x1 z1 x2 z2 Hneq.
  apply functional_extensionality; intro a.
  apply functional_extensionality; intro b.
  apply propositional_extensionality.
  apply compress_compress. exact Hneq.
Qed.

(* -------------------------------------------------------------------------- *)

(* Provided there is no path from [y] to [x], forward iterative compression at
   [y] commutes with one step of compression at [x]. *)

Lemma fw_ipc_compress_preliminary:
  forall V F x z y l F',
  fw_ipc V F y l F' ->
  ~ rtc F y x ->
  fw_ipc V (compress V F x z) y l (compress V F' x z).
Proof.
  intros V F x z y l F' Hfw.
  induction Hfw as [ F0 y0 Hrooty0 | F0 F0' y0 w t l0 HFy0w Hrepr Hfw0 IH ]; intros Hnopath.
  - apply FWIPCBase.
    apply compress_preserves_roots_other_than_x; [| exact Hrooty0].
    intro Heq. subst y0. apply Hnopath. apply rtc_refl.
  - assert (Hneq : x <> y0).
    { intro Heq. subst y0. apply Hnopath. apply rtc_refl. }
    assert (Hnopath_w : ~ rtc F0 w x).
    { intro Hc. apply Hnopath. eapply rtc_l; [exact HFy0w | exact Hc]. }
    assert (Hnopath_wt : ~ rtc (compress V F0 y0 t) w x).
    { intro Hc. apply Hnopath_w.
      eapply compress_preserves_paths_converse; [exact HFy0w | eapply is_repr_path; exact Hrepr | exact Hc]. }
    specialize (IH Hnopath_wt).
    eapply FWIPCStep.
    + apply compress_preserves_other_edges; [exact HFy0w | exact (not_eq_sym Hneq)].
    + apply compress_preserves_is_repr_weak; [exact Hrepr | exact Hnopath_w].
    + rewrite (compress_compress_eq V F0 x z y0 t Hneq). exact IH.
Qed.

(* A corollary of the previous lemma. *)

Lemma fw_ipc_compress:
  forall V EqV CountableV D F x y z l F',
  is_dsf V EqV CountableV D F ->
  F x y ->
  is_repr V F y z ->
  fw_ipc V F y l F' ->
  fw_ipc V (compress V F x z) y l (compress V F' x z).
Proof.
  intros V EqV CountableV D F x y z l F' Hdsf HFxy Hrepr Hfw.
  apply fw_ipc_compress_preliminary; [exact Hfw |].
  intro Hc. eapply edge_no_return_path; eauto using is_repr_path.
Qed.

(* -------------------------------------------------------------------------- *)

(* Provided there is no path from [y] to [x], backward iterative compression at
   [y] commutes with one step of un-compression at [x]. *)

Lemma bw_ipc_compress_preliminary:
  forall V (EqV : EqDecision V) Fxz y l Fxz',
  bw_ipc V Fxz y l Fxz' ->
  forall F x z,
  Fxz = compress V F x z ->
  ~ rtc F y x ->
  exists F',
  Fxz' = compress V F' x z /\
  bw_ipc V F y l F'.
Proof.
  intros V EqV Fxz y l Fxz' Hbw.
  induction Hbw as [ y0 Hrooty0 | y0 w t l0 Fxz0' Fxz2 HFxzy0w Hreprxz Hbw0 IH HeqFxz2 ];
    intros F x z -> Hnopath.
  - exists F. split; [reflexivity|].
    apply BWIPCBase. eapply (compress_preserves_roots_converse V EqV F x z y0); eauto.
  - assert (Hneq : x <> y0).
    { intro Heq. subst y0. apply Hnopath. apply rtc_refl. }
    assert (HFy0w : F y0 w).
    { eapply compress_preserves_other_edges_converse; [exact HFxzy0w | exact (not_eq_sym Hneq)]. }
    assert (Hnopath_w : ~ rtc F w x).
    { intro Hc. apply Hnopath. eapply rtc_l; [exact HFy0w | exact Hc]. }
    assert (Hreprw : is_repr V F w t).
    { eapply (compress_preserves_is_repr_weak_converse V EqV F x w); [exact Hreprxz | exact Hnopath_w]. }
    destruct (IH F x z eq_refl Hnopath_w) as [F' [Heq' Hbw']].
    exists (compress V F' y0 t). split.
    + rewrite HeqFxz2. rewrite Heq'. apply compress_compress_eq. exact Hneq.
    + eapply BWIPCStep; eauto.
Qed.

(* A corollary of the previous lemma. *)

Lemma bw_ipc_compress:
  forall V EqV CountableV D F x y z l F'',
  is_dsf V EqV CountableV D F ->
  F x y ->
  is_repr V F y z ->
  bw_ipc V (compress V F x z) y l F'' ->
  exists F',
  F'' = compress V F' x z /\
  bw_ipc V F y l F'.
Proof.
  intros V EqV CountableV D F x y z l F'' Hdsf HFxy Hrepr Hbw.
  eapply (bw_ipc_compress_preliminary V EqV (compress V F x z) y l F'' Hbw F x z eq_refl).
  intro Hc. eapply edge_no_return_path; eauto using is_repr_path.
Qed.

(* -------------------------------------------------------------------------- *)

(* Equivalence between [fw_ipc] and [bw_ipc]. *)

Lemma bw_ipc_fw_ipc:
  forall V F x l F',
  bw_ipc V F x l F' ->
  forall EqV CountableV D,
  is_dsf V EqV CountableV D F ->
  fw_ipc V F x l F'.
Proof.
  intros V F x l F' Hbw.
  induction Hbw as [ x0 Hrootx0 | x0 y0 z0 l0 F0' F0'' HFx0y0 Hrepr Hbw0 IH Heq ];
    intros EqV CountableV D Hdsf.
  - apply FWIPCBase. exact Hrootx0.
  - subst F0''. eapply FWIPCStep; eauto using fw_ipc_compress.
Qed.

Lemma fw_ipc_bw_ipc:
  forall V F x l F',
  fw_ipc V F x l F' ->
  forall EqV CountableV D,
  is_dsf V EqV CountableV D F ->
  bw_ipc V F x l F'.
Proof.
  intros V F x l F' Hfw.
  induction Hfw as [ F0 x0 Hrootx0 | F0 F0' x0 y0 z0 l0 HFx0y0 Hrepr Hfw0 IH ];
    intros EqV CountableV D Hdsf.
  - apply BWIPCBase. exact Hrootx0.
  - assert (Hdsfc : is_dsf V EqV CountableV D (compress V F0 x0 z0)).
    { eapply is_dsf_compress; eauto using is_repr_path. }
    assert (Hbwc : bw_ipc V (compress V F0 x0 z0) y0 l0 F0').
    { eapply IH; eauto. }
    destruct (bw_ipc_compress V EqV CountableV D F0 x0 y0 z0 l0 F0' Hdsf HFx0y0 Hrepr Hbwc)
      as [F' [Heq Hbw']].
    eapply BWIPCStep; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression, starting at an arbitrary vertex [x], is always
   possible. *)

Lemma ipc_defined_preliminary:
  forall V EqV CountableV D F,
  is_dsf V EqV CountableV D F ->
  forall x r,
  rtc F x r ->
  is_root V F r ->
  exists l F',
  bw_ipc V F x l F'.
Proof.
  intros V EqV CountableV D F Hdsf x r Hpath.
  induction Hpath as [ x | x x' r HFxx' Hpath IH ]; intros Hrootr.
  - exists 0, F. apply BWIPCBase. exact Hrootr.
  - destruct (IH Hrootr) as [l [F' Hbw]].
    exists (S l), (compress V F' x r).
    assert (Hreprx' : is_repr V F x' r) by (split; assumption).
    eapply BWIPCStep; eauto.
Qed.

Lemma ipc_defined:
  forall V EqV CountableV D F,
  is_dsf V EqV CountableV D F ->
  forall x,
  exists l F',
  bw_ipc V F x l F'.
Proof.
  intros V EqV CountableV D F Hdsf x.
  destruct (proj2 (proj2 Hdsf) x) as [r [Hpath Hrootr]].
  eapply ipc_defined_preliminary; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression is a composition of several path compression
   steps, so it preserves the agreement between [R] and [F]. This property
   is easy to establish for [fw_ipc], and is then transported to [bw_ipc]. *)

Lemma fw_ipc_preserves_RF_agreement:
  forall V F x l F',
  fw_ipc V F x l F' ->
  forall EqV CountableV D R,
  is_dsf V EqV CountableV D F ->
  fun_in_rel V R (is_repr V F) ->
  fun_in_rel V R (is_repr V F').
Proof.
  intros V F x l F' Hfw.
  induction Hfw as [ F0 x0 Hrootx0 | F0 F0' x0 y0 z0 l0 HFx0y0 Hrepr Hfw0 IH ];
    intros EqV CountableV D R Hdsf HR.
  - exact HR.
  - eapply IH.
    + eapply is_dsf_compress; [exact HFx0y0 | exact Hdsf | eapply is_repr_path; exact Hrepr].
    + eapply compress_R_compress_agree; [exact HFx0y0 | exact Hdsf | eapply is_repr_path; exact Hrepr | exact HR].
Qed.

Lemma bw_ipc_preserves_RF_agreement:
  forall V F x l F',
  bw_ipc V F x l F' ->
  forall EqV CountableV D R,
  is_dsf V EqV CountableV D F ->
  fun_in_rel V R (is_repr V F) ->
  fun_in_rel V R (is_repr V F').
Proof.
  intros V F x l F' Hbw EqV CountableV D R Hdsf HR.
  eapply fw_ipc_preserves_RF_agreement; eauto using bw_ipc_fw_ipc.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression preserves [is_dsf] (we don't track ranks, so
   this is the bare disjoint-set-forest fact, without the "is_rdsf" rank
   side-conditions the original development also tracked here). *)

Lemma is_dsf_fw_ipc:
  forall V F x l F',
  fw_ipc V F x l F' ->
  forall EqV CountableV D,
  is_dsf V EqV CountableV D F ->
  x ∈ D ->
  is_dsf V EqV CountableV D F'.
Proof.
  intros V F x l F' Hfw.
  induction Hfw as [ F0 x0 Hrootx0 | F0 F0' x0 y0 z0 l0 HFx0y0 Hrepr Hfw0 IH ];
    intros EqV CountableV D Hdsf HxD.
  - exact Hdsf.
  - eapply IH; [eapply is_dsf_compress; eauto using is_repr_path |].
    destruct Hdsf as [Hconf _]. eapply (proj2 (Hconf x0 y0 HFx0y0)).
Qed.

Lemma is_dsf_bw_ipc:
  forall V F x l F',
  bw_ipc V F x l F' ->
  forall EqV CountableV D,
  is_dsf V EqV CountableV D F ->
  x ∈ D ->
  is_dsf V EqV CountableV D F'.
Proof.
  intros V F x l F' Hbw EqV CountableV D Hdsf HxD.
  eapply is_dsf_fw_ipc; eauto using bw_ipc_fw_ipc.
Qed.
