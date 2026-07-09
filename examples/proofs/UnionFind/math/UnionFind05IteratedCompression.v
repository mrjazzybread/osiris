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
   stepping stone to transport facts to [bw_ipc]. *)

Inductive bw_ipc {V : Type} (F : relation V) : V -> nat -> relation V -> Prop :=
| BWIPCBase :
    forall x,
    Root F x ->
    bw_ipc F x 0 F
| BWIPCStep :
    forall x y z l F' F'',
    F x y ->
    Repr F y z ->
    bw_ipc F y l F' ->
    F'' = compress F' x z ->
    bw_ipc F x (S l) F''.

Inductive fw_ipc {V : Type} : relation V -> V -> nat -> relation V -> Prop :=
| FWIPCBase :
    forall F x,
    Root F x ->
    fw_ipc F x 0 F
| FWIPCStep :
    forall F F' x y z l,
    F x y ->
    Repr F y z ->
    fw_ipc (compress F x z) y l F' ->
    fw_ipc F x (S l) F'.

(* -------------------------------------------------------------------------- *)

(* A propositional-equality restatement of [compress_compress], obtained via
   functional and propositional extensionality. *)

Lemma compress_compress_eq {V : Type} (F : relation V) (x1 z1 x2 z2 : V) :
  x1 <> x2 ->
  compress (compress F x1 z1) x2 z2 = compress (compress F x2 z2) x1 z1.
Proof.
  intros Hneq.
  apply functional_extensionality; intro a.
  apply functional_extensionality; intro b.
  apply propositional_extensionality.
  apply compress_compress. exact Hneq.
Qed.

(* -------------------------------------------------------------------------- *)

(* Provided there is no path from [y] to [x], forward iterative compression at
   [y] commutes with one step of compression at [x]. *)

Lemma fw_ipc_compress_preliminary {V : Type} F x z y l (F' : relation V) :
  fw_ipc F y l F' ->
  ~ rtc F y x ->
  fw_ipc (compress F x z) y l (compress F' x z).
Proof.
  intros Hfw.
  induction Hfw as [ F0 y0 Hrooty0 | F0 F0' y0 w t l0 HFy0w Hrepr Hfw0 IH ]; intros Hnopath.
  - apply FWIPCBase.
    apply compress_preserves_roots_other_than_x; [| exact Hrooty0].
    intro Heq. subst y0. apply Hnopath. apply rtc_refl.
  - assert (Hneq : x <> y0).
    { intro Heq. subst y0. apply Hnopath. apply rtc_refl. }
    assert (Hnopath_w : ~ rtc F0 w x).
    { intro Hc. apply Hnopath. eapply rtc_l; [exact HFy0w | exact Hc]. }
    assert (Hnopath_wt : ~ rtc (compress F0 y0 t) w x).
    { intro Hc. apply Hnopath_w.
      eapply compress_preserves_paths_converse; [exact HFy0w | eapply repr_path; exact Hrepr | exact Hc]. }
    specialize (IH Hnopath_wt).
    eapply FWIPCStep.
    + apply compress_preserves_other_edges; [exact HFy0w | exact (not_eq_sym Hneq)].
    + apply compress_preserves_is_repr_weak; [exact Hrepr | exact Hnopath_w].
    + rewrite (compress_compress_eq F0 x z y0 t Hneq). exact IH.
Qed.

(* A corollary of the previous lemma. *)

Lemma fw_ipc_compress `{EqDecision V, Countable V} (F : relation V) D x y z l (F' : relation V) :
  DSF F D ->
  F x y ->
  Repr F y z ->
  fw_ipc F y l F' ->
  fw_ipc (compress F x z) y l (compress F' x z).
Proof.
  intros Hdsf HFxy Hrepr Hfw.
  apply fw_ipc_compress_preliminary; [exact Hfw |].
  intro Hc. eapply edge_no_return_path; eauto using repr_path.
Qed.

(* -------------------------------------------------------------------------- *)

(* Provided there is no path from [y] to [x], backward iterative compression at
   [y] commutes with one step of un-compression at [x]. *)

Lemma bw_ipc_compress_preliminary `{EqDecision V} (Fxz : relation V) y l (Fxz' : relation V) :
  bw_ipc Fxz y l Fxz' ->
  ∀ F x z,
  Fxz = compress F x z ->
  ~ rtc F y x ->
  ∃ F',
  Fxz' = compress F' x z /\
  bw_ipc F y l F'.
Proof.
  intros Hbw.
  induction Hbw as [ y Hrooty | y w t l0 Fxz0' Fxz2 HFxzy0w Hreprxz Hbw0 IH HeqFxz2 ];
    intros F x z -> Hnopath.
  - exists F. split; [reflexivity|].
    apply BWIPCBase. eapply (compress_preserves_roots_converse x z y); eauto.
  - assert (x ≠ y) as Hneq.
    { intros Heq. subst y. apply Hnopath. apply rtc_refl. }
    assert (F y w) as y_edge_w.
    { eapply compress_preserves_other_edges_converse; eauto. }
    assert (¬ rtc F w x) as Hnopath_w.
    { intros Hc. apply Hnopath. eapply rtc_l; eauto. }
    destruct (IH F x z eq_refl Hnopath_w) as [F' [Heq' Hbw']].
    exists (compress F' y t). split.
    + rewrite HeqFxz2. rewrite Heq'. apply compress_compress_eq. exact Hneq.
    + eapply BWIPCStep; eauto.
      eapply compress_preserves_is_repr_weak_converse; eauto.
Qed.

(* A corollary of the previous lemma. *)

Lemma bw_ipc_compress `{EqDecision V, Countable V} D (F : relation V) x y z l F'' :
  DSF F D ->
  F x y ->
  Repr F y z ->
  bw_ipc (compress F x z) y l F'' ->
  ∃ F',
  F'' = compress F' x z ∧
  bw_ipc F y l F'.
Proof.
  intros Hdsf HFxy Hrepr Hbw.
  eapply bw_ipc_compress_preliminary; eauto.
  intro Hc. eapply edge_no_return_path; eauto using repr_path.
Qed.

(* -------------------------------------------------------------------------- *)

(* Equivalence between [fw_ipc] and [bw_ipc]. *)

Lemma bw_ipc_fw_ipc `{EqDecision V, Countable V} (F : relation V) D x l F' :
  bw_ipc F x l F' ->
  DSF F D ->
  fw_ipc F x l F'.
Proof.
  intros Hbw.
  induction Hbw as [ x Hrootx | ];
    intros Hdsf.
  - apply FWIPCBase. exact Hrootx.
  - subst. eapply FWIPCStep; eauto using fw_ipc_compress.
Qed.

Lemma fw_ipc_bw_ipc `{EqDecision V, Countable V} (F : relation V) D x l F' :
  fw_ipc F x l F' ->
  DSF F D ->
  bw_ipc F x l F'.
Proof.
  intros Hfw.
  induction Hfw as [ ? x Hrootx | ];
    intros Hdsf.
  - apply BWIPCBase. exact Hrootx.
  - edestruct (bw_ipc_compress D F) as [F'' [Heq Hbw']]; eauto.
    + eapply IHHfw; eauto.
      eapply is_dsf_compress; eauto using repr_path.
    + eapply BWIPCStep; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression, starting at an arbitrary vertex [x], is always
   possible. *)

Lemma ipc_defined_preliminary `{EqDecision V, Countable V} D (F : relation V) x r:
  DSF F D ->
  rtc F x r ->
  Root F r ->
  ∃ l F',
  bw_ipc F x l F'.
Proof.
  intros Hdsf Hpath.
  induction Hpath as [ x | x x' r HFxx' Hpath IH ]; intros Hrootr.
  - exists 0, F. apply BWIPCBase. exact Hrootr.
  - destruct (IH Hrootr) as [l [F' Hbw]].
    exists (S l), (compress F' x r).
    eapply BWIPCStep; eauto.
    constructor; assumption.
Qed.

Lemma ipc_defined `{EqDecision V, Countable V} D (F : relation V) x :
  DSF F D ->
  ∃ l F',
  bw_ipc F x l F'.
Proof.
  intros Hdsf.
  pose proof Hdsf as [_ _ Hdefined].
  destruct (defined x) as [r [Hpat Hrootr]].
  eapply ipc_defined_preliminary; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression is a composition of several path compression
   steps, so it preserves the agreement between [R] and [F]. This property
   is easy to establish for [fw_ipc], and is then transported to [bw_ipc]. *)

Lemma fw_ipc_preserves_RF_agreement `{EqDecision V, Countable V} (F : relation V) D x l F' R :
  fw_ipc F x l F' ->
  DSF F D ->
  fun_in_rel R (Repr F) ->
  fun_in_rel R (Repr F').
Proof.
  intros Hfw.
  induction Hfw as [ ? x Hrootx | ];
    intros Hdsf HR.
  - exact HR.
  - eapply IHHfw.
    + eapply is_dsf_compress; eauto using repr_path.
    + eapply compress_R_compress_agree; eauto using repr_path.
Qed.

Lemma bw_ipc_preserves_RF_agreement `{EqDecision V, Countable V} (F : relation V) D x l F' R :
  bw_ipc F x l F' ->
  DSF F D ->
  fun_in_rel R (Repr F) ->
  fun_in_rel R (Repr F').
Proof.
  intros Hbw Hdsf HR.
  eapply fw_ipc_preserves_RF_agreement; eauto using bw_ipc_fw_ipc.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression preserves [is_dsf] (we don't track ranks, so
   this is the bare disjoint-set-forest fact, without the "is_rdsf" rank
   side-conditions the original development also tracked here). *)

Lemma is_dsf_fw_ipc `{EqDecision V, Countable V} (F : relation V) D x l F' :
  fw_ipc F x l F' ->
  DSF F D ->
  x ∈ D ->
  DSF F' D.
Proof.
  intros Hfw.
  induction Hfw as [ ? x Hrootx | ];
    intros Hdsf HxD.
  - exact Hdsf.
  - eapply IHHfw; [eapply is_dsf_compress; eauto using repr_path |].
    destruct Hdsf as [Hconf _ _].
    eapply confined; eassumption.
Qed.

Lemma is_dsf_bw_ipc `{EqDecision V, Countable V} (F : relation V) D x l F' :
  bw_ipc F x l F' ->
  DSF F D ->
  x ∈ D ->
  DSF F' D.
Proof.
  intros Hbw Hdsf HxD.
  eapply is_dsf_fw_ipc; eauto using bw_ipc_fw_ipc.
Qed.
