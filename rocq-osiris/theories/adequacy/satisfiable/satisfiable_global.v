From iris.prelude Require Import options.
From stdpp Require Import gmap.
From iris.base_logic Require Export iprop.
From iris.base_logic Require Import own.
From iris.proofmode Require Import ltac_tactics.
From osiris.adequacy.satisfiable Require Import satisfiable_standard.

From iris.algebra Require Import functions gmap.


(** To define a notion of satisfiable for iProp that allows arbitrary
  global resources to be allocatd initially, we define a predicate
  [allocated G P] and define [sat_global P] in terms of [allocated]. *)
Definition allocated {Σ} (G: gset gname) (P: iProp Σ): Prop :=
  (∃ m: iResUR Σ, ✓ m ∧ (∀ i, dom (m i) ⊆ G) ∧ (uPred_ownM m ⊢ P)).

Section allocated.
Context {Σ: gFunctors}.

Lemma allocated_empty : allocated ∅ (True%I: iProp Σ).
Proof.
  exists ε; split; first done.
  split; first done.
  apply bi.True_intro.
Qed.

Lemma allocated_own `{!inG Σ A} (γ : gname) (a : A):
  ✓ a → allocated {[ γ ]} (own γ a).
Proof.
  intros Hv. exists (own.iRes_singleton γ a). split; [|split].
  - apply cmra_valid_validN=> n.
    rewrite /own.iRes_singleton.
    eapply discrete_fun_singleton_validN.
    eapply singleton_validN.
    eapply own.inG_unfold_validN.
    eapply cmra_transport_validN.
    by eapply cmra_valid_validN.
  - intros i γ'. rewrite /own.iRes_singleton /discrete_fun_singleton /discrete_fun_insert.
    destruct decide.
    + destruct e; simpl. by rewrite dom_singleton.
    + naive_solver.
  - by rewrite own.own_eq /own.own_def.
Qed.

Lemma allocated_combine G1 G2 (P Q: iProp Σ):
  allocated G1 P → allocated G2 Q → G1 ## G2 → allocated (G1 ∪ G2) (P ∗ Q)%I.
Proof.
  intros (m1 & V1 & H1 & HP) (m2 & V2 & H2 & HQ) G12.
  exists (λ i, m1 i ⋅ m2 i). split; [|split].
  - intros i γ. rewrite lookup_op.
    specialize (H1 i). specialize (H2 i).
    destruct (m1 i !! γ) as [r|] eqn: EQ1; first destruct (m2 i !! γ) as [r'|] eqn: EQ2.
    + assert (γ ∈ dom (m1 i)) by by apply (elem_of_dom_2 (m1 i) γ r).
      assert (γ ∈ dom (m2 i)) by by apply (elem_of_dom_2 (m2 i) γ r' (D := (gset gname))).
      set_solver.
    + rewrite EQ2 right_id. apply V1.
    + rewrite EQ1 left_id. apply V2.
  - intros i. rewrite dom_op. set_solver.
  - by rewrite uPred.ownM_op HP HQ.
Qed.

Lemma allocated_mono G (P Q: iProp Σ):
  (P ⊢ Q) → allocated G P → allocated G Q.
Proof.
  intros PQ (m & V & H & HP).
  exists m; split; last split; eauto.
  by rewrite HP PQ.
Qed.

Lemma allocated_sat G (P: iProp Σ):
  allocated G P → sat_standard P.
Proof.
  intros (m & V & _ & HP); simpl.
  eapply sat_standard_mono; [apply HP|].
  by eapply sat_standard_valid_own.
Qed.

(* derived *)
Lemma allocated_own_fresh G (P: iProp Σ) {A: cmra} (a: A) `{!inG Σ A}:
  allocated G P → ✓ a → ∃ γ, allocated (G ∪ {[γ]}) (P ∗ own γ a).
Proof.
  intros Halloc Hv. exists (fresh G).
  apply allocated_combine; first done.
  - by apply allocated_own.
  - apply disjoint_singleton_r, is_fresh.
Qed.

End allocated.


(** *** Satisfiable for Allocation of Global Resources *)
Definition sat_global {Σ} (P: iProp Σ) :=
  ∃ G n, allocated G (Nat.iter n (λ P, |==> ▷ P)%I P).


Section satisfiable_global.
  Context {Σ: gFunctors}.

  Lemma sat_global_intro :
    sat_global (Σ := Σ) True.
  Proof.
    exists ∅, 0. by apply allocated_empty.
  Qed.

  Lemma sat_global_mono (P Q: iProp Σ) :
    (P ⊢ Q) → sat_global P → sat_global Q.
  Proof.
    intros HPQ (G & n & Hs). exists G, n.
    eapply allocated_mono; last done. clear Hs.
    iInduction n as [|n] "IH"; simpl; first by iApply HPQ.
    iIntros "H". iMod "H". iModIntro. iNext. by iApply "IH".
  Qed.

  Lemma sat_global_upd (P: iProp Σ) :
    sat_global (|==> P) → sat_global P.
  Proof.
    intros (G & n & Hs). exists G, (S n).
    eapply allocated_mono; last done.
    rewrite Nat.iter_succ_r. simpl. clear Hs.
    iInduction n as [|n] "IH"; simpl; first by rewrite -bi.later_intro; iIntros "$".
    iIntros "H". iMod "H". iModIntro. iNext. by iApply "IH".
  Qed.

  Lemma sat_global_later (P: iProp Σ) :
    sat_global (▷ P) → sat_global P.
  Proof.
    intros (G & n & Hs). exists G, (S n).
    eapply allocated_mono; last done.
    rewrite Nat.iter_succ_r. simpl. clear Hs.
    iInduction n as [|n] "IH"; simpl; first by rewrite -bupd_intro; iIntros "$".
    iIntros "H". iMod "H". iModIntro. iNext. by iApply "IH".
  Qed.

  Lemma sat_global_elim φ :
    sat_global (⌜φ⌝: iProp Σ)%I → φ.
  Proof.
    intros (G & n & Hs).
    eapply allocated_sat in Hs.
    induction n as [|n IHn].
    - simpl in Hs. eapply sat_standard_elim, Hs.
    - eapply IHn. eapply sat_standard_later, sat_standard_upd, Hs.
  Qed.

  Lemma sat_global_alloc_res {A: cmra} `{!inG Σ A} (a: A) P:
    ✓ a → sat_global P → ∃ γ, sat_global (own γ a ∗ P).
  Proof.
    intros Hv (G & n & Halloc).
    edestruct (@allocated_own_fresh Σ G) as [γ Ha]; [done..|].
    eexists γ, _, n. eapply allocated_mono, Ha.
    clear. clear Halloc.
    iInduction n as [|n] "IH"; simpl; first by iIntros "[$ $]".
    iIntros "[H Hown]". iMod "H". iModIntro. iNext. iApply "IH". iFrame.
  Qed.

  Lemma sat_global_sat (P: iProp Σ) :
    sat_global P → sat_standard P.
  Proof.
    intros (G & n & Hs).
    eapply allocated_sat in Hs.
    induction n as [|n IH]; simpl in *.
    - done.
    - eapply IH. eapply sat_standard_later, sat_standard_upd, Hs.
  Qed.

End satisfiable_global.
