From iris.prelude Require Import options.
From iris.base_logic Require Import own wsat invariants.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import ltac_tactics.

Require Import satisfiable.

(** *** Satisfiability and Later Credits *)
(** We provide lemmas for
  - allocating the initial credit supply
  - allocating new credits along the way
  - eliminating the later elimination update

  These lemmas should eventually be moved into the later credits library.
*)


(* Helper Lemmas and Definitions *)
Import later_credits.le_upd.
Import later_credits.le_upd_if.
Definition supply `{!lcGS Σ} (n: nat): iProp Σ := later_credits.lc_supply n.

Local Lemma lc_increase_supply `{!lcGS Σ} k n: supply n ⊢ |==> supply (n + k) ∗ £ k.
Proof.
  rewrite /supply later_credits.lc_supply_unseal later_credits.lc_unseal.
  rewrite /later_credits.lc_supply_def /later_credits.lc_def.
  iIntros "Hc". iMod (own_update with "Hc") as "Hc"; last first.
  { iModIntro. iDestruct "Hc" as "($ & $)". }
  apply auth_update_alloc. eapply nat_local_update.
  rewrite right_id //.
Qed.

Local Lemma lc_elim_upd `{!lcGS Σ} n P:
  (supply n ∗ |==£> P)%I ⊢ Nat.iter n (λ P, (|==> ▷ P))%I (|==> ◇ |==> (supply n ∗ P))%I.
Proof.
  iIntros "[Hc Hupd]". iPoseProof (le_upd_elim with "Hc Hupd") as "Hx".
  iApply (bi.iter_modal_mono with "[] Hx").
  - intros Q R. iIntros "HPQ HQ". iMod "HQ". iModIntro. iNext. by iApply "HPQ".
  - iIntros "Hupd". iMod "Hupd". iModIntro. iMod "Hupd". iModIntro.
    iDestruct ("Hupd") as "(%m & %Hle & Hs & $)". iMod (lc_increase_supply (n - m) with "Hs") as "[Hs _]".
    iModIntro. rewrite -Nat.le_add_sub //.
Qed.



(* Satisfiability Lemmas *)
Lemma SAT_alloc_later_credits `{!lcGpreS Σ} F P:
  SAT Alloc F [] P →
  ∃ _: lcGS Σ, SAT Alloc F [supply 0] P.
Proof.
  Local Existing Instances lcGpreS_inG.
  intros Hsat. destruct (SAT_alloc_res (● 0: authR natUR) F [] P) as [γ Hsat'].
  - by apply auth_auth_valid.
  - done.
  - exists (LcGS _ _ γ). rewrite SAT_res_cons.
    rewrite /supply later_credits.lc_supply_unseal //.
Qed.

Lemma SAT_later_credits_increase `{!lcGS Σ} m F n k P:
  SAT m F [supply n] P →
  SAT m F [supply (n + k)] (£ k ∗ P).
Proof.
  rewrite !SAT_res_cons. intros Hsat. eapply SAT_upd, SAT_mono, Hsat.
  iIntros "[Hc $]". by iApply (lc_increase_supply with "Hc").
Qed.

Lemma SAT_later_credits_credit_wand `{!lcGS Σ} m F n k P:
  SAT m F [supply n] (£ k -∗ P) →
  SAT m F [supply (n + k)] P.
Proof.
  intros Hsat. eapply SAT_mono, SAT_later_credits_increase, Hsat.
  iIntros "[Hc HP]". by iApply "HP".
Qed.

Lemma SAT_later_credits_upd_elim `{!lcGS Σ} m F n P:
  SAT m F [supply n] (|==£> P) →
  SAT m F [supply n] P.
Proof.
  rewrite !SAT_res_cons. intros Hsat. eapply SAT_mono in Hsat; last apply lc_elim_upd.
  eapply SAT_elim_iterated in Hsat; last first.
  { intros Q Hsat'. eapply SAT_later, SAT_upd, Hsat'. }
  eapply SAT_upd, SAT_except_0, SAT_upd, Hsat.
Qed.




(** *** Satisfiability and Fancy Updates *)
(** We provide lemmas for
  - allocating the initial view [⊤]
  - eliminating fancy updates by updating the view

  These lemmas should eventually be moved into the fancy update machinery of Iris.
  They depend on later credits having been allocated already.
*)
Definition view `{!wsatGS Σ} (E: coPset): iProp Σ := wsat ∗ ownE E.

Lemma SAT_alloc_world_satisfaction `{!wsatGpreS Σ} F P:
  SAT Alloc F [] P →
  ∃ _: wsatGS Σ, SAT Alloc F [view ⊤] P.
Proof.
  Local Existing Instances wsatGpreS_inv wsatGpreS_enabled wsatGpreS_disabled.
  intros Hsat.
  eapply (SAT_alloc_res (gmap_view_auth (DfracOwn 1) ∅)) in Hsat as [γI Hsat]; last first.
  { by apply gmap_view_auth_valid. }
  eapply (SAT_alloc_res (CoPset ⊤)) in Hsat as [γE Hsat]; last done.
  eapply (SAT_alloc_res (GSet ∅)) in Hsat as [γD Hsat]; last done.
  exists (WsatG _ _ γI γE γD). rewrite SAT_res_cons.
  eapply SAT_mono, Hsat. rewrite /view /wsat /ownE -!lock.
  iIntros "(HD & HE & HI & $)"; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.


(** We combine the allocation of world satisfaction and the later credit supply,
    following the current structure of Iris.                                    *)
Lemma SAT_alloc_fancy_updates `{!invGpreS Σ} F P (HL : has_lc) :
  SAT Alloc F [] P →
  ∃ _: invGS_gen HL Σ, SAT Alloc F [view ⊤; supply 0] P.
Proof.
  Local Existing Instances invGpreS_wsat invGpreS_lc.
  intros Hsat.
  destruct (SAT_alloc_world_satisfaction F P Hsat) as [Hwsat Hsat'].
  eapply (SAT_frame_resource _ (view ⊤)) in Hsat'; last apply _.
  destruct (SAT_alloc_later_credits _ P Hsat') as [Hlc Hsat''].
  eapply SAT_unframe_resource in Hsat''.
  by exists (InvG _ _ Hwsat Hlc).
Qed.

Lemma SAT_fupd `{!invGS_gen H Σ} E1 E2 m n F P:
  SAT m F [view E1; supply n] (|={E1,E2}=> P) →
  SAT m F [view E2; supply n] P.
Proof.
  rewrite SAT_res_cons. intros Hsat. rewrite SAT_res_cons.
  eapply SAT_except_0, SAT_later_credits_upd_elim, SAT_mono, Hsat.
  iIntros "[Hview HP]".
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
  rewrite /view /le_upd_if /= -bi.sep_assoc //.
  destruct H.
  - by iApply "HP".
  - iMod ("HP" with "Hview") as "HP".
    iApply "HP".
Qed.


(* Global Ghost State Constructions *)

(* Ghost Maps *)
From iris.base_logic Require Import ghost_map.
Lemma SAT_ghost_map_alloc `{ghost_mapG Σ K V} m F P :
  SAT Alloc F [] P →
  ∃ γ, SAT Alloc F [] (ghost_map_auth γ 1 m ∗ ([∗ map] k ↦ v ∈ m, k ↪[γ] v) ∗ P).
Proof.
  (* NOTE: this proof follows [ghost_map_alloc_strong] *)
  Local Existing Instance ghost_map_inG.
  rewrite ghost_map.ghost_map_auth_unseal /ghost_map.ghost_map_auth_def
          ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
  intros Hsat.
  apply (SAT_alloc_res (gmap_view_auth (V:=(agreeR (leibnizO V))) (DfracOwn 1) ∅))
    in Hsat as [γ Hauth]; last first.
  { eapply gmap_view_auth_valid. }
  exists γ. eapply SAT_upd, SAT_mono, Hauth.
  iIntros "[Hauth $]". rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
  etrans; first apply (gmap_view_alloc_big (V:=(agreeR (leibnizO V))) ∅ (to_agree <$> m) (DfracOwn 1)).
  - apply map_disjoint_empty_r.
  - done.
  - apply map_Forall_fmap. rewrite /compose.
    rewrite /map_Forall. intros. done.
  - rewrite right_id //.
    by rewrite big_opM_fmap.
Qed.


(* Gen Heaps *)
From iris.base_logic.lib Require Import gen_heap ghost_map.

Local Notation "l ↦ v" := (gen_heap.pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

Lemma SAT_gen_heap_init `{Countable L, !gen_heapGpreS L V Σ} σ F P:
  SAT Alloc F [] P →
  ∃ _: gen_heapGS L V Σ,
    SAT Alloc F [] (gen_heap_interp σ ∗
                    ([∗ map] l ↦ v ∈ σ, l ↦ v)%I ∗
                    ([∗ map] l ↦ a ∈ σ, meta_token l ⊤) ∗ P)%I.
Proof.
  (* NOTE: this proof follows [gen_heap_init] *)
  intros Hsat.
  eapply (SAT_ghost_map_alloc ∅) in Hsat as [γh Hsat].
  eapply (SAT_ghost_map_alloc ∅) in Hsat as [γm Hsat].
  exists (GenHeapGS _ _ _ γh γm).
  eapply SAT_upd, SAT_mono, Hsat.
  iIntros "(Hh & _ & Hm & _ & $)".
  iAssert (gen_heap_interp (hG:=GenHeapGS _ _ _ γh γm) ∅) with "[Hh Hm]" as "Hinterp".
  { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
  iMod (gen_heap_alloc_big with "Hinterp") as "(Hinterp & $ & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.


(* Inv Heaps *)
From iris.base_logic.lib Require Import gen_inv_heap.

Lemma SAT_inv_heap_init (L V : Type) (HL : has_lc)
  `{Countable L, !invGS_gen HL Σ, !gen_heapGS L V Σ, !inv_heapGpreS L V Σ} E n P F :
  SAT Alloc F [view E; supply n] P →
  ∃ _ : inv_heapGS L V Σ, SAT Alloc F [view E; supply n] (inv_heap_inv L V ∗ P).
Proof.
  (* NOTE: this proof follows [inv_heap_init] *)
  intros Hsat. eapply (SAT_alloc_res (● (to_inv_heap ∅))) in Hsat as [γ Hsat]; last first.
  { rewrite auth_auth_valid. eapply to_inv_heap_valid. }
  exists (Inv_HeapG L V γ).
  eapply SAT_fupd, SAT_mono, Hsat.
  iIntros "[H● $]". iAssert (inv_heap_inv_P (gG := Inv_HeapG L V γ)) with "[H●]" as "P".
  { iExists _; simpl. iFrame. done. }
  iApply (inv_alloc inv_heapN E inv_heap_inv_P with "P").
Qed.

(* Proph Maps *)
From iris.base_logic.lib Require Import proph_map.


Lemma SAT_proph_map_init `{Countable P, !proph_mapGpreS P V Σ} pvs ps F Q :
  SAT Alloc F [] Q →
  ∃ _ : proph_mapGS P V Σ, SAT Alloc F [] (proph_map_interp pvs ps ∗ Q).
Proof.
  (* NOTE: this proof is based on [proph_map_init] *)
  intros Hsat. eapply (SAT_ghost_map_alloc ∅) in Hsat as [γ Hsat].
  exists (ProphMapGS P V _ _ _ _ γ). eapply SAT_mono, Hsat.
  iIntros "(Hh & _ & $)". iExists ∅; simpl. iFrame. by iPureIntro.
Qed.


(* Mono Nat *)
From iris.algebra.lib Require Import mono_nat.
From iris.base_logic.lib Require Import mono_nat.

Lemma SAT_mono_nat_own_alloc `{!mono_natG Σ} n F P :
  SAT Alloc F [] P →
  ∃ γ, SAT Alloc F [] (mono_nat_auth_own γ 1 n ∗ mono_nat_lb_own γ n ∗ P).
Proof.
  (* NOTE: this proof is based on [mono_nat_own_alloc_strong] *)
  rewrite mono_nat.mono_nat_auth_own_unseal /mono_nat.mono_nat_auth_own_def.
  rewrite mono_nat.mono_nat_lb_own_unseal /mono_nat.mono_nat_lb_own_def.
  intros Hsat. eapply (SAT_alloc_res (●MN n ⋅ ◯MN n)) in Hsat as [γ Hsat]; last first.
  { apply mono_nat_both_valid; auto. }
  exists γ. eapply SAT_mono, Hsat.
  iIntros "([$ $] & $)".
Qed.
