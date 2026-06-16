From osiris Require Import base.
From osiris.lang Require Import encode thread_ids locations.
From osiris.semantics Require Import code eval.

Require Import ewp tactics.

Require Import basic_rules micro_rules.

From iris.proofmode Require Import proofmode.

(** This file contains structural rules for [imp]. *)

Section monotonicity.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Implicit Type m : micro V X.

  Lemma imp_strong_mono E1 E2 m Ψ1 Ψ2 ζ1 ζ2 Φ1 Φ2 :
    E1 ⊆ E2 →
    impure E1 m Ψ1 ζ1 Φ1 -∗
    (Ψ1 ⊑ Ψ2)%ieff -∗
    (∀ e, ζ1 e ={E2}=∗ ζ2 e) ∧ (∀ (a : A), Φ1 a ={E2}=∗ Φ2 a) -∗
    impure E2 m Ψ2 ζ2 Φ2.
  Proof.
    iIntros (HE) "Himp Hprot H".
    iApply (ewp_strong_mono with "Himp Hprot"); auto.
    iIntros ([|]).
    - iIntros "(%v & -> & HΦ1)".
      by iMod ("H" with "HΦ1") as "$".
    - iIntros "Hζ1".
      by iMod ("H" with "Hζ1") as "$".
  Qed.

  Local Tactic Notation "imp_mono" "with" constr(s) :=
    iApply (imp_strong_mono with s); auto with iFrame; first iApply iEff_le_refl.

  Lemma imp_mono E m Ψ ζ' ζ (Φ' : A → iProp Σ) Φ :
    (∀ a, Φ' a ⊢ Φ a) →
    (∀ e, ζ' e ⊢ ζ e) →
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} ⊢
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hmonor Hmonot) "H"; iApply (ewp_mono with "H").
    iIntros ([|]); last apply Hmonot.
    iIntros "(%v & -> & H)".
    iExists v. iSplit. auto.
    by iApply Hmonor.
  Qed.

  Lemma imp_mono_val E m Ψ ζ (Φ' : A → iProp Σ) Φ :
    (∀ a, Φ' a ⊢ Φ a) →
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} ⊢
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hmonor) "H"; iApply (imp_mono with "H"); auto.
  Qed.

  Lemma imp_mono_exn E m Ψ ζ' ζ Φ :
    (∀ e, ζ' e ⊢ ζ e) →
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ }} ⊢
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hmonot) "H"; iApply (imp_mono with "H"); auto.
  Qed.

  Lemma imp_mask_mono E1 E2 m Ψ ζ Φ :
    E1 ⊆ E2 →
    imp m @ E1 <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} ⊢ imp m @ E2 <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof. apply ewp_mask_mono. Qed.

  Global Instance imp_mono' E m Ψ ζ :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (impure E m Ψ ζ).
  Proof. by intros Φ Φ' ?; apply imp_mono. Qed.

  Global Instance imp_flip_mono' E m Ψ ζ :
    Proper (pointwise_relation _ (CRelationClasses.flip (⊢)) ==> (CRelationClasses.flip (⊢))) (impure E m Ψ ζ).
  Proof. by intros Φ Φ' ?; apply imp_mono. Qed.

  Lemma imp_frame_l E m Ψ ζ Φ R : R ∗ impure E m Ψ ζ Φ ⊢ impure E m Ψ ζ (λ o, R ∗ Φ o).
  Proof. iIntros "[? H]". imp_mono with "H". Qed.
  Lemma imp_frame_r E m Ψ ζ Φ R : impure E m Ψ ζ Φ ∗ R ⊢ impure E m Ψ ζ (λ v, Φ v ∗ R).
  Proof. iIntros "[H ?]". imp_mono with "H". Qed.

  Lemma imp_wand E m Ψ ζ Q' Q :
    impure E m Ψ ζ Q' -∗ (∀ v, Q' v -∗ Q v) -∗ impure E m Ψ ζ Q.
  Proof.
    iIntros "Hwp H". imp_mono with "Hwp".
    iSplitR; first auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma imp_wand' E m Ψ ζ' ζ Q' Q :
    impure E m Ψ ζ' Q' -∗ (∀ e, ζ' e -∗ ζ e) ∧ (∀ v, Q' v -∗ Q v) -∗ impure E m Ψ ζ Q.
  Proof.
    iIntros "Hwp H". imp_mono with "Hwp".
    iSplit.
    - iIntros (?) "?". by iApply "H".
    - iIntros (?) "?". by iApply "H".
  Qed.
  Lemma imp_wand_exn E m Ψ ζ' ζ Q :
    impure E m Ψ ζ' Q -∗ (∀ e, ζ' e -∗ ζ e) -∗ impure E m Ψ ζ Q.
  Proof.
    iIntros "Hwp H". imp_mono with "Hwp".
    iSplitL; last auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma imp_wand_l E m Ψ ζ Q' Q :
    (∀ v, Q' v -∗ Q v) ∗ impure E m Ψ ζ Q' ⊢ impure E m Ψ ζ Q.
  Proof. iIntros "[H Hwp]". iApply (imp_wand with "Hwp H"). Qed.
  Lemma imp_wand_r E m Ψ ζ Q' Q :
    impure E m Ψ ζ Q' ∗ (∀ v, Q' v -∗ Q v) ⊢ impure E m Ψ ζ Q.
  Proof. iIntros "[Hwp H]". iApply (imp_wand with "Hwp H"). Qed.
  Lemma imp_frame_wand E m Ψ ζ Φ R :
    R -∗ impure E m Ψ ζ (λ o, R -∗ Φ o) -∗ impure E m Ψ ζ Φ.
  Proof.
    iIntros "HR HWP". iApply (imp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma imp_mono_prot E m Ψ' Ψ ζ Φ :
    imp m @ E <|Ψ'|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (Ψ' ⊑ Ψ)%ieff -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_prot_mono with "Hmono Himp").
  Qed.

  Lemma imp_mono_pers E m Ψ ζ Φ' Φ :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    □ (∀ x, Φ' x ={E}=∗ Φ x) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp #Hmono".
    iApply ewp_fupd.
    iApply (ewp_wand with "Himp").
    iIntros ([|]); [ | by iIntros "$" ].
    iIntros "(%v & -> & HΦ)".
    iSpecialize ("Hmono" with "HΦ").
    iMod "Hmono". iModIntro.
    iFrame; auto.
  Qed.

End monotonicity.

Section updates.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Implicit Type m : micro V X.

  Lemma fupd_imp E m Ψ ζ Φ :
    (|={E}=> imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof. iApply fupd_ewp. Qed.

  Lemma imp_fupd E m Ψ ζ Φ :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ x, |={E}=> Φ x }} ⊢
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd.
    iApply (ewp_wand with "Himp").
    iIntros ([|]); [ iIntros "(%v & Henc & >HΦ) !>" | by iIntros "$ !>" ].
    iFrame.
  Qed.

  Lemma imp_fupd_exn E m Ψ ζ Φ :
    imp m @ E <|Ψ|> ⟨⟨ λ e, |={E}=> ζ e ⟩⟩ {{ Φ }} -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd.
    iApply (ewp_wand with "Himp").
    iIntros ([|]); [ by iIntros "(%v & -> & $) !>" | by iIntros "$ !>" ].
  Qed.

  Import ewp_rules_tactics.

  Lemma imp_atomic' E E2 m Ψ ζ Φ `{!thread_step.Atomic m}
    `{TCEq (option val) (to_eff m) None}
    `{TCEq (option thread) (to_join m) None}
    :
    (|={E,E2}=> impure E2 m Ψ (λ e, |={E2,E}=> ζ e) (λ o, |={E2,E}=> Φ o)) ⊢ impure E m Ψ ζ Φ.
  Proof.
    iIntros "He".
    iApply (ewp_atomic E E2). iMod "He". iModIntro.
    iApply (ewp_wand with "He").
    iIntros ([|]); [ iIntros "(% & -> & HΦ)" | iIntros "H" ].
    - by iMod "HΦ" as "$".
    - by iMod "H" as "$".
  Qed.

  Lemma imp_atomic E E2 m Ψ Φ `{!thread_step.Atomic m}
    `{TCEq (option val) (to_eff m) None}
    `{TCEq (option thread) (to_join m) None}
      :
    (|={E,E2}=> impure E2 m Ψ ⊥ (λ o, |={E2,E}=> Φ o)) ⊢ impure E m Ψ ⊥ Φ.
  Proof.
    iIntros "He".
    iApply (imp_atomic' E E2). iMod "He". iModIntro.
    iApply (imp_wand_exn with "He").
    iIntros (? []).
  Qed.

End updates.

Section proofmode_classes.
  Context `{!osirisGS Σ}.
  Context {A X V : Type} `{Observe A V}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : A → iProp Σ.
  Implicit Types m : micro V X.

  Global Instance frame_imp p E m R Ψ ζ Φ Φ' :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Φ' v)) →
    Frame p R (impure E m Ψ ζ Φ) (impure E m Ψ ζ Φ') | 2.
  Proof.
    rewrite /Frame=> HR. rewrite imp_frame_l. apply imp_mono_val, HR. constructor.
  Qed.

  Global Instance is_except_0_imp E m Ψ ζ Φ : IsExcept0 (impure E m Ψ ζ Φ).
  Proof. by rewrite /IsExcept0 -{2}fupd_imp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_imp p E m Ψ ζ P Φ :
    ElimModal True p false (|==> P) P (impure E m Ψ ζ Φ) (impure E m Ψ ζ Φ).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_imp.
  Qed.

  Global Instance elim_modal_fupd_imp p E m Ψ ζ P Φ :
    ElimModal True p false (|={E}=> P) P (impure E m Ψ ζ Φ) (impure E m Ψ ζ Φ).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_ewp.
  Qed.
  (* Error message instance for non-mask-changing view shifts.
     Also uses a slightly different error: we cannot apply fupd_mask_subseteq
     if e is not atomic, so we tell the user to first add a leading fupd and
     then change the mask of that. *)
  Global Instance elim_modal_fupd_ewp_wrong_mask p E1 E2 m Ψ ζ P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask. Use [iApply fupd_wp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (impure E1 m Ψ ζ Φ) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_imp_atomic p E1 E2 m Ψ P Φ
      `{!thread_step.Atomic m}
      `{TCEq (option val) (to_eff m) None}
      `{TCEq (option thread) (to_join m) None}
    :
    ElimModal True p false
            (|={E1,E2}=> P) P
            (impure E1 m Ψ ⊥ Φ) (impure E2 m Ψ ⊥ (λ o, |={E2,E1}=> Φ o))%I | 99.
  Proof.
    intros _. by rewrite bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r imp_atomic.
  Qed.
  Global Instance elim_modal_fupd_imp_atomic' p E1 E2 m Ψ ζ P Φ
      `{!thread_step.Atomic m}
      `{TCEq (option val) (to_eff m) None}
      `{TCEq (option thread) (to_join m) None}
    :
    ElimModal True p false
            (|={E1,E2}=> P) P
            (impure E1 m Ψ ζ Φ) (impure E2 m Ψ (λ e, |={E2,E1}=> ζ e) (λ o, |={E2,E1}=> Φ o))%I | 100.
  Proof.
    intros _. by rewrite bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r imp_atomic'.
  Qed.
  (* Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_imp_atomic_wrong_mask p E1 E2 E2' m Ψ ζ P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask. Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (impure E1 m Ψ ζ Φ) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_imp E m Ψ ζ P Φ :
    AddModal (|={E}=> P) P (impure E m Ψ ζ Φ).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_imp. Qed.


  Global Instance elim_acc_imp_atomic {Y} E1 E2 α β γ m Ψ Φ
      `{!thread_step.Atomic m}
      `{TCEq (option val) (to_eff m) None}
      `{TCEq (option thread) (to_join m) None}
    :
    ElimAcc (X:=Y) True
            (fupd E1 E2) (fupd E2 E1)
            α β γ (impure E1 m Ψ ⊥ Φ)
            (λ x, impure E2 m Ψ ⊥ (λ v, |={E2}=> β x ∗ (γ x -∗? Φ v)))%I | 99.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (imp_mono_exn _ _ _ ⊥). iIntros (? []).
    iApply (imp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
  Global Instance elim_acc_imp_atomic' {Y} E1 E2 α β γ m Ψ ζ Φ
      `{!thread_step.Atomic m}
      `{TCEq (option val) (to_eff m) None}
      `{TCEq (option thread) (to_join m) None}
    :
    ElimAcc (X:=Y) True
            (fupd E1 E2) (fupd E2 E1)
            α β γ (impure E1 m Ψ ζ Φ)
            (λ x, impure E2 m Ψ (λ e, |={E2}=> β x ∗ (γ x -∗? ζ e)) (λ v, |={E2}=> β x ∗ (γ x -∗? Φ v)))%I | 100.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (imp_wand' with "(Hinner Hα)").
    iSplit.
    - iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
    - iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_imp_nonatomic {Y} E α β γ m Ψ Φ :
    ElimAcc (X:=Y) True (fupd E E) (fupd E E)
            α β γ (impure E m Ψ ⊥ Φ)
            (λ x, impure E m Ψ ⊥ (λ v, |={E}=> β x ∗ (γ x -∗? Φ v)))%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply imp_fupd.
    iApply (imp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
  Global Instance elim_acc_imp_nonatomic' {Y} E α β γ m Ψ ζ Φ :
    ElimAcc (X:=Y) True (fupd E E) (fupd E E)
            α β γ (impure E m Ψ ζ Φ)
            (λ x, impure E m Ψ (λ e, |={E}=> β x ∗ (γ x -∗? ζ e)) (λ v, |={E}=> β x ∗ (γ x -∗? Φ v)))%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply imp_fupd. iApply imp_fupd_exn.
    iApply (imp_wand' with "(Hinner Hα)").
    iSplit.
    - iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
    - iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.

Section micro_constructors.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_ret (v : V) a :
    v = ♯ a →
    Φ a -∗
    imp (ret v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hobserve) "HΦ".
    iApply ewp_ret.
    iFrame. iPureIntro; apply Hobserve.
  Qed.

  Lemma invert_imp_ret (v : V) :
    imp (ret v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> ∃ a, ⌜v = ♯a⌝ ∗ Φ a.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_ret_inv with "Himp") as ">(%v' & -> & HΦ)".
    iModIntro. iFrame. auto.
  Qed.

  Lemma imp_throw e :
    ζ e -∗
    imp (throw e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hζ".
    iApply ewp_throw.
    iFrame.
  Qed.

  Lemma invert_imp_throw e :
    imp (throw e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> ζ e.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_throw_inv with "Himp") as ">$".
    iModIntro. auto.
  Qed.

  Lemma invert_imp_Crash :
    imp Crash @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> False.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_crash_inv with "Himp") as ">False".
    auto.
  Qed.

  Lemma imp_Par2 `{Observe A1 V1} `{Observe A2 V2} {X'}
    Φ1 ζ1 Φ2 ζ2 m1 m2 (k : outcome2 (V1 * V2) X' → micro V X) :
    imp m1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp m2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    (∀ e, ζ1 e -∗ ▷ imp discontinue k e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ2 e -∗ ▷ imp discontinue k e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ x y, Φ1 x -∗ Φ2 y -∗ ▷ imp continue k (♯x, ♯y) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Par m1 m2 k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin".
    iApply (ewp_Par with "H1 H2").
    iSplit; last iSplit.
    - iDestruct "Hjoin" as "[$ _]".
    - iDestruct "Hjoin" as "[_ [$ _]]".
    - iIntros (v1 v2) "(%x & -> & HΦ1) (%y & -> & HΦ2)".
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_Par `{Observe A1 V1} `{Observe A2 V2}
    Φ1 Φ2 m1 m2 (k : outcome2 (V1 * V2) X → micro V X) :
    imp m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    imp m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ e, ζ e -∗ ▷ imp discontinue k e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ x y, Φ1 x -∗ Φ2 y -∗ ▷ imp continue k (♯x, ♯y) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Par m1 m2 k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin".
    iApply (ewp_Par with "H1 H2").
    iSplit; last iSplit.
    - iDestruct "Hjoin" as "[$ _]".
    - iDestruct "Hjoin" as "[$ _]".
    - iIntros (v1 v2) "(%x & -> & HΦ1) (%y & -> & HΦ2)".
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

End micro_constructors.

Section micro_combinators.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_par' {ζ : exn → iProp Σ} `{Observe A1 V1} `{Observe A2 V2} {Φ : A1 * A2 → iProp Σ}
    Φ1 Φ2 m1 m2 :
    imp m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    imp m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ x y, Φ1 x -∗ Φ2 y -∗ ▷ Φ (x, y)) -∗
    imp (par m1 m2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin".
    iApply (imp_Par with "H1 H2").
    iSplit.
    - iIntros (e) "Hζ".
      iApply (imp_throw with "Hζ").
    - iIntros (v1 v2) "HΦ1 HΦ2".
      iApply (imp_ret _ (v1, v2)); first encode.
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_par {ζ : exn → iProp Σ} `{Observe A1 V1} `{Observe A2 V2}
    (Φ1 : A1 → iProp Σ) (Φ2 : A2 → iProp Σ) m1 m2 :
    imp m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    imp m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    imp (par m1 m2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ '(x, y), Φ1 x ∗ Φ2 y }}.
  Proof.
    iIntros "H1 H2".
    iApply (imp_par' with "H1 H2").
    iIntros (??) "$ $".
  Qed.

  Context {A X V : Type} `{Observe A V}.
  Context {ζ : X → iProp Σ} {Φ : A → iProp Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : A → iProp Σ.
  Implicit Types m : micro V X.

  Lemma imp_try2 `{Observe A1 V1} {X1}
    (Φ' : A1 → iProp Σ) (ζ' : X1 → iProp Σ) (m : micro V1 X1)
    (h : outcome2 V1 X1 -> micro V X) :
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ a, Φ' a -∗ imp (continue h ♯a) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ' e -∗ imp (discontinue h e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (try2 m h) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hresume".
    iApply ewp_try2.
    iApply (ewp_wand with "Himp").
    iIntros ([|]); [ iIntros "(%v & -> & HΦ)" | iIntros "Hζ" ].
    - iApply ("Hresume" with "HΦ").
    - iApply ("Hresume" with "Hζ").
  Qed.

  Lemma imp_try `{Observe A1 V1} {X1}
    (Φ' : A1 → iProp Σ) (ζ' : X1 → iProp Σ) (m : micro V1 X1)
    (k : V1 → micro V X) (z : X1 → micro V X) :
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ a, Φ' a -∗ imp (k ♯a) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ' e -∗ imp (z e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (try m k z) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hresume".
    iApply (imp_try2 with "Himp [Hresume]").
    rewrite /continue /discontinue.
    iExact "Hresume".
  Qed.

  Lemma imp_bind `{Observe A1 V1}
    (Φ' : A1 → iProp Σ) (m : micro V1 X)
    (f : V1 → micro V X) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A1), Φ' x -∗ imp (f ♯x) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (bind m f) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hconseq".
    rewrite bind_as_try.
    iApply (imp_try with "Himp [Hconseq]").
    iSplit; first iExact "Hconseq".
    iIntros (e). iApply imp_throw.
  Qed.

  Lemma imp_bind2 `{Observe A1 V1}
    (Φ' : A1 → iProp Σ) (ζ' : X → iProp Σ) (m : micro V1 X)
    (f : V1 → micro V X) :
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A1), Φ' x -∗ imp (f ♯x) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp (bind m f) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hconseq".
    rewrite bind_as_try.
    iApply (imp_try with "Himp [Hconseq]").
    iSplit.
    - iDestruct "Hconseq" as "[$ _]".
    - iDestruct "Hconseq" as "[_ Hζ]".
      iIntros (e) "Hζ'". iSpecialize ("Hζ" with "Hζ'").
      iApply (imp_throw with "Hζ").
  Qed.

  Lemma imp_widen (m : micro V void) :
    imp m @ E <|Ψ|> {{ Φ }} -∗
    imp (widen m) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    unfold widen.
    iApply (imp_try with "Himp").
    iSplit.
    - iIntros (a) "HΦ".
      iApply (imp_ret with "HΦ"); auto.
    - iIntros (e []).
  Qed.

  Lemma imp_of_option (o : option V) :
    match o with
    | Some a => (ireturns Φ) a
    | None => False
    end -∗
    imp (of_option o) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    unfold of_option. destruct o.
    - iDestruct "Himp" as (a ->) "HΦ".
      iApply (imp_ret with "HΦ"); auto.
    - done.
  Qed.


End micro_combinators.

Lemma imp_bind_par `{!osirisGS Σ} {V : Type} {E Ψ ζ} `{Observe A V} `{Observe A1 V1} `{Observe A2 V2}
  {Φ : A → iProp Σ}
  (Φ1 : A1 → iProp Σ) (Φ2 : A2 → iProp Σ) m1 m2 (f : (V1 * V2) → micro V exn) :
  imp m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
  imp m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
  (∀ a1 a2, Φ1 a1 -∗ Φ2 a2 -∗
            ▷ imp (f (♯a1, ♯a2)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
  imp (bind (par m1 m2) f) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
Proof.
  iIntros "H1 H2 P".
  iApply (imp_bind with "[-]").
  iApply (imp_par' with "H1 H2").
  iIntros (??) "HΦ1 HΦ2".
  instantiate (1:=λ '(x, y), impure E (f (♯x, ♯y)) _ _ _).
  iApply ("P" with "HΦ1 HΦ2").
  iIntros ([??]) "$".
Qed.

Lemma imp_bind_par_frac `{osirisGS Σ} `{Hfrac : fractional.AsFractional _ P Q q} {E Ψ ζ} `{Observe A V} `{Observe A1 V1} `{Observe A2 V2}
  (Φ : A → iProp Σ) (Φ1 : A1 → iProp Σ) (Φ2 : A2 → iProp Σ) (m1 : micro V1 exn) (m2 : micro V2 exn) (f : V1 * V2 → micro V exn) :
  P -∗
  (Q (q/2)%Qp -∗ impure E m1 Ψ ζ (λ a1, Φ1 a1 ∗ Q (q/2)%Qp)) -∗
  (Q (q/2)%Qp -∗ impure E m2 Ψ ζ (λ a2, Φ2 a2 ∗ Q (q/2)%Qp)) -∗
  (∀ a1 a2,
    Φ1 a1 -∗ Φ2 a2 -∗ ▷ impure E (f (♯a1, ♯a2)) Ψ ζ Φ) -∗
  impure E (bind (par m1 m2) f) Ψ ζ (λ a, Φ a ∗ P).
Proof.
  iIntros "P H1 H2 Hf".
  iDestruct "P" as "[P1 P2]".
  iApply (imp_bind with "[-]").
  { iApply (imp_par' with "[P1 H1] [P2 H2]").
    iApply ("H1" with "P1"). iApply ("H2" with "P2").
    iIntros (a1 a2) "(HΦ1 & Q1) (HΦ2 & Q2)".
    iSpecialize ("Hf" with "HΦ1 HΦ2"). iNext.
    instantiate (1:=λ '(x, y), (impure E (f (♯x, ♯y)) Ψ ζ Φ ∗ P)%I).
    iFrame "Hf".
    iApply fractional.as_fractional.
    iCombine "Q1 Q2" as "Q".
    iPoseProof (fractional.as_fractional_fractional (AsFractional := Hfrac) with "Q") as "Q".
    by rewrite Qp.div_2. }
  iIntros ((?&?)) "(Hf & $)". iApply "Hf".
Qed.

Lemma impure_pure2 `{osirisGS Σ} {V} `{Observe A V} {X} `{NotVal X} {E Ψ} (m : micro V X) (ζ : X → Prop) (Φ : A → Prop) :
  pure m Φ ζ →
  ⊢ imp m @ E <|Ψ|> ⟨⟨ λ e, ⌜ζ e⌝ ⟩⟩ {{ λ x, ⌜Φ x⌝ }}.
Proof.
  iIntros (Hpure).
  iPoseProof (pure_ewp _ _ _ _ _ Hpure) as "Hewp".
  iApply (ewp_mono with "Hewp").
  iIntros ([v|e]).
  - iIntros "(%a & %Henc & %Ha)". iExists a; iFrame "%".
  - iIntros "%He". iPureIntro.
    destruct He as (c & -> & Hc). unfold observe, observe_id. exact Hc.
Qed.

Lemma impure_pure `{osirisGS Σ} {V} `{Observe A V} `{Encode B} {E Ψ ζ} (m : micro V exn) Φ :
  pure m Φ (⊥ : B → Prop) →
  ⊢ imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ x, ⌜Φ x⌝ }}.
Proof.
  iIntros (Hpure).
  iPoseProof (pure_ewp _ _ _ _ _ Hpure) as "Hewp".
  iApply (ewp_mono with "Hewp").
  iIntros ([v|e]).
  - iIntros "(%a & %Henc & %HΦ)".
    iExists a; iFrame "%".
  - iIntros "%He". destruct He as (b & _ & []).
Qed.

Section dynamic_checks.

  Context `{!osirisGS Σ}.

  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Global Instance : Observe Z int := { observe := int.repr }.

  Lemma imp_as_int (m : microvx) (Φ : Z → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_int m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    rewrite /as_int.
    iApply (imp_bind with "Hm").
    iIntros (i) "HΦ".
    iApply (imp_ret with "HΦ"); first encode.
  Qed.

  Lemma imp_as_loc (m : microvx) (Φ : locations.loc → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_loc m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (l) "HΦ".
    iApply (imp_ret with "HΦ"); first encode.
  Qed.

  Lemma imp_as_array (m : microvx) (Φ : syntax.array → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_array m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (l) "HΦ".
    iApply (imp_ret with "HΦ"); first encode.
  Qed.

  Lemma imp_as_record (m : microvx) (Φ : syntax.record → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_record m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (l) "HΦ".
    iApply (imp_ret with "HΦ"); first encode.
  Qed.

  Lemma imp_as_bool (m : microvx) (Φ : bool → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_bool m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (b) "HΦ".
    destruct b;
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  Lemma imp_as_cont (m : microvx) (Φ : cont → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_cont m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (k) "HΦ".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  Lemma imp_as_thread (m : microvx) (Φ : thread → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_thread m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (k) "HΦ".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  Lemma imp_as_struct (m : microvx) (Φ : env → iProp Σ) :
    imp m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_struct m @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (k) "HΦ".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

End dynamic_checks.
