From osiris.lang Require Import encode.

From osiris Require Import base.
From osiris.semantics Require Import code.
From osiris.program_logic Require Import ewp tactics.

From osiris.program_logic.reasoning_rules Require Import basic_rules.

From iris.proofmode Require Import proofmode.

Section micro_combinators.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_ret (v : V) a :
    v = ♯ a →
    Φ a -∗
    imp^{ι} (ret v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hobserve) "HΦ".
    iApply ewp_ret.
    iFrame. iPureIntro; apply Hobserve.
  Qed.

  Lemma invert_imp_ret (v : V) :
    imp^{ι} (ret v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> ∃ a, ⌜v = ♯a⌝ ∗ Φ a.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_ret_inv with "Himp") as ">(%v' & -> & HΦ)".
    iModIntro. iFrame. auto.
  Qed.

  Lemma imp_throw e :
    ζ e -∗
    imp^{ι} (throw e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hζ".
    iApply ewp_throw.
    iFrame.
  Qed.

  Lemma invert_imp_throw e :
    imp^{ι} (throw e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> ζ e.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_throw_inv with "Himp") as ">$".
    iModIntro. auto.
  Qed.

  Lemma invert_imp_Crash :
    imp^{ι} Crash @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    |={E}=> False.
  Proof.
    iIntros "Himp".
    iPoseProof (ewp_crash_inv with "Himp") as ">False".
    auto.
  Qed.

  Lemma imp_try2 `{Observe A1 V1} {X1}
    (Φ' : A1 → iProp Σ) (ζ' : X1 → iProp Σ) (m : micro V1 X1)
    (h : outcome2 V1 X1 -> micro V X) :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ a, Φ' a -∗ imp^{ι} (continue h ♯a) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ' e -∗ imp^{ι} (discontinue h e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (try2 m h) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hresume".
    iApply ewp_try2.
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "(%v & -> & HΦ)" | iIntros "Hζ" ].
    - iApply ("Hresume" with "HΦ").
    - iApply ("Hresume" with "Hζ").
  Qed.

  Lemma imp_try `{Observe A1 V1} {X1}
    (Φ' : A1 → iProp Σ) (ζ' : X1 → iProp Σ) (m : micro V1 X1)
    (k : V1 → micro V X) (z : X1 → micro V X) :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ a, Φ' a -∗ imp^{ι} (k ♯a) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ' e -∗ imp^{ι} (z e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (try m k z) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hresume".
    iApply (imp_try2 with "Himp [Hresume]").
    rewrite /continue /discontinue.
    iExact "Hresume".
  Qed.

  Lemma imp_bind `{Observe A1 V1}
    (Φ' : A1 → iProp Σ) (m : micro V1 X)
    (f : V1 → micro V X) :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A1), Φ' x -∗ imp^{ι} (f ♯x) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (bind m f) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A1), Φ' x -∗ imp^{ι} (f ♯x) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp^{ι} (bind m f) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
    imp^{ι} m @ E <|Ψ|> {{ Φ }} -∗
    imp^{ι} (widen m) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    unfold widen.
    iApply (imp_try with "Himp").
    iSplit.
    - iIntros (a) "HΦ".
      iApply (imp_ret with "HΦ"); auto.
    - iIntros (e []).
  Qed.

  Lemma imp_Par `{Observe A1 V1} `{Observe A2 V2} {X'}
    Φ1 ζ1 Φ2 ζ2 m1 m2 (k : outcome2 (V1 * V2) X' → micro V X) :
    imp^{ι} m1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} m2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    (∀ e, ζ1 e -∗ ▷ imp^{ι} discontinue k e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e, ζ2 e -∗ ▷ imp^{ι} discontinue k e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ x y, Φ1 x -∗ Φ2 y -∗ ▷ imp^{ι} continue k (♯x, ♯y) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (Par m1 m2 k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin".
    iApply (ewp_Par with "H1 H2").
    iSplit; last iSplit.
    - iDestruct "Hjoin" as "[$ _]".
    - iDestruct "Hjoin" as "[_ [$ _]]".
    - iIntros (v1 v2) "(%x & -> & HΦ1) (%y & -> & HΦ2)".
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_Par2 `{Observe A1 V1} `{Observe A2 V2} {X'}
    Φ1 Φ2 m1 m2 (k : outcome2 (V1 * V2) X' → micro V X) :
    imp^{ι} m1 @ E <|Ψ|> {{ Φ1 }} -∗
    imp^{ι} m2 @ E <|Ψ|> {{ Φ2 }} -∗
    (∀ x y, Φ1 x -∗ Φ2 y -∗ ▷ imp^{ι} continue k (♯x, ♯y) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (Par m1 m2 k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin".
    iApply (imp_Par with "H1 H2 [Hjoin]").
    iSplit; last iSplit.
    - iIntros (? []).
    - iIntros (? []).
    - iExact "Hjoin".
  Qed.

End micro_combinators.

Section micro_codes.

  Import ewp_rules_tactics.

  Context `{!osirisGS Σ}.
  Context {V : Type} `{Observe A V}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {Φ : A → iProp Σ}.

  Lemma imp_please {ζ} η e :
    ▷ imp^{ι} eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp^{ι} please_eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    rewrite /please_eval.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hclose".
    construct_wp_nonret. thread_step.destruct_thread_step.
    iModIntro. ewp_mask_elim.
    rewrite try2_inject2_right. by iFrame.
  Qed.

  Lemma imp_choose {ζ} (m1 m2 : micro V exn) :
    imp^{ι} m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} ∧ imp^{ι} m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp^{ι} (code.choose m1 m2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm". rewrite /code.choose /code.flip.
    iApply (imp_bind (λ (b : bool), True)%I (stop CFlip ())).
    { rewrite /impure.
      ewp_unfold_head.
      intro_state. ewp_mask_intro "Hmod".
      construct_wp_nonret. thread_step.destruct_thread_step.
      ewp_mask_elim. iFrame. rewrite /continue.
      iApply ewp_ret. simpl.
      instantiate (1 := observe_bool).
      iExists b; destruct b; auto. }
    iIntros ([|] _) "/=".
    - iDestruct "Hm" as "[$ _]".
    - iDestruct "Hm" as "[_ $]".
  Qed.

End micro_codes.

Section monotonicity.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_mono (Φ' : A → iProp Σ) (ζ' : X → iProp Σ) m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A), Φ' x -∗ Φ x) -∗
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmonor Hmonot".
    iApply (ewp_mono with "Himp").
    iIntros ([|]).
    - iIntros "(%v & Henc & HΦ')".
      iFrame.
      iApply ("Hmonor" with "HΦ'").
    - iIntros "Hζ'".
      iApply ("Hmonot" with "Hζ'").
  Qed.

  Lemma imp_mono_ret (Φ' : A → iProp Σ) m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A), Φ' x -∗ Φ x) -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ | iIntros "$" ].
    iIntros "(%v & Henc & HΦ')".
    iFrame.
    iApply ("Hmono" with "HΦ'").
  Qed.

  Lemma imp_mono_throw (ζ' : X → iProp Σ) m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ }} -∗
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "$" | ].
    iIntros "Hζ'".
    iApply ("Hmono" with "Hζ'").
  Qed.

  Lemma imp_mono_prot Ψ' m :
    imp^{ι} m @ E <|Ψ'|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (Ψ' ⊑ Ψ)%ieff -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_prot_mono with "Hmono Himp").
  Qed.

  Lemma imp_mono_pers Φ' m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    □ (∀ x, Φ' x ={E}=∗ Φ x) -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp #Hmono".
    iApply (ewp_pers_mono with "Himp").
    iIntros "!>" ([|]); [ | by iIntros "$" ].
    iIntros "(%v & -> & HΦ)".
    iSpecialize ("Hmono" with "HΦ").
    iMod "Hmono". iModIntro.
    iFrame; auto.
  Qed.

End monotonicity.

Section updates.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_fupd m :
    (|={E}=> imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iApply ewp_fupd.
  Qed.

  Lemma imp_fupd_post m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ x, |={E}=> Φ x }} -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd_post.
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "(%v & Henc & >HΦ) !>" | by iIntros "$ !>" ].
    iFrame.
  Qed.

  Lemma imp_fupd_post2 m :
    imp^{ι} m @ E <|Ψ|> ⟨⟨ λ e, |={E}=> ζ e ⟩⟩ {{ Φ }} -∗
    imp^{ι} m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd_post.
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "(%v & Henc & HΦ) !>" | by iIntros "$ !>" ].
    iFrame.
  Qed.

End updates.

Lemma impure_pure `{osirisGS Σ} {V} `{Observe A V} {X} (m : micro V X) ζ Φ :
  pure m Φ ζ →
  ⊢ imp m ⟨⟨ λ e, ⌜ζ e⌝ ⟩⟩ {{ λ x, ⌜Φ x⌝ }}.
Proof.
  iIntros (Hpure).
  iIntros (ι).
  iPoseProof (pure_ewp _ _ _ _ _ _ Hpure) as "Hewp".
  iApply (ewp_mono with "Hewp").
  iIntros ([|]); last auto.
  iIntros "(%v & %Henc & %HΦ)".
  iExists v; iFrame "%".
Qed.
