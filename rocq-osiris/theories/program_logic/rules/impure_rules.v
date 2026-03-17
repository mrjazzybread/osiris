From osiris.lang Require Import encode locations.

From osiris Require Import base.
From osiris.semantics Require Import code.
From osiris.program_logic Require Import ewp tactics.

From osiris.program_logic.rules Require Import basic_rules.

From iris.proofmode Require Import proofmode.

Section micro_combinators.

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
    iApply (ewp_mono with "Himp").
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

  Lemma imp_widen (m : option V) :
    match m with
    | Some a => (ireturns Φ) a
    | None => False
    end -∗
    imp (widen m) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    unfold widen. destruct m.
    - iDestruct "Himp" as (a ->) "HΦ".
      iApply (imp_ret with "HΦ"); auto.
    - done.
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

End micro_combinators.

Section micro_codes.

  Import ewp_rules_tactics.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_please `{Observe A val} {Φ : A → iProp Σ} {ζ} η e :
    ▷ imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp please_eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    rewrite /please_eval.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hclose".
    construct_wp_nonret. thread_step.destruct_thread_step.
    iModIntro. ewp_mask_elim.
    rewrite try2_inject2_right. by iFrame.
  Qed.

  Lemma imp_choose {V : Type} `{Observe A V} {Φ : A → iProp Σ} {ζ} (m1 m2 : micro V exn) :
    imp m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} ∧ imp m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp (code.choose m1 m2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm". rewrite /code.choose /code.flip.
    iApply (imp_bind (λ (b : bool), True)%I (stop CFlip ())).
    { rewrite /impure.
      ewp_unfold_head.
      intro_state. ewp_mask_intro "Hmod".
      construct_wp_nonret. thread_step.destruct_thread_step.
      ewp_mask_elim. iFrame. rewrite /continue.
      iApply ewp_ret. simpl.
      iExists b; destruct b; auto. }
    iIntros ([|] _) "/=".
    - iDestruct "Hm" as "[$ _]".
    - iDestruct "Hm" as "[_ $]".
  Qed.

End micro_codes.

Section ugh.

  Import ewp_rules_tactics.

  Context `{!osirisGS Σ}.
  Context {V : Type} `{Observe A V}.
  Context {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_empty_loop {ζ} (R : iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    ⌜(j < i)%Z⌝ -∗
    R -∗
    imp loop x η (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (_ : unit), R }}.
  Proof.
    iIntros (Hrepr1 Hrepr2 Hbounds) "HR".
    rewrite /impure.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hmod". rewrite /loop.
    construct_wp_nonret. thread_step.destruct_thread_step.
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right.
    rewrite /E.loop.
    rewrite int.lt_repr_repr; try assumption.
    rewrite int.eq_repr_repr; try assumption.
    assert (i =? j = false)%Z as -> by lia.
    assert (j <? i = true)%Z as -> by lia.
    iApply (imp_ret VUnit ()); first encode.
    iApply "HR".
  Qed.

  Lemma imp_nonempty_loop {ζ} (I : Z → iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    ⌜(i ≤ j)%Z⌝ -∗
    I i -∗
    □ (∀ i',
         ⌜(i ≤ i' ≤ j)%Z⌝ -∗
         I i' -∗
         imp (eval ((x, #i') :: η) e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (_ : unit), I (i' + 1)%Z }}) -∗
    imp loop η x (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (_ : unit), I (j + 1)%Z }}.
  Proof.
    iIntros (Hrepr1 Hrepr2 Hbounds) "HR #He".
    iLöb as "IH" forall (i j Hrepr1 Hrepr2 Hbounds) "He".
    rewrite /impure.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hmod". rewrite /loop.
    construct_wp_nonret. thread_step.destruct_thread_step.
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right.
    rewrite /E.loop.
    assert (int.lt (int.repr j) (int.repr i) = false) as ->.
    { rewrite int.lt_repr_repr; first lia; assumption. }
    iPoseProof ("He" $! i with "[] HR") as "Heapp". iPureIntro; lia.
    rewrite int.eq_repr_repr; try assumption.
    case (decide (i = j)%Z); intros Heq.
    - assert (i =? j = true)%Z as -> by lia.
      iApply ewp_bind.
      iApply (ewp_mono with "Heapp").
      iIntros ([|]) "Ho".
      + iDestruct "Ho" as "(% & %Henc & HR)".
        iApply (imp_ret VUnit ()); first encode.
        rewrite Heq. iApply "HR".
      + done.
    - assert (i =? j = false)%Z as -> by lia.
      iApply ewp_bind.
      iApply (ewp_mono with "Heapp").
      iIntros ([|]) "Ho".
      + iDestruct "Ho" as "(% & %Henc & HR)".
        iSpecialize ("IH" $! (i + 1)%Z j).
        iSpecialize ("IH" with "[] [] [] HR").
        { iPureIntro.
          rewrite /int.representable in Hrepr1 Hrepr2 |- *.
          lia. }
        { iPureIntro; assumption. }
        { iPureIntro; lia. }
        replace (int.add (int.repr i) (int.one)) with (int.repr (i + 1)).
        iApply "IH".
        iIntros "!>" (?) "%Hbounds' HR".
        iApply ("He" with "[] HR").
        iPureIntro. lia.
        by rewrite int.add_repr_repr.
      + done.
  Qed.

   Lemma imp_loop {ζ} (I : Z → iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    I i -∗
    □ (∀ i',
         ⌜(i ≤ i' ≤ j)%Z⌝ -∗
         I i' -∗
         imp (eval ((x, #i') :: η) e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (_ : unit), I (i' + 1)%Z }}) -∗
    imp loop η x (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (_ : unit), I ((j + 1) `max` i)%Z }}.
  Proof.
    iIntros (Hrepr1 Hrepr2) "HI #He".
    case (decide (j < i)%Z); intros Hlt.
    - iApply imp_empty_loop; try assumption.
      iPureIntro; assumption.
      replace ((j + 1) `max` i)%Z with i by lia.
      iAssumption.
    - replace ((j + 1) `max` i)%Z with (j + 1)%Z by lia.
      iApply (imp_nonempty_loop with "[] HI He"); try assumption.
      iPureIntro; lia.
  Qed.

End ugh.

Section monotonicity.

  Context `{!osirisGS Σ}.

  Context {A V X : Type} `{Observe A V}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_mono (Φ' : A → iProp Σ) (ζ' : X → iProp Σ) m :
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A), Φ' x -∗ Φ x) -∗
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ (x : A), Φ' x -∗ Φ x) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ | iIntros "$" ].
    iIntros "(%v & Henc & HΦ')".
    iFrame.
    iApply ("Hmono" with "HΦ'").
  Qed.

  Lemma imp_mono_throw (ζ' : X → iProp Σ) m :
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ }} -∗
    (∀ (e : X), ζ' e -∗ ζ e) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "$" | ].
    iIntros "Hζ'".
    iApply ("Hmono" with "Hζ'").
  Qed.

  Lemma imp_mono_prot Ψ' m :
    imp m @ E <|Ψ'|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (Ψ' ⊑ Ψ)%ieff -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp Hmono".
    iApply (ewp_prot_mono with "Hmono Himp").
  Qed.

  Lemma imp_mono_pers Φ' m :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    □ (∀ x, Φ' x ={E}=∗ Φ x) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
  Context {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : A → iProp Σ}.

  Lemma imp_fupd m :
    (|={E}=> imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iApply ewp_fupd.
  Qed.

  Lemma imp_fupd_post m :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ x, |={E}=> Φ x }} -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd_post.
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "(%v & Henc & >HΦ) !>" | by iIntros "$ !>" ].
    iFrame.
  Qed.

  Lemma imp_fupd_post2 m :
    imp m @ E <|Ψ|> ⟨⟨ λ e, |={E}=> ζ e ⟩⟩ {{ Φ }} -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    iApply ewp_fupd_post.
    iApply (ewp_mono with "Himp").
    iIntros ([|]); [ iIntros "(%v & Henc & HΦ) !>" | by iIntros "$ !>" ].
    iFrame.
  Qed.

End updates.

Lemma impure_pure2 `{osirisGS Σ} {V} `{Observe A V} {X} (m : micro V X) ζ Φ :
  pure m Φ ζ →
  ⊢ imp m ⟨⟨ λ e, ⌜ζ e⌝ ⟩⟩ {{ λ x, ⌜Φ x⌝ }}.
Proof.
  iIntros (Hpure).
  iPoseProof (pure_ewp _ _ _ _ _ Hpure) as "Hewp".
  iApply (ewp_mono with "Hewp").
  iIntros ([|]); last auto.
  iIntros "(%v & %Henc & %HΦ)".
  iExists v; iFrame "%".
Qed.

Lemma impure_pure `{osirisGS Σ} {V} `{Observe A V} {X} (m : micro V X) Φ :
  pure m Φ ⊥ →
  ⊢ imp m {{ λ x, ⌜Φ x⌝ }}.
Proof.
  iIntros (Hpure).
  iPoseProof (pure_ewp _ _ _ _ _ Hpure) as "Hewp".
  iApply (ewp_mono with "Hewp").
  iIntros ([|]); last auto.
  iIntros "(%v & %Henc & %HΦ)".
  iExists v; iFrame "%".
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
