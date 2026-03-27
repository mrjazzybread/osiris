From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z big_opLZ.

Definition array : Type := list loc.

Global Instance : Encode array := { encode arr := VArray arr }.
Global Instance : Observe array (list loc) := { observe a := a }.

Section array_resources.

  Context `{!osirisGS Σ}.

  Definition isArray (a : array) (n : Z) : iProp Σ :=
      ⌜length a = n⌝ ∗ ⌜0 ≤ n ≤ max_array⌝.

  Global Instance is_array_persistent a n : Persistent (isArray a n).
  Proof. apply _. Qed.

  Definition isSlice `{Encode A} dq (ls : array) (i : Z) (xs : list A) : iProp Σ :=
    ⌜0 ≤ i ∧ i + length xs ≤ length ls⌝ ∗
    [∗ listZ] l;x ∈ seg i (i + length xs) ls; xs, pointsto l dq (V #x).

  Arguments isSlice {_ _} dq a i xs : rename.

  Lemma Slice_app `{Encode A} j dq a i (xs ys : list A) :
    j = i + length xs →
    isSlice dq a i (xs ++ ys) ⊣⊢ (isSlice dq a i xs ∗ isSlice dq a j ys).
  Proof.
    intros ->.
    length_nonneg xs; length_nonneg ys; length_nonneg a.
    iStartProof; iSplit; iIntros "Hslice".
    - unfold isSlice. length.
      iDestruct "Hslice" as "([%Hpos %Hlen] & Hseg)".
      rewrite -(assoc bi_sep).
      iSplitR. { iPureIntro; lia. }
      rewrite (comm bi_sep) -(assoc bi_sep).
      iSplitR. { iPureIntro; lia. }
      rewrite (comm bi_sep). iApply big_sepLZ2_app_inv; first (length; lia).
      rewrite (split_seg (i + length xs)); try lia.
      rewrite (assoc Z.add). iFrame.

    - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
      iDestruct "Hslice1" as "([%Hpos %Hlen] & Hslice1)".
      iDestruct "Hslice2" as "([%Hpos' %Hlen'] & Hslice2)".
      iSplit. { iPureIntro; length; lia. }
      iPoseProof (big_sepLZ2_app with "Hslice1 Hslice2") as "Hslice".
      rewrite -(split_seg (i + length xs)); try lia.
      length; rewrite (assoc Z.add).
      iApply "Hslice".
  Qed.

  (* We can split a slice on an index [j] of the model [xs].

     This results in two slices with models
     [seg 0 j xs] and [seg j (length xs) xs]. *)

  Lemma split_Slice `{Encode A} (j : Z) dq a i (xs : list A) :
    0 ≤ j ≤ length xs →
    isSlice dq a i xs ⊣⊢ isSlice dq a i (seg 0 j xs) ∗ isSlice dq a (i + j) (seg j (length xs) xs).
  Proof.
    length_nonneg xs; length_nonneg a.
    intros Hbound.
    rewrite -{1}(seg_all 0 (length xs) xs); try lia.
    rewrite (split_seg j); try lia.
    rewrite Slice_app.
    f_equiv. f_equiv. length. lia.
  Qed.

  Definition isArrayCell `{Encode A} dq (a : array) (i : nat) (x : A) : iProp Σ :=
    isSlice dq a i (singleton x).

  Definition ownArray `{Encode A} (a : array) (xs : list A) : iProp Σ :=
    isArray a (length xs) ∗ isSlice (DfracOwn 1) a 0 xs.

  Lemma slice_of_own `{Encode A} (a : array) (xs : list A) n :
    n = length xs →
    ownArray a xs ⊣⊢ isArray a n ∗ isSlice (DfracOwn 1) a 0 xs.
   Proof. intros ->. done. Qed.

End array_resources.

Section array_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_as_array {ζ} (m : microvx) (Φ : array → iProp Σ) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp as_array m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (a) "HΦ".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  Lemma imp_EArrayLit `{Encode A} {ζ} (Φs : list (A → iProp Σ)) es :
    ⌜length Φs = length es ∧ length es ≤ max_array⌝ -∗
    imp evals η es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ xs, [∗ listZ] x;Φ ∈ xs;Φs, Φ x }} -∗
    imp eval η (EArrayLit es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ a, ∃ xs, ownArray a xs ∗ [∗ listZ] x;Φ ∈ xs;Φs, Φ x }}.
  Proof.
    iIntros "[%Hleneq %Hlenbound] He". simpl_eval.
    iApply (imp_bind (A1:=list A) with "He").
    iIntros (xs) "HΦs".
    iApply (imp_allocn).
    iIntros "!>" (ls) "Hls".
    rewrite /continue /=.
    iApply (imp_ret _ ls); first encode.
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlenls".
    rewrite length_map in Hlenls.
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenxs".
    iFrame.
    iSplitR.
    - iPureIntro.
      length_nonneg es; rewrite Hlenls Hlenxs Hleneq; lia.
    - iSplit. { iPureIntro; lia. }
      rewrite -Hlenls. seg.
      iApply (big_sepLZ2_fmap_r encode.encode (λ _ l v, l ↦ v)%I).
      iApply "Hls".
  Qed.

  Lemma imp_EArrayEmpty `{Encode A} {ζ} :
    ⊢ imp eval η (EArrayLit []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
        {{ λ a, ownArray a (@nil A) }}.
  Proof.
    iApply imp_wand.
    - iApply (imp_EArrayLit (@nil (A → _))  []).
      iPureIntro; length; split; auto.
      pose proof (max_array_positive). lia.
      simpl_evals. iApply imp_ret; first encode.
      by iApply big_sepLZ2_nil.
    - iIntros (a) "(%xs & HownArr & Hxs)".
      by iPoseProof (big_sepLZ2_nil_inv_r with "Hxs") as "->".
  Qed.

  Lemma imp_EArrayLength {ζ} (n : Z) e :
    imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, isArray a n }} -∗
    imp eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n', ⌜n' = n⌝ }}.
  Proof.
    iIntros "He". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_array with "He"). }
    iIntros (ls) "(%Hlen & %Hbound)".
    change (♯ls) with ls.
    iApply (imp_ret (VInt (repr (length ls))) (length ls)%Z). encode.
    iPureIntro. lia.
  Qed.

  Lemma imp_EArrayMake `{Encode A} {ζ} {e1 e2} (n : Z) (Φ : A → iProp Σ) :
    ⌜0 ≤ n ≤ max_array⌝ -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, ⌜i = n⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArrayMake e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (a : array), ∃ x, Φ x ∗ ownArray a (replicate n x) }}.
  Proof.
    iIntros (Hbound) "He1 He2". simpl_eval.
    iApply (imp_Par (A1:=Z) (A2:=A) with "[He1] He2").
    { iApply (imp_as_int with "He1"). }
    rewrite /continue /discontinue /=.
    iSplit.
    - iIntros (e) "Hζ !>".
      iApply (imp_throw with "Hζ").
    - iIntros (? a) "-> Hφ !> /=".
      rewrite bind_ret signed_repr; last representable.
      case_decide; last contradiction.
      iApply imp_allocn.
      iIntros "!>" (ls) "Hpts".
      iPoseProof (big_sepLZ2_length with "Hpts") as "%Hlen'".
      rewrite length_replicate in Hlen'.
      rewrite /continue /=.
      iApply imp_ret; first encode.
      iFrame.
      iSplitR. { iPureIntro; length; lia. }
      iSplit. { iPureIntro; length; lia. }
      seg.
      rewrite -fmap_replicate big_sepLZ2_fmap_r.
      iApply "Hpts".
  Qed.

  Global Instance inhabited_loc : Inhabited loc.
  Proof.
    do 2 constructor. apply Z.inhabited.(inhabitant).
  Qed.

  Lemma big_sepLZ2_lookup_seg_acc `{Inhabited A, Inhabited B} k i j (xs : list A) (ys : list B) (Φ : Z → A → B → iProp Σ) :
    valid_seg i j xs →
    i ≤ k < j →
    ([∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x) -∗
    Φ (k - i) (xs !!! k) (ys !!! (k - i)) ∗
    (Φ (k - i) (xs !!! k) (ys !!! (k - i)) -∗ [∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x).
  Proof.
    iIntros (Hvalid Hlek) "Hseg".
    iPoseProof (big_sepLZ2_length with "Hseg") as "%Hlen".
    iApply (big_sepLZ2_lookup_acc _ _ _ (k - i) with "Hseg"); lookup.
    - replace (i + (k - i)) with k by lia.
      apply list_lookup_lookup_total_valid. lia.
    - apply list_lookup_lookup_total_valid.
      revert Hlen. length. lia.
  Qed.

  Lemma big_sepLZ2_insert_seg_acc `{Inhabited A, Inhabited B} k i j (xs : list A) (ys : list B) (Φ : Z → A → B → iProp Σ) :
    valid_seg i j xs →
    i ≤ k < j →
    ([∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x) -∗
    Φ (k - i) (xs !!! k) (ys !!! (k - i)) ∗
    (∀ x y, Φ (k - i) x y -∗ [∗ listZ] n↦l; x ∈seg i j (<[k:=x]>xs); <[k-i:=y]>ys, Φ n l x).
  Proof.
    iIntros (Hvalid Hlek) "Hseg".
    iPoseProof (big_sepLZ2_length with "Hseg") as "%Hlen".
    setoid_rewrite seg_insert_inside; last lia.
    iApply (big_sepLZ2_insert_acc _ _ _ (k - i) with "Hseg"); lookup.
    - replace (i + (k - i)) with k by lia.
      apply list_lookup_lookup_total_valid. lia.
    - apply list_lookup_lookup_total_valid.
      revert Hlen. length. lia.
  Qed.

  Lemma imp_EArrayGet2 `{Encode A, Inhabited A} {Φ : A → iProp Σ} {ζ} (Φ1 : array → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 :
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, Φ1 a }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, Φ2 i }} -∗
    (∀ a i, Φ1 a -∗ Φ2 i -∗
            ∃ n, isArray a n ∗
                 ∃ dq j xs,
                   ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ isSlice dq a j xs) ∗
                   ▷ (isSlice dq a j xs -∗ Φ (xs !!! (i - j)))) -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 P". simpl_eval.
    iApply (imp_Par (A1:=array) (A2:=Z) with "[He1] [He2]").
    { iApply (imp_as_array with "He1"). }
    { iApply (imp_as_int with "He2"). }
    iSplit.
    - iIntros (e) "Hζ !>".
      iApply (imp_throw with "Hζ").
    - iIntros (ls i) "HΦ1 HΦ2".
      iDestruct ("P" with "HΦ1 HΦ2")
        as "(%n & #Harr & %dq & %j & %xs & P)".
      rewrite /continue /= bind_ret.
      iNext.
      iDestruct "P" as "((%Hle & %Hlt & Hslice) & P)".
      iDestruct "Harr" as "(%Hlen' & %Hbound)".
      iDestruct "Hslice" as "(%Hlen & Hslice)".
      rewrite signed_repr; last representable.
      rewrite list_lookup_lookup_total_valid; last lia.
      iPoseProof (big_sepLZ2_lookup_seg_acc i with "Hslice")
        as "(Hl & Hslice)"; try lia.
      iApply (imp_load with "Hl").
      iIntros "!> Hl".
      iApply imp_ret; first encode.
      iApply "P".
      iSplit. { iPureIntro; apply Hlen. }
      iApply ("Hslice" with "Hl").
  Qed.

  Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} a (n : Z) (i j : Z) dq (xs : list A) x e1 e2 :
    ⌜j ≤ i⌝ -∗
    ⌜i - j < length xs⌝ -∗
    ⌜xs !!! (i - j) = x⌝ -∗
    isArray a n -∗
    ▷ isSlice dq a j xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ v, ⌜v = x⌝ ∗ isSlice dq a j xs }}.
  Proof.
    iIntros (Hi Hlookup Hlen) "#Harr Hslice He1 He2".
    iApply (imp_EArrayGet2 with "[He1] He2").
    { iApply (imp_wand with "He1").
      iIntros (?) "->". iFrame "#".
      instantiate (1 := (λ a', ⌜a' = a⌝)%I). done. }
    iIntros (? ?) "-> ->".
    iFrame "#".
    iFrame "%". iFrame.
    iIntros "!> $".
  Qed.

  Lemma imp_EArraySet2 `{Encode A, Inhabited A} {Φ : unit → iProp Σ} {ζ}
    (Φ3 : A → iProp Σ) (Φ1 : array → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 e3 :
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, Φ1 a }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, Φ2 i }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3  }} -∗
    (∀ a i y, Φ1 a -∗ Φ2 i -∗ Φ3 y -∗
              ∃ n, isArray a n ∗
                   ∃ j xs,
                     ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ isSlice (DfracOwn 1) a j xs) ∗
                     ▷ (isSlice (DfracOwn 1) a j (<[i - j := y]> xs) -∗ Φ ())) -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 He3 P". simpl_eval.
    iApply (imp_Par (A1:=array) (A2:=Z * A) with "[He1] [He2 He3]").
    { iApply (imp_as_array with "He1"). }
    { iApply (imp_Par (A1:=Z) (A2:=A) with "[He2] He3").
      iApply (imp_as_int with "He2").
      iSplit.
      - iIntros (e) "Hζ". iApply (imp_throw with "Hζ").
      - iIntros (i y) "HΦ2 HΦ3".
        iApply (imp_ret _ (i, y)); first encode.
        instantiate (1 := (λ '(i, y), Φ2 i ∗ Φ3 y)%I). iFrame. }
    iSplit.
    { iIntros (e) "Hζ !>".
      iApply (imp_throw with "Hζ"). }
    iIntros (a [i y]) "HΦ1 (HΦ2 & HΦ3)".
    iDestruct ("P" with "HΦ1 HΦ2 HΦ3")
      as "(%n & #Harr & %j & %xs & P)".
    rewrite /continue /= bind_ret.
    iNext.
    iDestruct "P" as "((%Hle & %Hlt & Hslice) & P)".
    iDestruct "Harr" as "(%Hlen' & %Hbound)".
    iDestruct "Hslice" as "(%Hlen & Hslice)".
    rewrite signed_repr; last representable.
    rewrite list_lookup_lookup_total_valid; last lia.
    iPoseProof (big_sepLZ2_insert_seg_acc i with "Hslice")
      as "(Hl & Hslice)"; try lia.

    iApply (imp_store with "Hl").
    rewrite /continue; iIntros "!> Hl /=".
    iApply imp_ret; first encode.
    iApply "P".
    iSplit; length. { iPureIntro. apply Hlen. }
    iSpecialize ("Hslice" with "Hl").
    update.
    iApply "Hslice".
  Qed.

  Lemma imp_EArraySet `{Encode A, Inhabited A} {ζ}
    (Φ : A → iProp Σ) (i j n : Z) (a : array) xs e1 e2 e3 :
    ⌜j ≤ i⌝ -∗
    ⌜i - j < length xs⌝ -∗
    isArray a n -∗
    ▷ isSlice (DfracOwn 1) a j xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a'=a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i'=i⌝ }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (_ : unit), ∃ y, Φ y ∗ isSlice (DfracOwn 1) a j (<[i-j:=y]> xs) }}.
  Proof.
    iIntros (Hbound Hlen) "#Harr Hslice He1 He2 He3".
    iApply (imp_EArraySet2 with "He1 He2 He3").
    iIntros (?? y) "-> -> HΦ".
    iFrame "#". iFrame.
    iSplit.
    - iPureIntro. lia.
    - iIntros "!> Hslice".
      iFrame.
  Qed.

End array_reasoning.
