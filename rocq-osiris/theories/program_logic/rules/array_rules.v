From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z big_opLZ.

(** This file defines array resource predicates and [imp] rules for array expressions. *)

Definition array : Type := loc.

Global Instance : Encode array := _.
Global Instance : Observe array loc := _.

Section array_resources.

  Context `{!osirisGS Σ}.

  Definition isArray (a : array) (n : Z) : iProp Σ :=
    ∃ t ls, pointsto a DfracDiscarded (Dict t ls) ∗
            ⌜length ls = n⌝ ∗ ⌜0 ≤ n ≤ max_array⌝.

  Global Instance is_array_persistent a n : Persistent (isArray a n).
  Proof. apply _. Qed.

  Definition isSlice `{Encode A} dq (a : array) (i : Z) (xs : list A) : iProp Σ :=
    ∃ t ls, pointsto a DfracDiscarded (Dict t ls) ∗
            ⌜0 ≤ i⌝ ∧ ⌜i + length xs ≤ length ls⌝ ∗
            [∗ listZ] l;x ∈ seg i (i + length xs) ls; xs, l ↦{dq} #x.

  Definition ownArray `{Encode A} (a : array) (xs : list A) : iProp Σ :=
    isArray a (length xs) ∗ isSlice (DfracOwn 1) a 0 xs.

End array_resources.

Notation "a ↦∗ dq xs" :=
    (isSlice dq a 0 xs)
      (at level 20, dq custom dfrac at level 1, format "a  ↦∗ dq  xs") : bi_scope.
Notation "a ↦∗[ i ] dq xs" :=
  (isSlice dq a i xs)
    (at level 20, dq custom dfrac at level 1, i at level 200, format "a  ↦∗[ i ] dq  xs") : bi_scope.

Section array_resources.

  Context `{!osirisGS Σ}.

  Lemma Slice_app `{Encode A} j dq a i (xs ys : list A) :
    j = i + length xs →
    a ↦∗[i]{dq} (xs ++ ys) ⊣⊢ (a ↦∗[i]{dq} xs ∗ a ↦∗[j]{dq} ys).
  Proof.
    intros ->.
    lengths.
    iStartProof; iSplit; iIntros "Hslice".
    - iDestruct "Hslice" as "(%t & %ls & #Ha & %Hpos & %Hlen & Hls)".
      iFrame "#". length in Hlen. length.
      rewrite (split_seg (i + length xs)); try lia.
      iPoseProof (big_sepLZ2_app_inv with "Hls")
        as "($ & Hslice2)"; first (length; lia).
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame.
      iPureIntro. lia.

    - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
      iDestruct "Hslice1" as "(%t & %ls & #Ha & %Hpos & %Hlen & Hslice1)".
      iDestruct "Hslice2" as "(%t' & %ls' & #Ha' & %Hpos' & %Hlen' & Hslice2)".

      iPoseProof (pointsto_valid_2 with "Ha Ha'") as "(_ & %Heq)".
      inversion_clear Heq.

      unfold isSlice. length.

      iPoseProof (big_sepLZ2_app with "Hslice1 Hslice2") as "Hslice".
      rewrite -(split_seg (i + length xs)); try lia.
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame "∗#%".
  Qed.

  (* We can split a slice on an index [j] of the model [xs].

     This results in two slices with models
     [seg 0 j xs] and [seg j (length xs) xs]. *)

  Lemma split_Slice `{Encode A} (j : Z) dq a i (xs : list A) :
    0 ≤ j ≤ length xs →
    a ↦∗[i]{dq} xs ⊣⊢ a ↦∗[i]{dq} (seg 0 j xs) ∗ a ↦∗[i + j]{dq} (seg j (length xs) xs).
  Proof.
    lengths.
    rewrite -{1}(seg_all 0 (length xs) xs); try lia.
    rewrite (split_seg j); try lia.
    rewrite (Slice_app (i + j)).
    reflexivity. length. lia.
  Qed.

  Lemma slice_of_own `{Encode A} (a : array) (xs : list A) n :
    n = length xs →
    ownArray a xs ⊣⊢ isArray a n ∗ a ↦∗ xs.
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
    iApply imp_bind.
    { iApply imp_allocn. iIntros "!>" (ls) "Hls". iExact "Hls". }
    iIntros (arr) "Hls". iApply imp_ret; first encode.
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlenls".
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenxs".
    iFrame. simpl.
    iSplitR.
    - iPureIntro.
      length_nonneg es; rewrite Hlenls Hlenxs Hleneq; lia.
    - iSplit. { iPureIntro; lia. }
      rewrite -Hlenls.
      by seg.
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
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_int with "He1"). }
    iIntros (? a) "->  Hφ /=".
    rewrite signed_repr; last representable.
    case_decide; last contradiction.
    iApply imp_bind.
    { rewrite <- fmap_replicate. iApply imp_allocn.
      iIntros "!>" (ls) "Hpts". iExact "Hpts". }
    iIntros (arr) "!> Hpts".
    iApply imp_ret; first encode.
    iPoseProof (big_sepLZ2_length with "Hpts") as "%Hlen'".
    simpl. length in Hlen'.
    iFrame.
    iSplitR. { iPureIntro; length; lia. }
    iSplit. { iPureIntro; length; lia. }
    by seg.
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
                   ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ a ↦∗[j]{dq} xs) ∗
                   ▷ (a ↦∗[j]{dq} xs -∗ Φ (xs !!! (i - j)))) -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] [He2]").
    { iApply (imp_as_array with "He1"). }
    { iApply (imp_as_int with "He2"). }
    iIntros (a i) "HΦ1 HΦ2".
    iDestruct ("P" with "HΦ1 HΦ2") as
      "(%n & #Harr & %dq & %j & %xs & >Hslice & Hlookup)".
    iDestruct "Harr" as "(%Hlen' & %Hbound)".
    iDestruct "Hslice" as "(%Hle & %Hlt & (%Hlen & Hslice))".
    simpl.
    rewrite signed_repr; last representable.
    rewrite list_lookup_lookup_total_valid; last lia.
    (* Subgoal: [load (a !!! i)] *)
    iPoseProof (big_sepLZ2_lookup_seg_acc i with "Hslice")
      as "(Hl & Hslice)"; try lia.
    iApply (imp_load' with "Hl").
    iIntros "!> !> Hl".
    iApply "Hlookup".
    iSplit. { iPureIntro; apply Hlen. }
    iApply ("Hslice" with "Hl").
  Qed.

  Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} a (n : Z) (i j : Z) dq (xs : list A) x e1 e2 :
    ⌜j ≤ i⌝ -∗
    ⌜i - j < length xs⌝ -∗
    ⌜xs !!! (i - j) = x⌝ -∗
    isArray a n -∗
    ▷ a ↦∗[j]{dq} xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ v, ⌜v = x⌝ ∗ a ↦∗[j]{dq} xs }}.
  Proof.
    iIntros (Hi Hlookup Hlen) "#Harr Hslice He1 He2".
    iApply (imp_EArrayGet2 with "He1 He2").
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
                     ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ a ↦∗[j] xs) ∗
                     ▷ (a ↦∗[j] (<[i - j := y]> xs) -∗ Φ ())) -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 He3 P". simpl_eval.
    iApply (imp_bind_par (A2:=(Z * A)) with "[He1] [He2 He3]").
    { iApply (imp_as_array with "He1"). }
    { iApply (imp_par with "[He2] He3").
      iApply (imp_as_int with "He2"). }
    iIntros (a (i & y)) "HΦ1 (HΦ2 & HΦ3)".
    iDestruct ("P" with "HΦ1 HΦ2 HΦ3")
      as "(%n & #Harr & %j & %xs & >(%Hle & %Hlt & Hslice) & HΦ)".
    iDestruct "Harr" as "(%Hlen' & %Hbound)".
    iDestruct "Hslice" as "(%Hlen & Hslice)".
    simpl.
    rewrite signed_repr; last representable.
    rewrite list_lookup_lookup_total_valid; last lia.
    (* Subogal: [store (a !!! i) #y] *)
    iPoseProof (big_sepLZ2_insert_seg_acc i with "Hslice")
      as "(Hl & Hslice)"; try lia.

    iApply (imp_store' with "Hl").
    iIntros "!> !> Hl".
    iApply "HΦ".
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
    ▷ a ↦∗[j] xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a'=a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i'=i⌝ }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (_ : unit), ∃ y, Φ y ∗ a ↦∗[j] (<[i-j:=y]> xs) }}.
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
