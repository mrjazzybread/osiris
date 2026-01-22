From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.reasoning_rules Require Import basic_rules stop_rules expr_rules.

Section array_resources.

  Context `{!osirisGS Σ}.

  Definition isArray (a : val) (n : nat) : iProp Σ :=
    ∃ (ls : list loc),
      ⌜a = VArray ls⌝ ∗
      ⌜length ls = n⌝ ∗
      ⌜Z.of_nat n < max_array⌝.

  Global Instance is_array_persistent a n : Persistent (isArray a n).
  Proof. apply _. Qed.

  Definition isSlice `{Encode A} dq (a : val) (i : nat) (xs : list A) : iProp Σ :=
    ∃ (ls : list loc),
      ⌜a = VArray ls⌝ ∗ ⌜(i + length xs ≤ length ls)%nat⌝ ∗
      [∗ list] l;x ∈ take (length xs) (drop i ls); xs, pointsto l dq (V #x).

  Lemma leq_length {A} i (l : list A) :
    (i ≤ length l)%nat →
    ∃ li lrest, l = li ++ lrest ∧ i = length li.
  Proof.
    intros Hle.
    exists (take i l), (drop i l).
    split. by rewrite take_drop. rewrite length_take. lia.
  Qed.

  Lemma eq_length {A} i j (l : list A) :
    (i + j = length l)%nat →
    ∃ li lj, l = li ++ lj ∧ i = length li ∧ j = length lj.
  Proof.
    intros Heq.
    exists (take i l), (drop i l).
    split. by rewrite take_drop. rewrite length_take length_drop. lia.
  Qed.

  Local Lemma decompose_list {A} i j k (ls : list A) :
    (i + j + k ≤ length ls)%nat →
    ∃ li lys lzs lextra,
      ls = li ++ lys ++ lzs ++ lextra ∧
      i = length li ∧ j = length lys ∧ k = length lzs.
  Proof.
    intros constraint.
    apply leq_length in constraint as (l' & lextra & -> & Hlen).
    apply eq_length in Hlen as (l1 & l2 & -> & Hlen1 & Hlen2).
    apply eq_length in Hlen1 as (l1' & l2' & -> & Hlen1' & Hlen2').
    exists l1', l2', l2, lextra.
    rewrite !app_assoc. auto.
   Qed.

   Lemma split_Slice `{Encode A} dq a (i j : nat) (xs ys zs : list A) :
     j = (i + length ys)%nat →
     xs = ys ++ zs →
     isSlice dq a i xs ⊣⊢ (isSlice dq a i ys ∗ isSlice dq a j zs).
   Proof.
     intros -> ->.
     iStartProof; iSplit; iIntros "Hslice".
     - iDestruct "Hslice" as "(%ls & -> & %Hlen & Hslice)".
       rewrite length_app Nat.add_assoc in Hlen.
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       destruct (decompose_list _ _ _ ls Hlen) as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       rewrite Hlen1 drop_app_length.
       rewrite {1}app_assoc.
       rewrite length_app. rewrite {1}Hlen2 {1}Hlen3. rewrite <- length_app.
       rewrite take_app_length.
       iPoseProof (big_sepL2_app_inv with "Hslice") as "[Hslice1 Hslice2]". auto.
       iSplitL "Hslice1".
       + iExists _. iSplit; first done. iSplit.
         { iPureIntro. rewrite !length_app. lia. }
         rewrite drop_app_length. rewrite Hlen2.
         rewrite take_app_length. iApply "Hslice1".
       + iExists _. iSplit; first done. iSplit.
         { iPureIntro. rewrite !length_app. lia. }
         rewrite Hlen2.
         rewrite <- (length_app li lys).
         rewrite app_assoc drop_app_length.
         rewrite Hlen3 take_app_length. iApply "Hslice2".
     - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
       iDestruct "Hslice1" as "(%ls & %Harr & %Hlen & Hslice1)".
       iDestruct "Hslice2" as "(%ls' & %Harr' & %Hlen' & Hslice2)".
       rewrite Harr' in Harr. inversion Harr; subst.
       iExists ls. iSplit; first done. iSplit.
       { iPureIntro. rewrite length_app. lia. }
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       destruct (decompose_list _ _ _ ls Hlen') as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       rewrite Hlen1 drop_app_length.
       rewrite length_app Hlen2 Hlen3. rewrite <- !length_app.
       rewrite {3}app_assoc !take_app_length.
       iApply (big_sepL2_app with "Hslice1 [Hslice2]").
       rewrite app_assoc drop_app_length take_app_length.
       iApply "Hslice2".
   Qed.

   Definition isArrayCell `{Encode A} dq (a : val) (i : nat) (x : A) : iProp Σ := isSlice dq a i [x].

 End array_resources.

 Section array_reasoning.

   Context `{!osirisGS Σ}.

   Context {ι : thread} {η : env} {E : coPset} {Ψ : iEff Σ}.

   Lemma ewp_EArrayLength n e :
     EWP[ι] eval η e @ E <|Ψ|> {{ ensures a, isArray a n }} -∗
     EWP[ι] eval η (EArrayLength e) @ E <|Ψ|> {{ ensures #n', ⌜n' = n⌝ }}.
   Proof.
     iIntros "He".
     simpl_eval.
     iApply ewp_bind.
     iApply ewp_bind.
     iApply (ewp_mono with "He").
     iIntros ([|]); [ | iIntros ([]) ].
     iIntros "#Harray". simpl.
     iDestruct "Harray" as "(%ls & -> & %Hlen & %Hbound)".
     iApply ewp_ret. iApply ewp_ret.
     iExists n. rewrite Hlen.
     auto.
   Qed.

   Lemma ewp_EArrayMake `{Encode A} {e1 e2} n (φ : A → iProp Σ) :
     ⌜Z.of_nat n < max_array⌝ -∗
     EWP[ι] eval η e1 @ E <|Ψ|> {{ ensures #i, ⌜i=n⌝ }} -∗
     EWP[ι] eval η e2 @ E <|Ψ|> {{ ensures #x, φ x }} -∗
     EWP[ι] eval η (EArrayMake e1 e2) @ E <|Ψ|>
       {{ ensures a, ∃ x, φ x ∗ isArray a n ∗ isSlice (DfracOwn 1) a 0 (repeat x n) }}.
   Proof.
     iIntros (Hbound) "He1 He2".
     simpl_eval.
     iApply (ewp_Par with "[He1] He2").
     - iApply ewp_bind. iApply (ewp_mono with "He1").
       iIntros ([|]); [ | iIntros ([]) ].
       iIntros "(%v & -> & ->) /=".
       rewrite (signed_repr n).
       assert (n >=? 0 = true) as -> by apply Z.geb_le, Nat2Z.is_nonneg.
       iApply ewp_ret.
       instantiate (1 := (λ o, match o with O2Ret i => ⌜i = n⌝ | O2Throw _ => False end)%I).
       simpl. iPureIntro. apply Nat2Z.id.
       pose proof (h := (Z.lt_trans n max_array max_signed Hbound max_array_length)).
       constructor; last lia.
       transitivity 0. rewrite min_signed_eq.
       apply Z.opp_nonpos_nonneg. apply Z.lt_le_incl, Z.gt_lt.
       apply Coqlib.two_power_nat_pos.
       apply Nat2Z.is_nonneg.
     - iIntros (? []).
     - iIntros (? []).
     - iIntros (i a ->) "Hφ".
       iNext. iApply ewp_bind. iApply ewp_ret. simpl.
       assert (n <? max_array = true) as -> by apply Z.ltb_lt, Hbound.
       iApply ewp_allocn.
       iIntros "!>" (ls) "(%Hlen & Hpts)".
       iApply ewp_ret. simpl.
       iDestruct "Hφ" as "(%x & -> & Hφ)".
       iFrame.
       iSplitR.
       iExists ls; auto.
       iExists ls. iSplit; first done.
       iSplit; first iPureIntro.
       rewrite repeat_length. lia.
       rewrite drop_0. rewrite repeat_length. rewrite <- Hlen, firstn_all.
       iApply big_sepL2_alt.
       iSplit; first (iPureIntro; by rewrite repeat_length).
       clear Hlen.
       iInduction ls as [|l ls IH].
       + done.
       + iApply big_sepL_cons.
         iPoseProof (big_sepL_cons with "Hpts") as "($ & Hpts)".
         iApply ("IH" with "Hpts").
   Qed.

   Lemma ewp_EArrayUnsafeGet `{Encode A} a (n : nat) (i j : nat) dq (xs : list A) x e1 e2 :
     ⌜(0 ≤ i < n)%nat⌝ -∗
     ⌜xs !! i = Some x⌝ -∗
     isArray a n -∗
     isSlice dq a j xs -∗
     EWP[ι] eval η e1 @ E <|Ψ|> {{ ensures a', ⌜a' = a⌝ }} -∗
     EWP[ι] eval η e2 @ E <|Ψ|> {{ ensures #i', ⌜i' = i⌝ }} -∗
     EWP[ι] eval η (EArrayUnsafeGet e1 e2) @ E <|Ψ|> {{ ensures #v, ⌜v=x⌝ ∗ isSlice dq a j xs }}.
   Proof.
     iIntros (Hi Hlookup) "#Harr Hslice He1 He2".
     iDestruct "Hslice" as "(%ls & -> & %Hlen & Hslice)".
     iDestruct "Harr" as "(%ls' & -> & %Hlen' & %Hbound)".
     simpl_eval.
     iApply (ewp_Par with "[He1] [He2]").
     - iApply ewp_bind. iApply (ewp_mono with "He1").
       iIntros ([|]); [ | iIntros ([]) ].
       iIntros (->).
       iApply ewp_ret.
       instantiate (1 := (λ o, match o with O2Ret ls => ⌜ls = ls'⌝ | O2Throw _ => False end)%I).
       auto.
     - iApply ewp_bind. iApply (ewp_mono with "He2").
       iIntros ([|]); [ | iIntros ([]) ].
       iIntros "(%v & -> & ->) /=".
       rewrite (signed_repr i).
       assert (i >=? 0 = true) as -> by apply Z.geb_le, Nat2Z.is_nonneg.
       iApply ewp_ret.
       instantiate (1 := (λ o, match o with O2Ret i' => ⌜i' = i⌝ | O2Throw _ => False end)%I).
       simpl. iPureIntro. apply Nat2Z.id.
       constructor.
       transitivity 0. rewrite min_signed_eq.
       apply Z.opp_nonpos_nonneg. apply Z.lt_le_incl, Z.gt_lt.
       apply Coqlib.two_power_nat_pos.
       lia.
       transitivity n. lia.
       pose proof (h := (Z.lt_trans n max_array max_signed Hbound max_array_length)).
       lia.
     - iIntros (? []).
     - iIntros (? []).
     - iIntros (? ? -> ->).
       iNext.
       iApply ewp_bind. iApply ewp_ret. simpl.
       admit.
   Admitted.

   Lemma ewp_EArrayGet `{Encode A} a (n : nat) (i : nat) e1 e2 φ :
     isArray a n -∗
     isSlice dq a j xs -∗
     EWP[ι] eval η e1 @ E <|Ψ|> {{ ensures a', ⌜a' = a⌝ }} -∗
     EWP[ι] eval η e2 @ E <|Ψ|> {{ ensures #i', ⌜i' = i⌝ }} -∗
     (∀ a, ∃ dq (j : nat) (xs : list A),
             isSlice dq a j xs ∗ ▷ (isSlice dq a j xs -∗ ∃ x, ⌜xs !! (i - j)%nat = Some x⌝ ∗ φ x)) -∗
     EWP[ι] eval η (EArrayGet e1 e2) @ E <|Ψ|> {{ ensures #x, φ x }}.
   Proof.
     iIntros "#Harr He1 He2 Hmono".
     simpl_eval.
     iApply (ewp_Par with "[He1] [He2]").
     - iApply ewp_bind. iApply (ewp_mono with "He1").
       iIntros ([|]); [ | iIntros ([]) ].
       iIntros (->). iDestruct "Harr" as "(%ls & -> & %Hlen & %Hbound)".
       iApply ewp_ret.
       instantiate (1 := (ensures ls, ∃ n, ⌜length ls = n⌝ ∗ ⌜n ≤ max_array⌝)%I).
       iExists n; auto.
     - iApply ewp_bind. iApply (ewp_mono with "He2").
       iIntros ([|]); [ | iIntros ([]) ].
       iIntros "(%v & -> & ->) /=".


     iApply ewp_bind.
     iApply (ewp_mono with "He").
     iIntros ([|]); [ | iIntros ([]) ].
     iIntros "#Harray". simpl.
     iDestruct "Harray" as "(%ls & -> & %Hlen & %Hbound)".
     iApply ewp_ret. iApply ewp_ret.
     iExists n. rewrite Hlen.
     auto.
   Qed.



End array_reasoning.
