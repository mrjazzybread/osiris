From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z.

Section array_resources.

  Context `{!osirisGS Σ}.

  Definition isArray (a : val) (n : Z) : iProp Σ :=
    ∃ (ls : list loc),
      ⌜a = VArray ls⌝ ∗
      ⌜length ls = n⌝ ∗
      ⌜0 ≤ n < max_array⌝.

  Global Instance is_array_persistent a n : Persistent (isArray a n).
  Proof. apply _. Qed.

  Definition isSlice `{Encode A} dq (a : val) (i : Z) (xs : list A) : iProp Σ :=
    ∃ (ls : list loc),
      ⌜a = VArray ls⌝ ∗ ⌜0 ≤ i ∧ i + length xs ≤ length ls⌝ ∗
      [∗ list] l;x ∈ take (length xs) (drop i ls); xs, pointsto l dq (V #x).

  Lemma leq_length {A} (i : Z) (l : list A) :
    0 ≤ i ≤ length l →
    ∃ li lrest, l = li ++ lrest ∧ i = length li.
  Proof.
    intros Hpos.
    exists (take i l), (drop i l).
    split. by rewrite take_drop. rewrite length_take.
    lia.
  Qed.

  Lemma eq_length {A} (i j : Z) (l : list A) :
    0 ≤ i ∧ 0 ≤ j →
    i + j = length l →
    ∃ li lj, l = li ++ lj ∧ i = length li ∧ j = length lj.
  Proof.
    intros Hpos Heq.
    exists (take i l), (drop i l).
    split. by rewrite take_drop. rewrite length_take length_drop. lia.
  Qed.

  Local Lemma decompose_list {A} (i j k : Z) (ls : list A) :
    (0 ≤ i ∧ 0 ≤ j ∧ 0 ≤ k) →
    (i + j + k ≤ length ls) →
    ∃ li lys lzs lextra,
      ls = li ++ lys ++ lzs ++ lextra ∧
      i = length li ∧ j = length lys ∧ k = length lzs.
  Proof.
    intros Hpos constraint.
    assert (0 ≤ i + j + k ∧ i + j + k ≤ length ls) as Hpos' by lia.
    apply leq_length in Hpos' as (l' & lextra & -> & Hlen).
    apply eq_length in Hlen as (l1 & l2 & -> & Hlen1 & Hlen2); last lia.
    apply eq_length in Hlen1 as (l1' & l2' & -> & Hlen1' & Hlen2'); last lia.
    exists l1', l2', l2, lextra.
    rewrite !app_assoc. auto.
  Qed.

  Local Lemma cut_out_slice {A} (i j : Z) (ls : list A) :
    (0 ≤ i ∧ 0 ≤ j) →
    (i + j ≤ length ls) →
    ∃ li slice lextra,
      ls = li ++ slice ++ lextra ∧
      i = length li ∧ j = length slice.
  Proof.
    intros Hpos constraint.
    assert (0 ≤ i + j ∧ i + j ≤ length ls) as Hpos' by lia.
    apply leq_length in Hpos' as (l' & lextra & -> & Hlen).
    apply eq_length in Hlen as (l1 & l2 & -> & Hlen1 & Hlen2); last lia.
    exists l1, l2, lextra. rewrite app_assoc. auto.
  Qed.

   Lemma split_Slice `{Encode A} dq a (i j : Z) (xs ys zs : list A) :
     j = i + length ys →
     xs = ys ++ zs →
     isSlice dq a i xs ⊣⊢ (isSlice dq a i ys ∗ isSlice dq a j zs).
   Proof.
     intros -> ->.
     iStartProof; iSplit; iIntros "Hslice".
     - iDestruct "Hslice" as "(%ls & -> & [%Hpos %Hlen] & Hslice)".
       rewrite length_app in Hlen.
       replace (i + (length ys + length zs))
         with (i + length ys + length zs) in Hlen by lia.
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       assert (0 ≤ length ys)%Z by apply (length_nonneg).
       assert (0 ≤ length zs)%Z by apply (length_nonneg).
       assert (0 ≤ i ∧ 0 ≤ length ys ∧ 0 ≤ length zs) as Hpos' by lia.
       destruct (decompose_list _ _ _ ls Hpos' Hlen)
         as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       drop. take.
       iPoseProof (big_sepL2_app_inv with "Hslice") as "[Hslice1 Hslice2]".
       { rewrite /length in Hlen2. lia. }
       iSplitL "Hslice1".
       + iExists _. iSplit; first done. iSplit.
         { iPureIntro. rewrite !length_app in Hlen |-*. lia. }
         drop. take.
         iApply "Hslice1".
       + iExists _. iSplit; first done. iSplit.
         { iPureIntro. rewrite !length_app in Hlen |- *. lia. }
         drop. take.
         iApply "Hslice2".
     - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
       iDestruct "Hslice1" as "(%ls & %Harr & [%Hpos %Hlen] & Hslice1)".
       iDestruct "Hslice2" as "(%ls' & %Harr' & [%Hpos' %Hlen'] & Hslice2)".
       rewrite Harr' in Harr; inversion Harr; subst.
       iExists ls. iSplit; first done. iSplit.
       { iPureIntro. rewrite length_app. lia. }
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       assert (0 ≤ length ys) by apply length_nonneg.
       assert (0 ≤ length zs) by apply length_nonneg.
       assert (0 ≤ i ∧ 0 ≤ length ys ∧ 0 ≤ length zs) as Hpos'' by lia.
       destruct (decompose_list _ _ _ ls Hpos'' Hlen')
         as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       drop. take.
       iApply (big_sepL2_app with "Hslice1 Hslice2").
   Qed.

   Definition isArrayCell `{Encode A} dq (a : val) (i : nat) (x : A) : iProp Σ :=
     isSlice dq a i [x].

 End array_resources.

 Section array_reasoning.

   Context `{!osirisGS Σ}.

   Context {η : env} {E : coPset} {Ψ : iEff Σ}.

   Lemma imp_EArrayLength {ζ} (n : Z) e :
     imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, isArray a n }} -∗
     imp eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n', ⌜n' = n⌝ }}.
   Proof.
     iIntros "He". simpl_eval.
     iApply (imp_bind _ _ (λ ls, ret (VInt (repr (length ls)))) with "[He]").
     { rewrite /as_array.
       iApply (imp_bind _ _ (λ v, val_as_array v) with "He").
       iIntros (a) "#Harray".
       iDestruct "Harray" as "(%ls & -> & Harray)". simpl.
       iApply (imp_ret ls ls).
       instantiate (1 := Build_Observe (list loc) _ (list loc) id). reflexivity.
       iExact "Harray". }
     iIntros (ls) "(%Hlen & %Hbound)".
     change (♯ls) with ls.
     iApply (imp_ret (VInt (repr (length ls))) (length ls)%Z). encode.
     iPureIntro. lia.
   Qed.

   Lemma array_size_representable i :
     0 ≤ i < max_array →
     representable i.
   Proof.
     intros (Hpos & Hlt).
     constructor.
     - rewrite min_signed_eq.
       transitivity 0; last assumption.
       apply Z.opp_nonpos_nonneg. apply Z.lt_le_incl, Z.gt_lt.
       apply Coqlib.two_power_nat_pos.
     - pose proof (h := (Z.lt_trans i max_array max_signed Hlt max_array_length)).
       apply Z.lt_le_incl, h.
   Qed.

   Lemma list_elem_of_split_length {A : Type} (l : list A) (i : Z) (x : A) :
     l !! i = Some x → ∃ l1 l2 : list A, l = l1 ++ x :: l2 ∧ i = length l1.
   Proof.
     intros Hlookup.
     pose proof (list_z.lookup_lt_Some l i x Hlookup) as Hvalid.
     rewrite /lookup /listz_lookup in Hlookup.
     rewrite /list_z.length in Hvalid.
     rewrite (decide_False) in Hlookup; last lia.
     pose proof (list_elem_of_split_length _ _ _ Hlookup)
       as (l1 & l2 & -> & Hlength).
     eexists l1, l2; split; [ reflexivity | ].
     rewrite /length. lia.
   Qed.

   Lemma unroll_replicate {A : Type} (a : A) n :
     n >= 1 → replicate n a = a :: replicate (n - 1) a.
   Proof.
     intros Hgeq.
     rewrite /replicate /init /list_basics_extra.init.
     case_decide; first lia.
     case_decide; first lia.
     assert (Z.to_nat n = S (Z.to_nat (n - 1))) as -> by lia.
     generalize (Z.to_nat (n - 1)). intros k. simpl. f_equal.
     generalize 1%nat. generalize 0%nat.
     induction k.
     - done.
     - intros. simpl.
       f_equal. apply IHk.
   Qed.

   Lemma imp_EArrayMake `{Encode A} {ζ} {e1 e2} (n : Z) (Φ : A → iProp Σ) :
     ⌜0 ≤ n < max_array⌝ -∗
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, ⌜i = n⌝ }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
     imp eval η (EArrayMake e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
       {{ λ a, ∃ x, Φ x ∗ isArray a n ∗ isSlice (DfracOwn 1) a 0 (replicate n x) }}.
   Proof.
     iIntros (Hbound) "He1 He2". simpl_eval.
     iApply (@imp_Par _ _ val val exn _ _
               _ _ _ _ _ _ _ _ _ _ _ _ _
               _ _ _ _ (as_int (eval η e1)) _ (pfbind inject2
               (λ '(n0, v),
                  if ((0 <=? signed n0) && (signed n0 <? max_array))%bool
                  then
                   Stop CAllocn (replicate (signed n0) v)
                     (pfbind inject2 (λ ls : list loc, ret (VArray ls)))
                  else crash "invalid_argument: Array.make")) with "[He1] He2").
     { rewrite /as_int.
       iApply (imp_bind _ _ (λ v, val_as_int v) with "He1").
       iIntros (?) "-> /=".
       iApply (imp_ret (repr n) n). instantiate (1 := Build_Observe Z _ int repr). reflexivity.
       instantiate (1 := (λ i, ⌜i = n⌝)%I). done. }
     iSplit; last iSplit.
     - iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ").
     - iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ").
     - iIntros (? a) "-> Hφ !>".
       rewrite /continue /=.
       rewrite bind_ret.
       rewrite signed_repr; last apply array_size_representable, Hbound.
       assert (0 <=? n = true) as -> by lia.
       assert (n <? max_array = true) as -> by lia.
       iApply imp_allocn.
       iIntros "!>" (ls) "Hpts".
       iPoseProof (big_sepL2_length with "Hpts") as "%Hlen'".
       assert (length ls = n) as Hlen.
       { pose proof (length_replicate n #a) as Hlen_z.
         rewrite /length in Hlen_z |- *. lia. }
       rewrite /continue /=.
       iApply imp_ret. encode.
       iFrame.
       iSplitR.
       { iExists ls; auto. }
       iExists ls. iSplit; first done.
       rewrite length_replicate.
       iSplit; first (iPureIntro; lia).
       drop. take.
       iApply big_sepL2_alt.
       iSplit; first iPureIntro.
       { pose proof (length_replicate n a) as Hlen_z.
         pose proof (length_replicate n #a) as Hlen_z'.
         rewrite /length in Hlen_z, Hlen_z'. lia. }
       clear Hlen Hlen'.
       iInduction ls as [|l ls IH] forall (n Hbound).
       + done.
       + simpl.
         iPoseProof (big_sepL2_length with "Hpts") as "%Hlen".
         assert (n >= 1) as Hgt_1.
         { pose proof (length_replicate n #a). rewrite /length in H0.
           rewrite <- Hlen in H0. simpl in H0.
           lia. }
         rewrite (unroll_replicate a n Hgt_1).
         rewrite (unroll_replicate #a n Hgt_1).
         iDestruct "Hpts" as "($ & Hpts)".
         iApply ("IH" with "[] Hpts").
         iPureIntro. lia.
   Qed.

   Lemma imp_EArrayUnsafeGet2 `{Encode A, Inhabited A} {Φ : A → iProp Σ} {ζ} (Φ1 : val → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 :
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, ∃ n, isArray a n ∗ Φ1 a }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, Φ2 i }} -∗
     (∀ a i, Φ1 a -∗ Φ2 i -∗
             ∃ n, isArray a n ∗
             ∃ dq j xs (x : A),
               ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ isSlice dq a j xs ∗ ⌜xs !!! (i - j) = x⌝) ∗
               ▷ (isSlice dq a j xs -∗ Φ x)) -∗
     imp eval η (EArrayUnsafeGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
   Proof.
     iIntros "He1 He2 P". simpl_eval.
     iApply (imp_Par _ _ _ _ _ _ (pfbind inject2
               (λ '((ls0, i0) : list loc * int),
                  match ls0 !! signed i0 with
                  | Some l => load l
                  | None => crash "index out of bounds"
                  end)) with "[He1] [He2]").
     { rewrite /as_array.
       iApply (imp_bind _ _ (λ v, val_as_array v) with "He1").
       iIntros (a) "(%n & (%ls & -> & Harr) & HΦ1)".
       iApply (imp_ret ls ls).
       instantiate (1 := Build_Observe (list loc) _ (list loc) id). reflexivity.
       instantiate (1 := (λ ls', Φ1 (VArray ls'))%I). done. }
     { rewrite /as_int.
       iApply (imp_bind _ _ (λ v, val_as_int v) with "He2").
       iIntros (i) "HΦ2".
       iApply (imp_ret (repr i) i).
       instantiate (1 := Build_Observe (Z) _ (int) repr). reflexivity.
       iExact "HΦ2". }
     iSplit; last iSplit.
     { iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ"). }
     { iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ"). }
     iIntros (ls i) "HΦ1 HΦ2".
     iDestruct ("P" with "HΦ1 HΦ2")
       as "(%n & #Harr & %dq & %j & %xs & %x & P)".
     rewrite /continue /= bind_ret.
     iNext.
     iDestruct "P" as "((%Hle & %Hlt & Hslice & %Htotal_lookup) & P)".

     iDestruct "Harr" as "(% & %Heq & %Hlen' & %Hbound)".
     iDestruct "Hslice" as "(% & %Heq' & %Hlen & Hslice)".
     inversion Heq; subst ls0; clear Heq.
     inversion Heq'; subst ls1; clear Heq'.

     (* Decompose [ls] into [lj ++ slice ++ _]. *)
     pose proof (cut_out_slice j (length xs) ls ltac:(lia) ltac:(lia))
       as (lj & slice & lextra & Hls & Hj & Hslice).
     (* Turn [take _ (drop _ ls)] into [slice]. *)
     rewrite Hj {1}Hls. drop.
     rewrite Hslice. take.

     assert (¬ (i - j < 0)) as Heqf by lia.

     rewrite (signed_repr i); last (apply array_size_representable; lia).
     assert (list_z.valid (i - j) xs) as Hvalid by lia.
     pose proof (list_lookup_lookup_total_valid xs (i - j) Hvalid) as Hlookup.

     (* [Decompose [xs] intl [xk ++ x :: _]. *)
     pose proof (list_elem_of_split_length xs (i - j) _ Hlookup)
       as (xk & xrest & Hxs & Hxk).
     rewrite {1}Hxs.

     (* Inversions on [Hslice] gives us that
        [slice] = [slicek ++ l :: _]. *)
     iDestruct (big_sepL2_app_inv_r with "Hslice")
       as "(%slicek & %slice' & -> & Hslice1 & Hslice2)".
     iDestruct (big_sepL2_cons_inv_r with "Hslice2") as
       "(%l & %slicerest & -> & Hl & Hslice2)".

     (* We can now prove that [ls !! i] = [Some l]. *)
     rewrite {2}Hls lookup_app_r; last lia.
     rewrite <- Hj.
     rewrite <- app_assoc. iPoseProof (big_sepL2_length with "Hslice1") as "%Hleneq".
     assert (length ls = j + length slicek + 1 + length slicerest + length lextra).
     { rewrite Hls. rewrite !length_app. rewrite length_cons. lia. }
     assert (length slicek = length xk) by (rewrite /length; lia).
     rewrite lookup_app_r; last lia.
     assert (i - j - length slicek = 0) as -> by lia.
     rewrite <- app_comm_cons.
     rewrite lookup_cons_eq_0.

     iApply (imp_load with "Hl").
     rewrite /continue; iIntros "!> Hl /=".
     iApply imp_ret. encode. rewrite Htotal_lookup. iApply "P".
     iCombine ("Hl Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_cons (λ _ l' x', pointsto l' dq (V #x')) with "Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_app with "Hslice1 Hslice2") as "Hslice".
     iExists ls. iSplit; first auto. iSplit.
     { iPureIntro. lia. }
     rewrite {1}Hls.
     rewrite Hj. rewrite drop_app drop_all Z.sub_diag drop_none. simpl.
     assert (length xs = length (slicek ++ l :: slicerest)) as -> by lia.
     rewrite take_app_length.
     rewrite Hxs. rewrite Htotal_lookup.
     iApply "Hslice".
   Qed.

   Lemma imp_EArrayUnsafeGet `{Encode A, Inhabited A} {ζ} a (k n : Z) (i j : Z) dq (xs : list A) x e1 e2 :
     ⌜j ≤ i⌝ -∗
     ⌜i - j < length xs⌝ -∗
     ⌜xs !!! (i - j)%Z = x⌝ -∗
     isArray a n -∗
     ▷ isSlice dq a j xs -∗
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
     imp eval η (EArrayUnsafeGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
           {{ λ v, ⌜v = x⌝ ∗ isSlice dq a j xs }}.
   Proof.
     iIntros (Hi Hlookup Hlen) "#Harr Hslice He1 He2".
     iApply (imp_EArrayUnsafeGet2 with "[He1] He2").
     { iApply (imp_mono_ret with "He1").
       iIntros (?) "->". iFrame "#".
       instantiate (1 := (λ a', ⌜a' = a⌝)%I). done. }
     iIntros (? ?) "-> ->".
     iFrame "#".
     iFrame "%". iFrame.
     iIntros "!> $". done.
   Qed.

   Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} a (k n : Z) (i j : Z) dq (xs : list A) x e1 e2 :
     ⌜j ≤ i⌝ -∗
     ⌜i - j < length xs⌝ -∗
     ⌜xs !!! (i - j)%Z = x⌝ -∗
     isArray a n -∗
     ▷ isSlice dq a j xs -∗
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
     imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
       {{ λ v, ⌜v = x⌝ ∗ isSlice dq a j xs }}.
   Proof.
     iIntros (Hi Hlen' Hlookup) "#Harr Hslice He1 He2".
     iDestruct "Harr" as "(% & -> & %Hlen & %Hbound)".
     simpl_eval.
     iApply (imp_Par _ _ _ _ _ _ (pfbind inject2
               (λ '((ls0, i0) : list loc * int),
                  match ls0 !! signed i0 with
                  | Some l => load l
                  | None => crash "invalid_argument: index out of bounds"
                  end)) with "[He1] [He2]").
     { rewrite /as_array.
       iApply (imp_bind _ _ (λ v, val_as_array v) with "He1").
       iIntros (?) "->".
       iApply (imp_ret ls ls).
       instantiate (1 := Build_Observe (list loc) _ (list loc) id). reflexivity.
       instantiate (1 := (λ ls', ⌜ls' = ls⌝)%I). done. }
     { rewrite /as_int.
       iApply (imp_bind _ _ (λ v, val_as_int v) with "He2").
       iIntros (?) "->".
       iApply (imp_ret (repr i) i).
       instantiate (1 := Build_Observe (Z) _ (int) repr). reflexivity.
       instantiate (1 := (λ i', ⌜i' = i⌝)%I). done. }
     iSplit; last iSplit.
     { iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ"). }
     { iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ"). }
     iIntros (? ?) "-> ->".
     rewrite /continue /= bind_ret.
     iNext.

     iDestruct "Hslice" as "(% & %Heq' & %Hlen'' & Hslice)".
     inversion Heq'; subst ls0; clear Heq'.

     (* Decompose [ls] into [lj ++ slice ++ _]. *)
     pose proof (cut_out_slice j (length xs) ls ltac:(lia) ltac:(lia))
       as (lj & slice & lextra & Hls & Hj & Hslice).
     (* Turn [take _ (drop _ ls)] into [slice]. *)
     rewrite Hj {1}Hls. drop.
     rewrite Hslice. take.

     assert (¬ (i - j < 0)) as Heqf by lia.

     rewrite (signed_repr i); last (apply array_size_representable; lia).
     assert (list_z.valid (i - j) xs) as Hvalid by lia.
     pose proof (list_lookup_lookup_total_valid xs (i - j) Hvalid) as Hlookup'.

     (* [Decompose [xs] intl [xk ++ x :: _]. *)
     pose proof (list_elem_of_split_length xs (i - j) _ Hlookup')
       as (xk & xrest & Hxs & Hxk).
     rewrite {1}Hxs.

     (* Inversions on [Hslice] gives us that
        [slice] = [slicek ++ l :: _]. *)
     iDestruct (big_sepL2_app_inv_r with "Hslice")
       as "(%slicek & %slice' & -> & Hslice1 & Hslice2)".
     iDestruct (big_sepL2_cons_inv_r with "Hslice2") as
       "(%l & %slicerest & -> & Hl & Hslice2)".

     (* We can now prove that [ls !! i] = [Some l]. *)
     rewrite Hls lookup_app_r; last lia.
     rewrite <- Hj.
     rewrite <- app_assoc. iPoseProof (big_sepL2_length with "Hslice1") as "%Hleneq".
     assert (length ls = j + length slicek + 1 + length slicerest + length lextra).
     { rewrite Hls. rewrite !length_app. rewrite length_cons. lia. }
     assert (length slicek = length xk) by (rewrite /length; lia).
     rewrite lookup_app_r; last lia.
     assert (i - j - length slicek = 0) as -> by lia.
     rewrite <- app_comm_cons.
     rewrite lookup_cons_eq_0.

     iApply (imp_load with "Hl").
     rewrite /continue; iIntros "!> Hl /=".
     iApply imp_ret. encode. rewrite Hlookup. iSplit; first auto.
     iCombine ("Hl Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_cons (λ _ l' x', pointsto l' dq (V #x')) with "Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_app with "Hslice1 Hslice2") as "Hslice".
     iExists ls. iSplit; first (rewrite Hls; rewrite <- !app_assoc; auto). iSplit.
     { iPureIntro. lia. }
     rewrite {1}Hls.
     rewrite Hj. rewrite drop_app drop_all Z.sub_diag drop_none. simpl.
     assert (length xs = length (slicek ++ l :: slicerest)) as -> by lia.
     rewrite take_app_length.
     rewrite Hxs. rewrite Hlookup.
     iApply "Hslice".
   Qed.


End array_reasoning.
