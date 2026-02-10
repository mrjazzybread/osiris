From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z.

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
    [∗ list] l;x ∈ take (length xs) (drop i ls); xs, pointsto l dq (V #x).

  Arguments isSlice {_ _} dq a i xs : rename.

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
     - iDestruct "Hslice" as "([%Hpos %Hlen] & Hslice)".
       rewrite length_app in Hlen.
       replace (i + (length ys + length zs))
         with (i + length ys + length zs) in Hlen by lia.
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       assert (0 ≤ length ys)%Z by apply (length_nonneg).
       assert (0 ≤ length zs)%Z by apply (length_nonneg).
       assert (0 ≤ i ∧ 0 ≤ length ys ∧ 0 ≤ length zs) as Hpos' by lia.
       destruct (decompose_list _ _ _ a Hpos' Hlen)
         as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       rewrite /sub /seg.
       drop. take.
       iPoseProof (big_sepL2_app_inv with "Hslice") as "[Hslice1 Hslice2]".
       { rewrite /length in Hlen2. lia. }
       iSplitL "Hslice1".
       + iSplit.
         { iPureIntro. rewrite !length_app in Hlen |-*. lia. }
         rewrite /sub /seg.
         drop. take.
         iApply "Hslice1".
       + iSplit.
         { iPureIntro. rewrite !length_app in Hlen |- *. lia. }
         rewrite /sub /seg.
         drop. take.
         iApply "Hslice2".
     - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
       iDestruct "Hslice1" as "([%Hpos %Hlen] & Hslice1)".
       iDestruct "Hslice2" as "([%Hpos' %Hlen'] & Hslice2)".
       iSplit.
       { iPureIntro. rewrite length_app. lia. }
       (* Decompose [ls] into [li ++ lys ++ lzs ++ lextra]. *)
       length_nonneg ys. length_nonneg zs.
       assert (0 ≤ i ∧ 0 ≤ length ys ∧ 0 ≤ length zs) as Hpos'' by lia.
       destruct (decompose_list _ _ _ a Hpos'' Hlen')
         as (li & lys & lzs & lextra & -> & Hlen1 & Hlen2 & Hlen3).
       drop. take.
       iApply (big_sepL2_app with "Hslice1 Hslice2").
   Qed.

   Definition isArrayCell `{Encode A} dq (a : array) (i : nat) (x : A) : iProp Σ :=
     isSlice dq a i [x].

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
     imp evals η es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ xs, [∗ list] x;Φ ∈ xs;Φs, Φ x }} -∗
     imp eval η (EArrayLit es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
       {{ λ a, isArray a (length es) ∗ ∃ xs, isSlice (DfracOwn 1) a 0 xs ∗ [∗ list] x;Φ ∈ xs;Φs, Φ x }}.
   Proof.
     iIntros "[%Hleneq %Hlenbound] He". simpl_eval.
     iApply (imp_bind (A1:=list A) with "He").
     iIntros (xs) "HΦs".
     iApply (imp_allocn).
     iIntros "!>" (ls) "Hls".
     rewrite /continue /=.
     iApply (imp_ret _ ls); first encode.
     iPoseProof (big_sepL2_length with "Hls") as "%Hlenls".
     assert (length ls = length xs).
     { rewrite length_map in Hlenls. rewrite /length. lia. }
     iPoseProof (big_sepL2_length with "HΦs") as "%Hlenxs".
     assert (length xs = length Φs).
     { rewrite /length. apply inj_eq. assumption. }
     iSplit.
     { iPureIntro; length_nonneg es; lia. }
     iFrame.
     rewrite /isSlice. iSplit; first (iPureIntro; lia).
     drop. take.
     iApply (big_sepL2_fmap_r encode.encode (λ _ l v, l ↦ v)%I).
     iApply "Hls".
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

   Lemma array_size_representable i :
     0 ≤ i ≤ max_array →
     representable i.
   Proof.
     intros (Hpos & Hle).
     constructor.
     - rewrite min_signed_eq.
       transitivity 0; last assumption.
       apply Z.opp_nonpos_nonneg. apply Z.lt_le_incl, Z.gt_lt.
       apply Coqlib.two_power_nat_pos.
     - transitivity (max_array); auto.
       apply Z.lt_le_incl, max_array_length.
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

   Lemma imp_EArrayMake `{Encode A} {ζ} {e1 e2} (n : Z) (Φ : A → iProp Σ) :
     ⌜0 ≤ n ≤ max_array⌝ -∗
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, ⌜i = n⌝ }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
     imp eval η (EArrayMake e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
       {{ λ (a : array), ∃ x, Φ x ∗ isArray a n ∗ isSlice (DfracOwn 1) a 0 (replicate n x) }}.
   Proof.
     iIntros (Hbound) "He1 He2". simpl_eval.
     iApply (imp_Par (A1:=Z) (A2:=A) with "[He1] He2").
     { iApply (imp_as_int with "He1"). }
     rewrite /continue /discontinue /=.
     iSplit; last iSplit.
     - iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ").
     - iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ").
     - iIntros (? a) "-> Hφ !> /=".
       rewrite bind_ret.
       rewrite signed_repr; last apply array_size_representable, Hbound.
       assert (0 <=? n = true) as -> by lia.
       assert (n <=? max_array = true) as -> by lia.
       simpl.
       iApply (imp_allocn _ (pfbind inject2 (λ ls : list loc, ret (VArray ls)))).
       iIntros "!>" (ls) "Hpts".
       iPoseProof (big_sepL2_length with "Hpts") as "%Hlen'".
       assert (length ls = n) as Hlen.
       { pose proof (length_replicate n #a) as Hlen_z.
         rewrite /length in Hlen_z |- *. lia. }
       rewrite /continue /=.
       iApply (imp_ret (VArray ls) ls). encode.
       iFrame.
       iSplitR.
       { iPureIntro. auto. }
       iSplit.
       { iPureIntro; rewrite length_replicate. lia. }
       drop. take.
       iApply (big_sepL2_fmap_r encode.encode (λ _ l v, l ↦ v)%I).
       rewrite fmap_replicate.
       iApply "Hpts".
   Qed.

   Lemma imp_EArrayGet2 `{Encode A, Inhabited A} {Φ : A → iProp Σ} {ζ} (Φ1 : array → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 :
     imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, Φ1 a }} -∗
     imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, Φ2 i }} -∗
     (∀ a i, Φ1 a -∗ Φ2 i -∗
             ∃ n, isArray a n ∗
             ∃ dq j xs (x : A),
               ▷ (⌜j ≤ i⌝ ∗ ⌜i - j < length xs⌝ ∗ isSlice dq a j xs ∗ ⌜xs !!! (i - j) = x⌝) ∗
               ▷ (isSlice dq a j xs -∗ Φ x)) -∗
     imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
   Proof.
     iIntros "He1 He2 P". simpl_eval.
     iApply (imp_Par (A1:=array) (A2:=Z) with "[He1] [He2]").
     { iApply (imp_as_array with "He1"). }
     { iApply (imp_as_int with "He2"). }
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

     iDestruct "Harr" as "(%Hlen' & %Hbound)".
     iDestruct "Hslice" as "(%Hlen & Hslice)".

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
     iApply imp_ret; first encode.
     rewrite Htotal_lookup. iApply "P".
     iCombine ("Hl Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_cons (λ _ l' x', pointsto l' dq (V #x')) with "Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_app with "Hslice1 Hslice2") as "Hslice".
     iSplit.
     { iPureIntro. lia. }
     rewrite {1}Hls.
     rewrite Hj. rewrite drop_app drop_all Z.sub_diag drop_none. simpl.
     assert (length xs = length (slicek ++ l :: slicerest)) as -> by lia.
     rewrite take_app_length.
     rewrite Hxs. rewrite Htotal_lookup.
     iApply "Hslice".
   Qed.

   Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} a (k n : Z) (i j : Z) dq (xs : list A) x e1 e2 :
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
     { iApply (imp_mono_ret with "He1").
       iIntros (?) "->". iFrame "#".
       instantiate (1 := (λ a', ⌜a' = a⌝)%I). done. }
     iIntros (? ?) "-> ->".
     iFrame "#".
     iFrame "%". iFrame.
     iIntros "!> $". done.
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
       iSplit; last iSplit.
       - iIntros (e) "Hζ". iApply (imp_throw with "Hζ").
       - iIntros (e) "Hζ". iApply (imp_throw with "Hζ").
       - iIntros (i y) "HΦ2 HΦ3".
         iApply (imp_ret _ (i, y)); first encode.
         instantiate (1 := (λ '(i, y), Φ2 i ∗ Φ3 y)%I). iFrame. }
     iSplit; last iSplit.
     { iIntros (e) "Hζ !>".
       iApply (imp_throw with "Hζ"). }
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

     (* Decompose [ls] into [lj ++ slice ++ _]. *)
     pose proof (cut_out_slice j (length xs) a ltac:(lia) ltac:(lia))
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
     assert (length a = j + length slicek + 1 + length slicerest + length lextra).
     { rewrite Hls. rewrite !length_app. rewrite length_cons. lia. }
     assert (length slicek = length xk) by (rewrite /length; lia).
     rewrite lookup_app_r; last lia.
     assert (i - j - length slicek = 0) as -> by lia.
     rewrite <- app_comm_cons.
     rewrite lookup_cons_eq_0.

     iApply (imp_store with "Hl").
     rewrite /continue; iIntros "!> Hl /=".
     iApply imp_ret; first encode.
     iApply "P".
     iCombine ("Hl Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_cons (λ _ l' x', pointsto l' (DfracOwn 1) (V #x')) with "Hslice2") as "Hslice2".
     iPoseProof (big_sepL2_app with "Hslice1 Hslice2") as "Hslice".
     iSplit.
     { iPureIntro. rewrite length_insert. lia. }
     assert ((xk ++ y :: xrest) = <[i-j:=y]> xs) as ->.
     { rewrite Hxs.
       rewrite insert_take_drop.
       take. drop. reflexivity.
       split; first lia.
       rewrite !length_app length_cons /length.
       rewrite /length in Hxk.
       lia. }
     rewrite {1}Hls.
     rewrite Hj. rewrite drop_app drop_all Z.sub_diag drop_none. simpl.
     rewrite length_insert.
     assert (length xs = length (slicek ++ l :: slicerest)) as -> by lia.
     rewrite take_app_length.
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
