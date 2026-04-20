From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.tactics Require Import osiris_utils.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z big_opLZ.

(** This file defines array resource predicates and [imp] rules for array expressions. *)

Definition array : Type := syntax.block.

Section array_resources.

  Context `{!osirisGS Σ}.

  (* [isArray a ls] is now defined in ewp.v as a persistent ghost map entry.
     The definition, [isArray_pers], [isArray_valid], and [isArray_length] lemmas
     are all there. *)

  (* Ownership over a segment of the array. *)

  Definition isSlice `{Encode A} a dq (i : Z) (xs : list A) : iProp Σ :=
    ∃ ls, isArray a ls ∗
    ⌜0 ≤ i ≤ length ls - length xs⌝ ∗
    [∗ listZ] l;x ∈ seg i (i + length xs) ls; xs, l ↦{dq} #x.

  Lemma isSlice_isArray `{Encode A} a dq i (xs : list A) :
    isSlice a dq i xs -∗ ∃ ls, isArray a ls ∗ ⌜0 ≤ i ≤ length ls - length xs⌝.
  Proof. iIntros "(%ls & $ & $ & _)". Qed.

  (* Ownership of the whole array.
     Includes the exclusive physical block ownership [a ⤇{1} Mut ls], enabling freeze. *)

  Definition ownArray `{Encode A} (a : array) dq (xs : list A) : iProp Σ :=
    ∃ ls, isArray a ls ∗ a ⤇{dq} Mut ∗ isSlice a dq 0 xs ∗ ⌜length ls = length xs⌝.

  Lemma ownArray_isArray `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ ∃ ls, isArray a ls ∗ ⌜length ls = length xs⌝.
  Proof. iIntros "(%ls & #$ & _ & _ & $)". Qed.

  Lemma ownArray_length `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ ⌜0 ≤ length xs ≤ max_array_length⌝.
  Proof.
    iIntros "Hown".
    iPoseProof (ownArray_isArray with "Hown") as "(%ls & Ha & %Hlenls)".
    iPoseProof (isArray_length with "Ha") as "%Hboundls".
    iPureIntro. rewrite Hlenls in Hboundls.
    split; [ by length_nonneg xs | apply Hboundls ].
  Qed.

  Lemma ownArray_isSlice `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ isSlice a dq 0 xs.
  Proof. iIntros "(%ls & #Ha & _ & $ & %Hlen)". Qed.

  Lemma isSlice_ownArray `{Encode A} a dq ls (xs : list A) :
    isArray a ls -∗
    a ⤇{dq} Mut -∗
    isSlice a dq 0 xs -∗
    ⌜length ls = length xs⌝ -∗
    ownArray a dq xs.
  Proof. iIntros "#Ha Hmut $ $". iFrame "Hmut Ha". Qed.

End array_resources.

Notation "a ↦∗ dq xs" :=
    (ownArray a dq xs)
      (at level 20, dq custom dfrac at level 1, format "a  ↦∗ dq  xs") : bi_scope.
Notation "a ↦∗[ i ] dq xs" :=
  (isSlice a dq i xs)
    (at level 20, dq custom dfrac at level 1, i at level 200, format "a  ↦∗[ i ] dq  xs") : bi_scope.

Section array_resources.

  Lemma Slice_app `{!osirisGS Σ} `{Encode A} j dq a i (xs ys : list A) :
    j = i + length xs →
    a ↦∗[i]{dq} (xs ++ ys) ⊣⊢ (a ↦∗[i]{dq} xs ∗ a ↦∗[j]{dq} ys).
  Proof.
    intros ->.
    lengths.
    iSplit; iIntros "Hslice".
    - iDestruct "Hslice" as "(%ls & #$ & %Hbound & Hls)".
      length in Hbound. length.
      rewrite (split_seg (i + length xs)); try lia.
      iPoseProof (big_sepLZ2_app_inv with "Hls")
        as "($ & Hslice2)"; first (length; lia).
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame.
      iPureIntro. lia.

    - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
      iDestruct "Hslice1" as "(%ls & #Harr & %Hlen & Hslice1)".
      iDestruct "Hslice2" as "(% & #Harr' & %Hlen' & Hslice2)".
      iPoseProof (isArray_valid with "Harr Harr'") as "->".
      iFrame "#". length.

      iPoseProof (big_sepLZ2_app with "Hslice1 Hslice2") as "Hslice".
      rewrite -(split_seg (i + length xs)); try lia.
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame "∗".
      iPureIntro. lia.
  Qed.

  (* We can split a slice on an index [j] of the model [xs].

     This results in two slices with models
     [seg 0 j xs] and [seg j (length xs) xs]. *)

  Lemma split_Slice `{!osirisGS Σ} `{Encode A} (j : Z) dq ls i (xs : list A) :
    0 ≤ j ≤ length xs →
    ls ↦∗[i]{dq} xs ⊣⊢ ls ↦∗[i]{dq} (seg 0 j xs) ∗ ls ↦∗[i + j]{dq} (seg j (length xs) xs).
  Proof.
    lengths.
    rewrite -{1}(seg_all 0 (length xs) xs); try lia.
    rewrite (split_seg j); try lia.
    rewrite (Slice_app (i + j)). reflexivity.
    length; lia.
  Qed.

End array_resources.


Section array_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.

  Global Instance notval_dict : NotVal (mut_tag * list loc) := {}.
  Global Instance notval_listloc : NotVal (list loc) := {}.

  (** General [as_array] rule.  Given that the postcondition of [m] implies
      [isArray a ls] for some [a] and [ls], the [load_block] step is
      discharged automatically and [Φ ls] is delivered. *)
  Lemma imp_as_array {ζ} {Φ : list loc → iProp Σ} (Φ1 : array → iProp Σ) (m : microvx) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ (a : array), Φ1 a -∗ ∃ ls, ▷ isArray a ls ∗ Φ ls) -∗
    imp as_array m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm H".
    iApply (imp_bind with "Hm").
    iIntros (a) "HΦ1".
    iDestruct ("H" with "HΦ1") as "(%ls & #Harr & HΦ)".
    iApply (imp_bind with "[Harr]").
    { iApply (imp_load_block_ghost with "Harr"). }
    iIntros ([? ?]) "->".
    iApply (imp_ret with "HΦ"). encode.
  Qed.

  (** [as_array] rule for a pre-existing array.  Use when [isArray a ls] is
      already in context and [m] reduces to the array address [a]. *)
  Lemma imp_as_array_isArray {ζ} {Φ : list loc → iProp Σ} a ls (m : microvx) :
    ▷ isArray a ls -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
    Φ ls -∗
    imp as_array m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "#Harr Hm HΦ".
    iApply (imp_as_array (λ a', ⌜a' = a⌝)%I with "Hm").
    iIntros (a') "->".
    iExists ls. iFrame "#∗".
  Qed.

  (** [as_array] rule for a freshly allocated array.  Use when [m] allocates
      an array, producing [ownArray a ls xs]; the full ownership is preserved
      in the postcondition together with any additional frame [R a xs]. *)
  Lemma imp_as_array_ownArray `{Encode A} {ζ}
      {R : array → list A → iProp Σ} (m : microvx) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, ∃ (xs : list A), a ↦∗ xs ∗ R a xs }} -∗
    imp as_array m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ ls, ∃ a xs, a ↦∗ xs ∗ R a xs }}.
  Proof.
    iIntros "Hm".
    iApply (imp_as_array (λ a, ∃ xs, a ↦∗ xs ∗ R a xs)%I with "Hm").
    iIntros (a) "(%xs & Hown & $)".
    iPoseProof (ownArray_isArray with "Hown") as "(%ls & #Ha & %hlen)".
    iFrame "Hown". iExists ls. iFrame "#".
  Qed.

  Lemma imp_EArrayLit `{Encode A} {ζ} (Φs : list (A → iProp Σ)) es :
    ⌜length Φs = length es ∧ length es ≤ max_array_length⌝ -∗
    imp evals η es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ xs, [∗ listZ] x;Φ ∈ xs;Φs, Φ x }} -∗
    imp eval η (EArrayLit es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ a, ∃ xs, a ↦∗ xs ∗ [∗ listZ] x;Φ ∈ xs;Φs, Φ x }}.
  Proof.
    iIntros "[%Hleneq %Hlenbound] He". simpl_eval.
    iApply (imp_bind (A1:=list A) with "He").
    iIntros (xs) "HΦs".
    iApply imp_bind.
    { iApply imp_allocn. iIntros "!>" (ls) "Hls". iExact "Hls". }
    iIntros (arr) "Hls".
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlenls".
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenxs".
    iApply imp_bind.
    { iApply (imp_alloc_block arr with "[]").
      iPureIntro. rewrite Hlenls Hlenxs Hleneq. apply Hlenbound. }
    iIntros (a) "(Ha & #Harr)".
    iApply imp_ret; first encode.
    iFrame "HΦs".

    (* Goal: establish [a ↦∗ xs] from [a ⤇{1} Mut arr], [isArray a arr],
       and [∀ l x ∈ arr xs, l ↦ #x ]. *)
    iApply (isSlice_ownArray with "Harr Ha [Hls] [//]").
    iFrame "Harr". seg. iFrame "Hls".
    iPureIntro; lia.
  Qed.

  Lemma imp_EArrayEmpty `{Encode A} {ζ} :
    ⊢ imp eval η (EArrayLit []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
        {{ λ a, a ↦∗ (@nil A) }}.
  Proof.
    iApply imp_wand.
    - iApply (imp_EArrayLit (@nil (A → _))  []).
      iPureIntro; length; split; auto.
      pose proof (max_array_positive). lia.
      simpl_evals. iApply imp_ret; first encode.
      by iApply big_sepLZ2_nil.
    - iIntros (a) "(%xs & HownArr & Hxs)".
      iPoseProof (big_sepLZ2_nil_inv_r with "Hxs") as "->".
      iApply "HownArr".
  Qed.

  Lemma imp_EArrayLength' {ζ} (ls : list loc) e :
    imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, isArray a ls }} -∗
    imp eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n, ⌜n = length ls⌝ }}.
  Proof.
    iIntros "He". simpl_eval.
    iApply (imp_bind with "[He] [-]").
    - set_postcondition (λ ls', ⌜ls'=ls⌝)%I.
      iApply (imp_as_array with "He").
      iIntros (a) "#Harr". by iFrame "#".
    - iIntros (ls') "->". iApply imp_ret; first encode. auto.
  Qed.

  Lemma imp_EArrayLength `{Encode A} {ζ} dq (xs : list A) e :
    imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, a ↦∗{dq} xs }} -∗
    imp eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n, ⌜n = length xs⌝ }}.
  Proof.
    iIntros "He". simpl_eval.
    iApply (imp_bind with "[He] [-]").
    - set_postcondition (λ ls, ⌜length ls = length xs⌝)%I.
      iApply (imp_as_array with "He").
      iIntros (a) "Hown".
      iPoseProof (ownArray_isArray with "Hown") as "(% & $ & $)".
    - iIntros (ls) "<-". iApply imp_ret; first encode. auto.
  Qed.

  Lemma imp_EArrayMake `{Encode A} {ζ} {e1 e2} (n : Z) (Φ : A → iProp Σ) :
    ⌜0 ≤ n ≤ max_array_length⌝ -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i, ⌜i = n⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArrayMake e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (a : array), ∃ x, Φ x ∗ a ↦∗ (replicate n x) }}.
  Proof.
    iIntros (Hbound) "He1 He2". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_int with "He1"). }
    iIntros (? x) "->  Hφ /=".
    rewrite signed_repr; last representable.
    case_decide; last contradiction.
    iApply imp_bind.
    { rewrite <- fmap_replicate. iApply imp_allocn.
      iIntros "!>" (ls) "Hpts". iExact "Hpts". }
    iIntros (arr) "!> Hpts".
    iPoseProof (big_sepLZ2_length with "Hpts") as "%Hlen'".
    iApply imp_bind.
    { iApply (imp_alloc_block arr).
      iPureIntro. length in Hlen'. length; lia. }
    iIntros (a) "(Ha & #Harr)".

    iApply imp_ret; first encode.
    simpl. length in Hlen'.
    iFrame "Hφ".
    iFrame "#∗". seg. iFrame "Hpts".
    iPureIntro.
    length; lia.
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

  Lemma imp_EArrayGet2 `{Encode A, Inhabited A} {Φ : A → iProp Σ} {ζ} (Φ2 : Z → iProp Σ) e1 e2 a ls :
    ▷ isArray a ls -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a'=a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ i, Φ2 i -∗
          ∃ dq j xs,
            ▷ (⌜j ≤ i < j + length xs⌝ ∗ a ↦∗[j]{dq} xs) ∗
            ▷ (a ↦∗[j]{dq} xs -∗ Φ (xs !!! (i - j)))) -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "#Ha He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] [He2]").
    - iApply (imp_as_array_isArray a ls (Φ := λ ls', ⌜ls' = ls⌝%I) with "Ha He1"). auto.
    - iApply (imp_as_int with "He2").
    - iIntros (? i) "-> HΦ2".
      iDestruct ("P" with "HΦ2") as
        "(%dq & %j & %xs & >(%le & Hslice) & Hlookup)".
      iDestruct "Hslice" as "(% & #Ha' & %Hbound & Hslice)".
      iNext.
      iPoseProof (isArray_valid with "Ha Ha'") as "->".
      iPoseProof (isArray_length with "Ha") as "%Hlenls".

      simpl.
      rewrite signed_repr; last representable.
      rewrite list_lookup_lookup_total_valid; last lia.
      (* Subgoal: [load (a !!! i)] *)
      iPoseProof (big_sepLZ2_lookup_seg_acc i with "Hslice")
        as "(Hl & Hslice)"; try lia.
      iApply (imp_load' with "Hl").
      iIntros "!> Hl".
      iApply "Hlookup". iFrame "#%".
      iApply ("Hslice" with "Hl").
  Qed.

  Lemma imp_EArrayGet' `{Encode A, Inhabited A} {ζ} a (i j : Z) dq (xs : list A) e1 e2 :
    ⌜j ≤ i < j + length xs⌝ -∗
    ▷ a ↦∗[j]{dq} xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (x : A), ⌜x = xs !!! (i - j)⌝ ∗ a ↦∗[j]{dq} xs }}.
  Proof.
    iIntros (Hlen) "Hslice He1 He2".
    iDestruct "Hslice" as "(%ls & #Harr & >%Hlenls & H)".
    iApply (imp_EArrayGet2 with "Harr He1 He2").
    iIntros (?) "->".
    iExists dq, j, xs.
    iSplitL. { iFrame. iFrame "%#". }
    iIntros "!> $ //".
  Qed.

  Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} (a : array) (i j : Z) dq (xs : list A) e1 e2 :
    ⌜0 ≤ i < length xs⌝ -∗
    a ↦∗{dq} xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i' = i⌝ }} -∗
    imp eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (x : A), ⌜x = xs !!! i⌝ ∗ a ↦∗{dq} xs }}.
  Proof.
    iIntros (Hlen) "Hown He1 He2".
    iDestruct "Hown" as "(%ls & #Harr & Hblock & Hslice & %Hlenls)".
    iApply (imp_wand with "[- Hblock]").
    { iApply (imp_EArrayGet' with "[%] Hslice He1 He2").
      lia. }
    iIntros (x) "(-> & Hslice)".
    iSplit.
    + iPureIntro. rewrite Z.sub_0_r. reflexivity.
    + iApply (isSlice_ownArray with "Harr Hblock Hslice [%]").
      assumption.
  Qed.

  Lemma imp_EArraySet2 `{Encode A, Inhabited A} {Φ : unit → iProp Σ} {ζ}
    (Φ3 : A → iProp Σ) (Φ1 : array → list loc → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 e3 :
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a, ∃ ls, ▷ isArray a ls ∗ Φ1 a ls }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3  }} -∗
    (∀ a ls i y, Φ1 a ls -∗ Φ2 i -∗ Φ3 y -∗
                 ∃ j xs,
                   ▷ (⌜j ≤ i < j + length xs⌝ ∗ a ↦∗[j] xs) ∗
                   ▷ (a ↦∗[j] (<[i - j := y]> xs) -∗ Φ ())) -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 He3 P". simpl_eval.
    iApply (imp_bind_par (A2:=(Z * A)) with "[He1] [He2 He3]").
    { set_postcondition (λ ls, ∃ a, ▷ isArray a ls ∗ Φ1 a ls)%I.
      iApply (imp_as_array with "He1").
      iIntros (l) "(% & #$ & $)". }
    { iApply (imp_par with "[He2] He3").
      iApply (imp_as_int with "He2"). }
    iIntros (ls (i & y)) "(%a & #Ha & HΦ1) (HΦ2 & HΦ3)".
    iDestruct ("P" with "HΦ1 HΦ2 HΦ3")
      as "(%j & %xs & >(%Hle & Hslice) & HΦ)".

    iDestruct "Hslice" as "(% & #Ha' & %Hlen & Hslice)".
    iNext.
    iPoseProof (isArray_valid with "Ha Ha'") as "->".
    iPoseProof (isArray_length with "Ha") as "%Hlen'".

    simpl.
    rewrite signed_repr; last representable.
    rewrite list_lookup_lookup_total_valid; last lia.
    (* Subogal: [store (a !!! i) #y] *)
    iPoseProof (big_sepLZ2_insert_seg_acc i with "Hslice")
      as "(Hl & Hslice)"; try lia.

    iApply (imp_store' with "Hl").
    iIntros "!> Hl".
    iApply "HΦ". iFrame "Ha'". length. iFrame "%".
    iSpecialize ("Hslice" with "Hl").
    update.
    iApply "Hslice".
  Qed.

  Lemma imp_EArraySet' `{Encode A, Inhabited A} {ζ}
    (Φ : A → iProp Σ) (i j : Z) (a : array) xs e1 e2 e3 :
    ⌜j ≤ i < j + length xs ⌝ -∗
    ▷ a ↦∗[j] xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a'=a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i'=i⌝ }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (_ : unit), ∃ y, Φ y ∗ a ↦∗[j] (<[i-j:=y]> xs) }}.
  Proof.
    iIntros (Hbound) "Hslice He1 He2 He3".
    iDestruct "Hslice" as "(%ls & #Harr & >%Hlenls & slice)".
    iApply (imp_EArraySet2 with "[He1] He2 He3").
    { set_postcondition (λ a', ∃ ls', _ ∗ ⌜a' = a⌝ ∗ ⌜ls' = ls⌝)%I.
      iApply (imp_wand with "He1").
      iIntros (?) "->". iFrame "Harr". auto. }
    iIntros (??? y) "(-> & ->) -> HΦ".
    iExists j, xs. iSplitL "slice".
    - iFrame. iFrame "%#".
    - iIntros "!> $".
      iFrame.
  Qed.

  Lemma imp_EArraySet `{Encode A, Inhabited A} {ζ}
    (Φ : A → iProp Σ) (i j : Z) (a : array) xs e1 e2 e3 :
    ⌜0 ≤ i < length xs⌝ -∗
    a ↦∗ xs -∗
    imp eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a'=a⌝ }} -∗
    imp eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ i', ⌜i'=i⌝ }} -∗
    imp eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ λ (_ : unit), ∃ y, Φ y ∗ a ↦∗ (<[i:=y]> xs) }}.
  Proof.
    iIntros (Hbound) "Hown He1 He2 He3".
    iDestruct "Hown" as "(%ls & #Harr & Hblock & Hslice & %Hlenls)".
    iApply (imp_wand with "[- Hblock]").
    { iApply (imp_EArraySet' with "[%] Hslice He1 He2 He3").
      lia. }
    iIntros ([]) "(%y & $ & Hslice)".
    rewrite Z.sub_0_r.
    iApply (isSlice_ownArray with "Harr Hblock Hslice [%]").
    by length.
  Qed.

End array_reasoning.
