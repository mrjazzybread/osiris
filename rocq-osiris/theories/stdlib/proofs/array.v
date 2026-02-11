From osiris.lang Require Import type_nel encode notations int.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import proofmode.

From osiris.stdlib Require Import translated_array.

From iris Require Import ltac_tactics.

From osiris.logic Require Import list_z.

Section proof.

  Context `{!osirisGS Σ}.

  Open Scope Z.

  Definition init_spec : Z → val → microvx → iProp Σ :=
    λ n f m,
      (∀ `(_ : Encode A) `(_ : Inhabited A) (Φ : Z → A → iProp Σ) ,
         ⌜0 ≤ n ≤ max_array⌝ -∗
         □ iSpec τ[Z] f (λ i m, imp m {{ Φ i }}) -∗
         imp m {{ λ a, ∃ (xs : list A), ⌜length xs = n⌝ ∗ ownArray a xs ∗
                                     [∗ list] i↦x ∈ xs, Φ i x }})%I.

  Definition init := (EAnonFun __fun8).

  Lemma imp_init η :
    ⊢ imp (eval η init) {{ λ c, □ iSpec τ[Z; val] c init_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros (n f).
    change (VInt (int.repr n)) with #n.
    unfold init_spec.
    iIntros (A HencA HinhA Φ) "%Hbounds #Hf".
    iApply imp_please; iNext.
    iApply imp_EIfThenElse.
    { iApply (imp_EOpEq_Z _ _ _ n 0). representable. representable.
      - iApply imp_EPath. iApply imp_ret; auto.
      - iApply imp_EInt. }
    iIntros ([|]) "%Heq0".

    { (* Case: [n = 0]. *)
      iApply imp_mono_ret.
      iApply (imp_EArrayLit (A:=A) []).
      - iPureIntro; split; [ reflexivity | ].
        rewrite length_nil. lia.
      - simpl_evals. iApply (imp_ret [] []). reflexivity.
        done.
      - iIntros (a) "(%xs & Harray & Hemp)".
        iPoseProof (big_sepL2_length with "Hemp") as "%Hlen".
        apply list.nil_length_inv in Hlen as ->.
        iFrame. rewrite length_nil. iSplit; [ iPureIntro; lia | auto ]. }

    iApply imp_EIfThenElse.
    { iApply (imp_EOpLt_Z _ _ _ n 0). representable. representable.
      - iApply imp_EPath. iApply imp_ret; auto.
      - iApply imp_EInt. }
    iIntros ([|]) "%Hlt0".

    { (* Case: [n < 0]. *)
      (* This case is forbidden by the spec. *) lia. }

    iApply (imp_ELet_var (B:=array)).
    { (* Subgoal: [make l (f 0)] *)
      iApply (imp_EArrayMake (A:=A) n). iPureIntro; assumption.
      iApply imp_EPath. iApply imp_ret; eauto.
      { iApply (imp_EApp τ[Z]).
        iApply imp_EPath. iApply imp_ret; auto.
        iApply imp_EInt.
        iIntros (?) "-> %m $". } }
    iIntros (res) "(%x & HΦx & #Harr & Hslice)".

    (* Subgoal: [for i = 1 to ... done; res]. *)
    iApply (imp_ESeq with "[Hslice HΦx]").

    { (* Subgoal: [for i = 1 to ... done]. *)
      iApply (imp_EFor
                (λ i,
                   isSlice (DfracOwn 1) res i (replicate (n - i) x) ∗
                   ∃ xs, ⌜length xs = i⌝ ∗ isSlice (DfracOwn 1) res 0 xs ∗
                            [∗ list] j↦x ∈ take i xs, Φ j x)%I
                1 (n-1) with "[] [] [Hslice HΦx]").
      representable. representable.
      { iApply imp_EInt. }
      { iApply (imp_EIntSub).
        - instantiate (1:=(λ i,⌜i=n⌝)%I). iApply imp_EPath. iApply imp_ret; auto.
        - iApply imp_EInt.
        - iIntros "!> %% -> ->". auto. }
      { rewrite unroll_replicate; last lia.
        rewrite cons_is_append.
        iPoseProof (split_Slice 1 with "Hslice") as "[Hslice1 Hslice2]".
        reflexivity. done. iFrame. auto. }

      iIntros "!>" (i' Hbound) "(Hslice1 & %xs & %Hlenxs & Hslice2 & HΦs)".
      iApply (imp_EArraySet2 (A:=A)).
      { iApply imp_EPath.
        instantiate (1:=(λ a', ⌜a'=res⌝)%I).
        iApply imp_ret; auto. }
      { iApply imp_EPath.
        instantiate (1:=(λ i, ⌜i = i'⌝)%I).
        iApply imp_ret; auto. }
      { iApply (imp_EApp τ[Z]).
        iApply imp_EPath. iApply imp_ret; auto.
        iApply imp_EPath.
        instantiate (1:=(λ i, ⌜i = i'⌝)%I).
        iApply imp_ret; auto.
        iIntros "% -> % $". }

      iIntros (?? y) "-> -> HΦ".
      iFrame "#".
      iCombine "Hslice2 Hslice1" as "Hslice".
      iPoseProof (split_Slice with "Hslice") as "Hslice".
      reflexivity. lia.

      iFrame.
      iSplit; iNext.
      - iPureIntro. rewrite length_app length_replicate.
        lia.
      - iIntros "Hslice".
        iPoseProof (split_Slice (i'+1) _ _ _ _ (xs ++ [y]) with "Hslice")
          as "[Hslice0 Hslicei]".
        { rewrite unroll_replicate; last lia.
          rewrite cons_is_append. rewrite app_assoc.
          rewrite insert_app_l; last (rewrite length_app length_singleton; lia).
          rewrite insert_app_r; last lia.
          rewrite insert_singleton. case_decide; last lia.
          reflexivity. }
        { rewrite length_app length_singleton. lia. }
        replace (n - (i' + 1)) with (n - i' -1) by lia.
        iFrame.
        iSplit; first (iPureIntro; rewrite length_app length_singleton; lia).
        take.
        rewrite big_sepL_snoc. iFrame.
        rewrite /length in Hlenxs. rewrite Hlenxs.
        iApply "HΦ". }

    iIntros "(Hslempty & %xs & %Hlen & Hslice & HΦs)".
    iApply imp_EPath. iApply imp_ret; first encode.
    take.
    iFrame. rewrite length_replicate. rewrite Hlen.
    replace (n - 1 + 1) with n by lia.
    assert (n `max` 0 = n) as -> by lia.
    assert (n `max` 1 = n) as -> by lia.
    by iFrame "#".
  Qed.

End proof.
