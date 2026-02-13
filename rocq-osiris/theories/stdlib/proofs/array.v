From osiris.lang Require Import type_nel encode notations int.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import proofmode.

From osiris.stdlib Require Import og_array Externals.

From iris Require Import ltac_tactics.

From osiris.logic Require Import list_z.

Section proof.

  Context `{!osirisGS Σ}.

  Open Scope Z.

  Definition init_spec : Z → val → microvx → iProp Σ :=
    λ n f m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) (Φ : Z → A → iProp Σ) ,
         ⌜0 ≤ n ≤ max_array⌝ -∗
         (* [f] is a function [Z → A], such that [f i] satisfies [Φ i]. *)
         □ iSpec τ[Z] f (λ i m, ⌜0 ≤ i < n⌝ -∗ imp m {{ Φ i }}) -∗
         (* Calling [init f n] returns an array [a] such that [ownArray a xs],
            and such that [Φ i] holds for the [i]'th element of xs. *)
         imp m {{ λ a, ∃ (xs : list A), ⌜length xs = n⌝ ∗ ownArray a xs ∗
                                     [∗ list] i↦x ∈ xs, Φ i x }})%I.

  Definition init := (EAnonFun __fun21).

  Lemma imp_init η :
    lookup_name η "make" = ret Externals__array_make →
    lookup_name η "unsafe_set" = ret Externals__array_set →
    ⊢ imp (eval η init) {{ λ c, □ iSpec τ[Z; val] c init_spec }}.
  Proof.
    iIntros (Hlookup1 Hlookup2).
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros (n f).
    change (VInt (int.repr n)) with #n.
    unfold init_spec.
    iIntros (A HencA HinhA Φ) "%Hbounds #Hf".
    iApply imp_please; iNext.
    iApply imp_EIfThenElse.
    { iApply (imp_EOpEq_Z _ _ _ n 0). representable. representable.
      - iApply imp_EPath; auto.
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
      - iApply imp_EPath; auto.
      - iApply imp_EInt. }
    iIntros ([|]) "%Hlt0".

    { (* Case: [n < 0]. *)
      (* This case is forbidden by the spec. *) lia. }

    iApply (imp_ELet_var (B:=array)).
    { (* Subgoal: [make l (f 0)] *)
      iApply (imp_EApp_literal2 Z A). { simpl; eassumption. }
      - instantiate (1:=(λ n',⌜n'=n⌝)%I). iApply imp_EPath; auto.
      - iApply (imp_EApp τ[Z]).
        iApply imp_EPath; auto.
        iApply imp_EInt.
        iIntros (?) "-> %m H". iApply "H". iPureIntro; lia.
      - iIntros (?? ->) "HΦ !> !>".
        iApply (imp_EArrayMake (A:=A)). iPureIntro; eassumption.
        iApply imp_EPath; auto.
        iApply imp_EPath; first auto. iExact "HΦ". }
    iIntros (res) "(%x & HΦx & HownArr)".
    iDestruct "HownArr" as "(#Harr & Hslice)". length.

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
        - instantiate (1:=(λ i,⌜i=n⌝)%I). iApply imp_EPath; auto.
        - iApply imp_EInt.
        - iIntros "!> %% -> ->". auto. }
      { (* Prove that the loop invariant holds at index [1]. *)
        rewrite (split_replicate x n 1); last lia.
        iPoseProof (split_Slice 1 with "Hslice") as "[Hslice1 Hslice2]".
        reflexivity. done. iFrame. auto. }

      (* Prove that for any [i'] inside the loop,
         executing the loop's body produces the loop invariant at index [i' + 1],
         assuming that the loop invariant holds at index [i']. *)
      iIntros "!>" (i' Hbound) "(Hslice2 & %xs & %Hlenxs & Hslice1 & HΦs)".
      rewrite (split_replicate x (n - i') 1); last lia.
      replicate.
      iPoseProof (split_Slice with "Hslice2") as "[Hslice Hslice2]"; first reflexivity.
      length. reflexivity.
      iCombine ("Hslice1 Hslice") as "Hslice1".
      iPoseProof (split_Slice with "Hslice1") as "Hslice1". reflexivity. lia.
      (* Subgoal: [unsafe_set res i (f i)]. *)
      iApply (imp_EApp_literal3 array Z A). { simpl; eassumption. }
      { instantiate (1:=(λ a, ⌜a = res⌝)%I).
        iApply imp_EPath; auto. }
      { instantiate (1:=(λ i, ⌜i = i'⌝)%I).
        iApply imp_EPath; auto. }
      { iApply (imp_EApp τ[Z]).
        iApply imp_EPath; auto.
        instantiate (1:=(λ i, ⌜i = i'⌝)%I). iApply imp_EPath; auto.
        iIntros "% -> % H". iApply "H"; iPureIntro; lia. }
      { iIntros (? i y) "-> -> HΦ !> !>".
        iApply (imp_mono_ret with "[Hslice1 HΦ]").
        iApply (imp_EArraySet _ i' with "[] [] Harr Hslice1").
        { iPureIntro; lia. }
        { iPureIntro; length; lia. }
        { iApply imp_EPath; auto. }
        { iApply imp_EPath; auto. }
        { iApply imp_EPath; first auto. iExact "HΦ". }
        iIntros (_) "(% & HΦ & Hslice1)".
        replace (n - (i' + 1)) with (n - i' - 1) by lia.
        iFrame. length. iSplit; first (iPureIntro; lia).
        update. take.
        rewrite big_sepL_snoc. iFrame.
        rewrite /length in Hlenxs. rewrite Hlenxs.
        iApply "HΦ". } }

    iIntros "(Hslempty & %xs & %Hlen & Hslice & HΦs)".
    iApply imp_EPath; first auto.
    unfold ownArray. length. take.
    iFrame. rewrite Hlen.
    replace (n - 1 + 1) with n by lia.
    assert (n `max` 1 = n) as -> by lia.
    by iFrame "#".
  Qed.

End proof.

Section module_proof.
  Context `{!osirisGS Σ}.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Lemma module_proof η :
    ⊢ imp (eval_mexpr η __main)
      {{ λ η, ∃ init, ⌜lookup_name η "init" = ret init⌝ ∗
                     □ iSpec τ[Z; val] init init_spec }}.
  Proof.
    iApply imp_module.
    iApply imp_externals_length.
    iApply imp_externals_get.
    iApply imp_externals_set.
    iApply imp_externals_get.
    iApply imp_externals_set.
    iApply imp_externals_make.

    iApply (imp_sitems_module).
    { simpl_eval_mexpr.
      iApply imp_ret; first encode.
      instantiate (1 := (λ δ, ⌜δ = []⌝)%I). done. }
    iIntros (? ->).

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_init; auto. }
    iIntros (init) "#Hinit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (make_matrix) "Hmake_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (init_matrix) "Hinit_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (copy) "Hcopy".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (append) "Happend".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sub) "Hsub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fill) "Hfill".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (blit) "Hblit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter) "Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter2) "Hiter2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map) "Hmap".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map_inplace) "Hmap_inplace".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mapi_inplace) "Hmapi_inplace".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map2) "Hmap2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iteri) "Hiteri".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mapi) "Hmapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_list) "Hto_list".

    iApply (imp_sitems_letrec).
    { admit. }
    iIntros (list_length) "Hlist_length".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_list) "Hof_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (equal) "Hequal".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stdlib_compare) "Hstdlib_compare".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (compare) "Hcompare".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_left) "Hfold_left".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_left_map) "Hfold_left_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_right) "Hfold_right".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_right_map) "Hfold_right_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all) "Hfor_all".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all2) "Hfor_all2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (vexists2) "Hexists2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mem) "Hmem".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (memq) "Hmemq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_opt) "Hfind_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_index) "Hfind_index".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_map) "Hfind_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_mapi) "Hfind_mapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (split) "Hsplit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (combine) "Hcombine".

    iApply (imp_sitems_extend).
    iIntros (bottom) "Hbottom".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sort) "Hsort".

    iApply (imp_sitems_let (A:=Z)).
    { iApply imp_EInt. }
    iIntros (?) "->".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (unstable_sort) "Hunstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort_sub) "Hstable_sort_sub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort) "Hstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_EPath; first auto. admit. }
    iIntros (fast_sort) "Hfast_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle_contract_violation) "Hshuffle_contract_violation".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle) "Hshuffle".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seqi) "Hto_seqi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_rev_list) "Hof_rev_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iExists init. iSplit; [ auto | iFrame "#" ].

  Admitted.

End module_proof.
