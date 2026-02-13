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
      iApply (imp_EApp τ[Z;A]).
      - iApply imp_EPath. { simpl; eassumption. } iApply array_make_spec.
      - instantiate (1:=(λ n',⌜n'=n⌝)%I). iApply imp_EPath; auto.
      - iApply (imp_EApp τ[Z]).
        iApply imp_EPath; auto.
        iApply imp_EInt.
        iIntros (?) "-> %m H". iApply "H". iPureIntro; lia.
      - iIntros (?? ->) "HΦ %m Hm". iApply "Hm"; [ iPureIntro; assumption | iExact "HΦ" ]. }
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

      iIntros "!>" (i' Hbound) "(Hslice2 & %xs & %Hlenxs & Hslice1 & HΦs)".
      rewrite (split_replicate x (n - i') 1); last lia.
      replicate.
      iPoseProof (split_Slice with "Hslice2") as "[Hslice Hslice2]"; first reflexivity.
      length. reflexivity.
      iCombine ("Hslice1 Hslice") as "Hslice1".
      iPoseProof (split_Slice with "Hslice1") as "Hslice1". reflexivity. lia.
      iApply (imp_EApp τ[array;Z;A]).
      { iApply imp_EPath. { simpl; eassumption. } iApply array_set_spec. }
      { instantiate (1:=(λ a, ⌜a = res⌝)%I).
        iApply imp_EPath; auto. }
      { instantiate (1:=(λ i, ⌜i = i'⌝)%I).
        iApply imp_EPath; auto. }
      { iApply (imp_EApp τ[Z]).
        iApply imp_EPath; auto.
        instantiate (1:=(λ i, ⌜i = i'⌝)%I). iApply imp_EPath; auto.
        iIntros "% -> % H". iApply "H"; iPureIntro; lia. }
      { iIntros (y?) "-> %a -> HΦ %m Hm".
        iSpecialize ("Hm" with "Harr Hslice1 HΦ [] []").
        { iPureIntro; lia. }
        { iPureIntro; length; lia. }
        iApply (imp_mono_ret with "Hm").
        iIntros "!>" (_) "(% & HΦ & Hslice1)".
        update.
        replace (n - (i' + 1)) with (n - i' - 1) by lia.
        iFrame. length.
        iSplit; first (iPureIntro; lia).
        take.
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
