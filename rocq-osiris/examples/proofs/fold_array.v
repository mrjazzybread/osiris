From osiris Require Import osiris.
From iris.proofmode Require Import ltac_tactics.

From osiris.examples Require Import og_fold_array.
From osiris.stdlib.proofs Require Import array.

From Stdlib.Logic Require Import FunctionalExtensionality.

Section verification.

  Context `{!osirisGS Σ}.

  Open Scope Z.

  Definition sum_spec : Z → microvx → iProp Σ :=
    λ n m,
      (⌜0 ≤ n ≤ max_array⌝ -∗
       imp m {{ λ i, ⌜i = n * (n + 1) / 2⌝ }})%I.

  Definition esum := EAnonFun __fun2.

  Lemma imp_sum η :
    in_env "Array" array_module_spec η -∗
    in_env "+" (λ add, □ iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) η -∗
    imp (eval η esum) {{ λ sum, □ iSpec τ[Z] sum sum_spec }}.
  Proof.
    iIntros "#Hmodule_spec #Hadd".
    iApply imp_EAnon_pers.
    iIntros "!>" (n Hpos).
    iApply imp_please; iNext.
    (* let a = .. *)
    iApply (imp_ELet_var (B:=array)).
    { (* Array.init n (fun i -> i +) *)
      imp_app τ[Z;val].
      (* (fun i -> i + 1) *)
      { iApply (imp_EAnon_pers τ[Z] (λ i m, imp m {{ λ j, ⌜(j = i + 1)%Z⌝ }})%I).
        iIntros (i) "!>". iApply imp_please; iNext.
        iApply imp_EIntAdd. imp_path. iApply imp_EInt.
        iIntros "!>" (? j) "-> ->". auto. }
      iIntros (f ?) "-> #Hf %m Hm".
      iPoseProof (weaken_init_spec with "Hm") as "Hm".
      iApply ("Hm" $! Z _ _ _ Hpos).
      iIntros "!> !>".
      iApply (iSpec_mono with "Hf").
      iIntros (i m') "$ Hbound //". }
    iIntros (a) "(%xs & %Hlenxs & HownArr & #Hxs)".
    (* Array.fold_left (+) 0 a *)
    imp_app τ[val;Z;array].
    iIntros (??) "-> %add #Hadd_ -> %m Hm".

    iSpecialize ("Hm" $! Z _ _ _ xs (λ acc elems, let n := length elems in ⌜acc = n * (n + 1) / 2⌝)%I).
    iPoseProof (slice_of_own with "HownArr") as "(#Harr & Hslice)"; first reflexivity.
    iSpecialize ("Hm" with "Harr Hslice").
    iApply (imp_mono_ret with "[-]").

    - iApply "Hm".
      + iIntros "!>".
        iApply (iSpec_mono with "Hadd_").
        iIntros (i j m') "Hm' %visited %Hprefix %Hacc".
        iApply (imp_mono_ret with "Hm'").
        iIntros (? ->). length.
        destruct Hprefix as (ys & ->).
        iPoseProof (big_sepLZ_lookup_acc _ _ (length visited) j with "Hxs")
          as "(%Hvisited & _)"; first by lookup.
        iPureIntro.
        (* Painful arithmetic rewriting. *)
        remember (length visited) as v.
        replace (v + 1 + 1) with (v + 2) by lia.
        rewrite -Hvisited in Hacc |-*; rewrite Hacc.
        replace (j * (v + 2)) with (j * v + j * 2) by lia.
        rewrite Z.div_add; last lia. rewrite Z.mul_comm. reflexivity.
      + iPureIntro. length. rewrite Z.mul_0_l Zdiv_0_l. reflexivity.
    - iIntros "!>" (acc) "(%Hacc & Hslice)".
      iPureIntro. rewrite Hacc Hlenxs. reflexivity.
  Qed.

  Lemma module_proof η :
    in_env "Array" array_module_spec η -∗
    in_env "+" (λ add, □ iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) η -∗
    imp (eval_mexpr η __main) {{ context [ var_spec "sum" (λ sum, iSpec τ[Z] sum sum_spec) ] {[ "sum" ]} }}.
  Proof.
    iIntros "#Hlookup #Hlookup'".
    iApply imp_module.

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_sum; auto. }
    iIntros (sum) "#Hsum".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Qed.

End verification.
