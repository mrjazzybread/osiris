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
    var_spec "Array" array_module_spec η -∗
    var_spec "+" (λ add, iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) η -∗
    imp (eval η esum) {{ λ sum, □ iSpec τ[Z] sum sum_spec }}.
  Proof.
    iIntros "#Hmodule_spec #Hadd".
    iApply imp_EAnon_pers.
    iIntros "!>" (n Hpos).
    iApply imp_please; iNext.
    iApply (imp_ELet_var (B:=array)).
    { iApply (imp_EApp_pers τ[Z;val]).
      { iApply imp_EPath_spec.
        iApply path_module_spec. { iApply var_spec_cons. auto. iAssumption. }
        iIntros (?) "#Hcontext".
        iApply path_var_spec.
        iPoseProof (extract_context [] with "Hcontext") as "(_ & $ & _)". }
      iApply imp_EPath_var; eauto.
      iApply (imp_EAnon_pers τ[Z] (λ i m, imp m {{ λ j, ⌜(j = i + 1)%Z⌝ }})%I).
      { iIntros (i) "!>". iApply imp_please; iNext.
        iApply imp_EIntAdd. iApply imp_EPath_var; eauto. iApply imp_EInt.
        iIntros "!>" (? j) "-> ->". auto. }
      iIntros (f ?) "-> #Hf %m Hm".
      iPoseProof (weaken_init_spec with "Hm") as "Hm".
      iSpecialize ("Hm" $! Z _ _ Hpos).
      iApply "Hm".
      iIntros "!> !>".
      iApply (iSpec_mono with "Hf"). iIntros (i m') "Hm Hbound".
      iApply "Hm". }
    iIntros (a) "(%xs & %Hlenxs & HownArr & #Hxs)".
    iApply (imp_EApp_pers τ[val;Z;array]).
    { iApply imp_EPath_spec.
      iApply path_module_spec. { repeat (iApply var_spec_cons; first auto). iAssumption. }
      iIntros (?) "#Hcontext". iApply path_var_spec.
      unfold array_module_spec at 2.
      iApply var_spec_mono.
      { iPoseProof (extract_context [_;_;_] with "Hcontext") as "(_ & $ & _)". }
      auto. }
    { iApply imp_EPath_spec.
      iApply path_var_spec. repeat (iApply var_spec_cons; first auto). iAssumption. }
    { iApply imp_EInt. }
    { iApply imp_EPath_var; auto. }
    iIntros (??) "-> %add #Hadd_ -> %m Hm".

    unfold fold_left_spec, tapp.
    iSpecialize ("Hm" $! Z _ _ _ xs (λ acc elems, let n := length elems in ⌜acc = n * (n + 1) / 2⌝)%I).
    iApply (imp_mono_ret with "[-]").
    iPoseProof (slice_of_own with "HownArr") as "(#Harr & Hslice)"; first reflexivity.
    - iApply ("Hm" with "Harr Hslice").
      { iIntros "!>".
        iApply (iSpec_mono with "Hadd_").
        iIntros (i j m') "Hm' %Hvisited %Hprefix %Hacc".
        iApply (imp_mono_ret with "Hm'").
        iIntros (? ->).
        destruct Hprefix as (ys & ->).
        iPoseProof (big_sepL_app with "Hxs") as "(Helems & Hys)".
        iPoseProof (big_sepL_app with "Helems") as "(Hvisited & %Hj)".
        specialize (Hj 0%nat j (list_lookup_singleton_eq_0 j)).
        iPureIntro. length. rewrite Hacc Hj. rewrite /length.
        generalize (Datatypes.length Hvisited).
        intros n0. replace (n0 + 0)%nat with n0 by lia.
        replace (n0 + 1 + 1) with (n0 + 2) by lia.
        replace ((n0 + 1) * (n0 + 2)) with ((n0 + 1) * n0 + (n0 +1) * 2) by lia.
        replace (((n0 + 1) * n0 + (n0 + 1) * 2) / 2) with (((n0 + 1) * n0) / 2 + (n0 + 1)).
        rewrite Z.mul_comm. reflexivity.
        by rewrite Z.div_add; last lia. }
      { iPureIntro. length. rewrite Z.mul_0_l Zdiv_0_l. reflexivity. }
    - iIntros "!>" (acc) "(%Hacc & Hslice)".
      iPureIntro. rewrite Hacc Hlenxs. reflexivity.
  Qed.

  Lemma module_proof η :
    var_spec "Array" array_module_spec η -∗
    var_spec "+" (λ add, iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) η -∗
    imp (eval_mexpr η __main) {{ context [ Spec "sum" (λ sum, iSpec τ[Z] sum sum_spec) ] {[ "sum" ]} }}.
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
