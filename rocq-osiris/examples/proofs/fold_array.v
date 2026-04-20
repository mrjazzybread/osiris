From osiris Require Import osiris.
From iris.proofmode Require Import ltac_tactics.

From osiris.examples Require Import og_fold_array.
From osiris.stdlib.proofs Require Import array.

From Stdlib.Logic Require Import FunctionalExtensionality.

Section verification.

  Context `{!osirisGS Σ}.

  Open Scope Z.

  (* Some helpful lemmas about sums. *)

  Definition gauss_summation n := n * (n + 1) / 2.

  Lemma gauss_summation_0 :
    gauss_summation 0 = 0.
  Proof.
    unfold gauss_summation.
    rewrite Z.mul_0_l Zdiv_0_l.
    reflexivity.
  Qed.

  Lemma gauss_summation_incr n :
    gauss_summation (n + 1) = gauss_summation n + (n + 1).
  Proof.
    unfold gauss_summation.
    replace (n + 1 + 1) with (n + 2) by lia.
    replace ((n + 1) * (n + 2)) with ((n + 1) * n + (n + 1) * 2) by lia.
    rewrite Z.div_add; last lia. rewrite Z.mul_comm. reflexivity.
  Qed.

  Lemma gauss_summation_as_fold n :
    0 ≤ n →
    List.fold_left Z.add (list_z.init n (λ i, i + 1)) 0 = gauss_summation n.
  Proof.
    intros Hpos.
    pattern n. apply natlike_ind; last lia.
    - apply gauss_summation_0.
    - intros n' Hpos' IH. unfold Z.succ.
      rewrite (split_init (n' + 1) n'); try lia.
      rewrite Z.add_simpl_l init_singleton.
      rewrite fold_left_app IH.
      rewrite singleton_unfold /=.
      rewrite gauss_summation_incr. lia.
  Qed.

  (* The specification of our function:
     the precondition is [0 ≤ n ≤ max_array_length]
     the postcondition is [λ i, ⌜i = gaus_summation n⌝]. *)

  Definition sum_spec : Z → microvx → iProp Σ :=
    λ n m,
      (⌜0 ≤ n ≤ max_array_length⌝ -∗
       imp m {{ λ i, ⌜i = gauss_summation n⌝ }})%I.

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
    { (* [Array.init n (fun i -> i +)] *)
      imp_app τ[Z;val].
      { (* (fun i -> i + 1) *)
        iApply (imp_EAnon_pers τ[Z] (λ i m, imp m {{ λ j, ⌜(j = i + 1)%Z⌝ }})%I).
        iIntros (i) "!>". iApply imp_please; iNext. imp_arith. }
      iIntros "#Hf Hm".
      (* We weaken the spec of [Array.init] to one where the function is known to be pure. *)
      iPoseProof (init_spec_pure_spec with "Hm") as "Hm".
      iApply ("Hm" $! Z with "[//]").
      iIntros "!>".
      iApply (iSpec_mono with "Hf").
      iIntros (i m') "$ Hbound //". }

    (* [Array.fold_left (+) 0 a] *)
    iIntros (a) "HownArr".
    imp_app τ[val;Z;array].
    iIntros "#Hadd_ Hm".
    (* Weaken the spec of [Array.fold_left] to one where the function is known to be pure. *)
    iPoseProof (fold_left_spec_pure_spec with "Hm") as "Hm".

    unfold fold_left_pure_spec.
    iSpecialize ("Hm" $! Z with "HownArr Hadd_").
    iApply (imp_wand with "Hm").
    iIntros (acc) "(-> & _)".
    iPureIntro.

    (* Subgoal: [fold_left Z.add (init n (λ i, i + 1)) 0 = gauss_summation n]. *)
    apply gauss_summation_as_fold. lia.
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
