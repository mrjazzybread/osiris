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

  Lemma imp_EPath_spec {E : coPset} {Ψ : iEff Σ} {A : Type} {EncA : Encode A}
  {Φ : A → iProp Σ} {ζ : exn → iProp Σ} (η : env) (p : path) :
    lookup_spec η p Φ -∗ imp eval η (EPath p) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ a, □ Φ a }}.
  Proof.
    iIntros "(% & %Hpath & #HΦ)".
    simpl_eval.
    iApply imp_widen. rewrite Hpath. iApply imp_ret; eauto.
  Qed.

  Lemma lookup_spec_step {A : Type} `{Encode A} {Φ : A → iProp Σ} {η x p} mspec :
    lookup_spec η [x] mspec -∗
    (∀ (δ : env), mspec δ -∗ lookup_spec δ p Φ) -∗
    lookup_spec η (x :: p) Φ.
  Proof.
    iIntros "(%δ & %Hlookup & #Hpost) Hcov".
    iDestruct ("Hcov" with "Hpost") as "(% & %Hlookup' & #HΦ)".
    iFrame "#". iPureIntro.
    simpl. destruct p.
    - simpl in Hlookup'. discriminate Hlookup'.
    - simpl in Hlookup.
      rewrite Hlookup !bind_ret.
      assumption.
  Qed.

  Lemma lookup_spec_search {A : Type} `{Encode A} {Φ : A → iProp Σ} {η v p} x y :
    (x =? y)%string = false →
    lookup_spec ((y, v) :: η) (x :: p) Φ =
    lookup_spec η (x :: p) Φ.
  Proof.
    intros Hneq.
    unfold lookup_spec. f_equal.
    extensionality v'. f_equal. f_equal.
    destruct p; simpl.
    - unfold lookup_name. rewrite Hneq. reflexivity.
    - unfold lookup_name. rewrite Hneq. reflexivity.
  Qed.

  Lemma imp_EPath_var {E Ψ ζ} {A : Type} `{Encode A} {η p} (a : A) :
    lookup_path η p = ret #a →
    ⊢ imp (eval η (EPath p)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }}.
  Proof.
    iIntros (Hlookup).
    iApply imp_EPath; eauto.
  Qed.

  Lemma lookup_spec_mono {A : Type} `{Encode A} {η p} (Φ Φ' : A → iProp Σ) :
    lookup_spec η p Φ' -∗
    □ (∀ a, Φ' a -∗ Φ a) -∗
    lookup_spec η p Φ.
  Proof.
    iIntros "(%a & %Hlookup & #HΦ') #Hcov".
    iExists a; iSplit; first (iPureIntro; assumption).
    iIntros "!>". iApply ("Hcov" with "HΦ'").
  Qed.

  Lemma imp_sum η :
    lookup_spec η ["Array"] (array_module_spec) -∗
    lookup_spec η ["+"] (λ add, iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) -∗
    imp (eval η esum) {{ λ sum, □ iSpec τ[Z] sum sum_spec }}.
  Proof.
    iIntros "#Hmodule_spec #Hadd".
    iApply imp_EAnon_pers.
    iIntros "!>" (n Hpos).
    iApply imp_please; iNext.
    iApply (imp_ELet_var (B:=array)).
    { iApply (imp_EApp_pers τ[Z;val]).
      { iApply imp_EPath_spec.
        rewrite lookup_spec_search; last reflexivity.
        iApply (lookup_spec_step with "[$]").
        iIntros (?) "#Harray_module".
        unfold array_module_spec at 2. unfold context. simpl.
        iDestruct "Harray_module" as "($ & _)". }
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
      rewrite lookup_spec_search; last reflexivity.
      rewrite lookup_spec_search; last reflexivity.
      iApply (lookup_spec_step with "[$]").
      iIntros (?) "#Harray_module".
      unfold array_module_spec at 2. unfold context. simpl.
      iDestruct "Harray_module" as "(_ & _ & _ & Hfold_left & _)".
      iApply (lookup_spec_mono with "Hfold_left").
      iIntros "!>" (init) "Hinit". iApply "Hinit". }
    { iApply imp_EPath_spec.
      rewrite lookup_spec_search; last reflexivity.
      rewrite lookup_spec_search; last reflexivity.
      iAssumption. }
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
    lookup_spec η ["Array"] (array_module_spec) -∗
    lookup_spec η ["+"] (λ add, iSpec τ[Z;Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})) -∗
    imp (eval_mexpr η __main) {{ context [ vSpec "sum" (λ sum, iSpec τ[Z] sum sum_spec) ] }}.
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
