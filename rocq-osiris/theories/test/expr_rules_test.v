From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import osiris lang.
From osiris.program_logic Require Import ewp.
From osiris.proofmode Require Import proofmode.

Section test_expr_rules.
Context `{!osirisGS Σ}.

(* Useful when goal is [R ⊢ WP (ret v) {{ ?evar }}] *)
(* iApply-ing it will fail without providing much information if [R] or [v]
   depends on a variable [y] that was created after the creation of the evar, in
   which case, instantiate the evar with something like [λx, ∃y, ⌜x = y⌝ ∗ R] *)
Lemma ewp_ret_eq {A E} ι Ψ (v : A) R : R ⊢ EWP[ι] (@Ret A E v) <|Ψ|> {{ ensures x, ⌜x = v⌝%I ∗ R }}.
Proof.
  iIntros "H".
  iApply ewp_ret.
  iFrame.
  auto.
Qed.

(* Simpler case with no useful resource *)
Lemma ewp_ret_eq_emp {A E} ι Ψ (v : A) : ⊢ EWP[ι] (@Ret A E v) <|Ψ|> {{ ensures x, ⌜x = v⌝ }}.
Proof.
  iApply ewp_ret.
  auto.
Qed.

Lemma ewp_ret_eq_enc `{Encode A} {E} ι Ψ (v : A) : ⊢ EWP[ι] (@Ret val E #v) <|Ψ|> {{ ensures #x, ⌜x = v⌝ }}.
Proof.
  iApply ewp_ret.
  iExists _; auto.
Qed.


(* Useful when goal is [R ⊢ ?evar v] *)
Lemma goal_eq {A} (v : A) (R : iProp Σ) φ :
  φ = (λ x, ⌜x = v⌝ ∗ R)%I ->
  R ⊢ φ v.
Proof.
  iIntros (->) "R".
  auto.
Qed.

(* Useful when goal is [⊢ ?evar v] *)
Lemma goal_eq_emp {A} (v : A) (φ : _ -> iProp Σ) :
  φ = (λ x, ⌜x = v⌝)%I ->
  ⊢ φ v.
Proof.
  iIntros (->).
  auto.
Qed.

(* [ref 1] *)

Lemma example_ref_1 ι η:
  ⊢ EWP[ι] (eval η (ERef (EInt 1))) {{ ensures #l, l ↦ V #1 }}.
Proof.
  iApply ewp_ERef.
  - (* 1 *)
    instantiate (1 := λ i, (⌜i = 1%Z⌝)%I).
    iApply ewp_EInt. iExists 1; equality.
  - (* ref *)
    iIntros (i l) "-> Hl".
    iFrame.
Qed.

(* [!x] *)
Lemma example_load ι η x l v :
  lookup_name η x = ret (VLoc l) ->
  l ↦ V v ⊢ EWP[ι] (eval η (ELoad (EVar x))) {{ ensures v, l ↦ V v }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_ELoad.
  - simpl_eval. rewrite Hx.
    instantiate (1 := (λ l', ⌜l' = l ⌝)%I). iApply ewp_ret.
    iExists _; auto.
  - iIntros (?) "->".
    iExists _, _. iFrame. auto.
Qed.

(* [x := 2] *)
Lemma example_store ι η x l :
  lookup_name η x = ret #l ->
  l ↦ V #1
    ⊢ EWP[ι] (eval η (EStore (EVar x) (EInt 2)))
    {{ ensures r, ⌜r = VUnit⌝ ∗ l ↦ V #2 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_EStore.
  - simpl_eval. rewrite Hx. iApply ewp_ret_eq_enc.
  - iApply ewp_EInt. instantiate (1 := (λ i, ⌜i=2%Z⌝)%I).
    iExists _. iFrame; eauto.
  - iIntros (? ?) "(-> & ->)".
    iExists _. iFrame. iNext.
    iIntros "Hl /=".
    auto.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores ι η x l :
  lookup_name η x = ret #l ->
  l ↦ V #1
    ⊢ EWP[ι] (eval η
            (ESeq
               (EStore (EVar x) (EInt 2))
               (EStore (EVar x) (EInt 4))))
    {{ ensures r, ⌜r = VUnit⌝ ∗ l ↦ V #4 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_ESeq.
  iApply ewp_EStore.
  - simpl_eval. rewrite Hx. iApply ewp_ret_eq_enc.
  - iApply ewp_EInt. instantiate (1 := (λ i, ⌜i=2%Z⌝)%I).
    iExists 2; auto.
  - iIntros (? ?) "(-> & ->)".
    iExists _. iFrame. iNext. iIntros "Hl /=".
    iApply ewp_EStore.
    + simpl_eval. rewrite Hx. iApply ewp_ret_eq_enc.
    + iApply ewp_EInt. instantiate (1 := (λ i, ⌜i=4%Z⌝)%I).
      iExists 4; auto.
    + iIntros (? ?) "(-> & ->)".
      iExists _. iFrame. iNext. iIntros "$ //".
Qed.

(* [!(ref 1)]  *)
Lemma example_load_ref ι η :
  ⊢ EWP[ι] (eval η (ELoad (ERef (EInt 1)))) {{ ensures #r, ⌜r = 1⌝ }}.
Proof.
  iApply (ewp_ELoad _ _ (λ l, l ↦ V #1)%I).
  - (* ref 1 *)
    iApply ewp_ERef.
    + iApply ewp_EInt. instantiate (1 := (λ i, ⌜i = 1%Z⌝)%I).
      iExists 1; eauto.
    + iIntros (i l) "-> $".
  - (* load *)
    iIntros (l) "Hl".
    iExists _, _.
    iFrame.
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr ι η x lx n :
  lookup_name η x = ret #lx ->
  lx ↦ V #n
  ⊢ EWP[ι] (eval η (EStore (EVar x) (EIntAdd (EInt 1) (ELoad (EVar x)))))
    {{ ensures r, ⌜r = VUnit⌝ ∗ lx ↦ V #(1 + n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (ewp_EStore with "[] [Hx]").

  - (* l-value x *)
    simpl_eval. rewrite Ex. iApply ewp_ret_eq_enc.

  - (* 1 + !x *)
    instantiate (1 := (λ i, ⌜i = (1 + n)%Z⌝ ∗ lx ↦ V #n)%I).
    iApply (ewp_EIntAdd with "[] [Hx]").
    + (* 1 *)
      iApply ewp_EInt. instantiate (1 := (λ i, ⌜i=1%Z⌝)%I).
      by iExists 1.
    + (* !x *)
      iApply ewp_ELoad.
      * simpl_eval. rewrite Ex. instantiate (1 := (λ l, ⌜l=lx⌝)%I).
        iApply ewp_ret. by iExists lx.
      * iIntros (l) "->".
        iExists _, _; iFrame.
        iNext.
        iIntros "Hx". iExists n; iSplit; first done.
        instantiate (1 := (λ n', ⌜n' = n⌝ ∗ lx ↦ V #n)%I).
        iFrame; auto.
    + (* add's postcondition *)
      iIntros (n1 n2) "(-> & -> & $)".
      auto.

  - (* store's postcondition *)
    iIntros (l1 n2) "(-> & -> & Hlx)".
    iExists _. iFrame. iNext.
    iIntros "$". auto.
Qed.

(* [x := !x + (y := 1 + !y; !y)] *)
Lemma example_incr_via_y ι η x lx y ly n :
  lookup_name η x = ret #lx ->
  lookup_name η y = ret #ly ->
  lx ↦ V #n ∗ ly ↦ V #0
  ⊢ EWP[ι] (eval η (EStore (EVar x) (ELoad (EVar x) +
         ESeq (EStore (EVar y) (EIntAdd (EInt 1) (ELoad (EVar y)))) (ELoad (EVar y))
       )))
    {{ ensures r, ⌜r = VUnit⌝ ∗ lx ↦ V #(n + 1)%Z ∗ ly ↦ V #1 }}.
Proof.
  iIntros (Ex Ey) "(Hx & Hy)".
  iApply (ewp_EStore with "[] [Hx Hy]").

  - (* l-value x *)
    simpl_eval. rewrite Ex. iApply ewp_ret_eq_enc.

  - (* !x + (...) *)
    iApply (ewp_EIntAdd with "[Hx] [Hy]").
    + (* !x *)
      iApply ewp_ELoad.
      * simpl_eval. rewrite Ex. instantiate (1 := (λ l', ⌜l'=lx⌝)%I).
        iApply ewp_ret. iExists _; auto.
      * iIntros (l) "->".
        iExists _, _. iFrame. iNext.
        iIntros "Hx".
        iExists _; iSplit; first auto.
        instantiate (1 := (λ n', ⌜n' = n⌝ ∗ lx ↦ V #n)%I).
        iFrame; auto.

    + (* (y := 1 + !y; !y) *)
      iApply ewp_ESeq.
      (* y := 1 + !y: use previous example *)
      iApply (ewp_mono with "[Hy]").
      by iApply (example_incr with "Hy").
      (* !y *)
      iIntros_RET (v) "H".
      iApply ewp_ELoad.
      * simpl_eval. rewrite Ey.
        instantiate (1 := (λ l, ⌜l = ly⌝)%I).
        iApply ewp_ret. iExists _; auto.
      * iDestruct "H" as "(-> & H)".
        iIntros (l) "->".
        iExists _, _. iFrame. iNext.
        iIntros "Hy". simpl.
        iExists 1; iSplit; first auto.
        instantiate (1 := (λ n', ⌜n' = 1%Z⌝ ∗ ly ↦ _)%I).
        iFrame; auto.

    + (* add's postcondition *)
      iIntros (n1 n2) "((-> & Hx) & (-> & Hy))".
      iFrame.
      iCombine "Hx" "Hy" as "H".
      iApply (goal_eq with "H"). reflexivity.

  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & -> & (Hx & Hy))".
    iExists _. iFrame.
    iNext. iIntros "Hx".
    iFrame; auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double ι η x lx n :
  lookup_name η x = ret #lx ->
  lx ↦ V #n
  ⊢ EWP[ι] (eval η (EStore (EVar x) (ELoad (EVar x) + ELoad (EVar x))))
    {{ ensures r, ⌜r = VUnit⌝ ∗ lx ↦ V #(2 * n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (ewp_EStore with "[] [Hx]").
  { simpl_eval. rewrite Ex. iApply ewp_ret_eq_enc. }
  - (* !x + !x *)
    iDestruct "Hx" as "(Hx1 & Hx2)".
    iApply (ewp_EIntAdd with "[Hx1] [Hx2]").
    + (* !x *)
      iApply (ewp_ELoad).
      { simpl_eval. rewrite Ex. instantiate (1 := (λ l, ⌜l=lx⌝)%I).
        iApply ewp_ret. iExists _; auto. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iExists _; iSplit; first auto.
      instantiate (1 := (λ i, ⌜i = n⌝ ∗ pointsto lx _ _)%I).
      iFrame; auto.
    + (* !x *)
      iApply (ewp_ELoad).
      { simpl_eval. rewrite Ex. instantiate (1 := (λ l, ⌜l=lx⌝)%I).
        iApply ewp_ret. iExists _; auto. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iExists _; iSplit; first auto.
      instantiate (1 := (λ i, ⌜i = n⌝ ∗ pointsto lx _ _)%I).
      iFrame; auto.
    + (* + *)
      iIntros (_n1 _n2) "((-> & Hx1) & (-> & Hx2))".
      iCombine "Hx1" "Hx2" as "Hx".
      iApply (goal_eq with "Hx"). reflexivity.
  - (* := *)
    iIntros (_l1 _v2) "(-> & -> & Hx)".
    iExists _. iFrame. iNext. iIntros "Hx".
    replace (n + n)%Z with (2 * n)%Z by lia.
    by iFrame.
Qed.

(* match 1 with _ -> true *)

Lemma simple_PAny_match ι η :
  ⊢ EWP[ι] eval η
    (EMatch (EInt 1)
      [Branch (CVal PAny) (EConstant "true")])
    {{ ensures #r, ⌜r = true⌝ }}.
Proof.
  prove_match with (@lift_ret_spec Σ _ exn (λ v, ⌜v = #1⌝))%I.
  { iApply ewp_EInt. encode. }

  iIntros_RET "-> !>".
  iApply deep_handle_cons. { iPureIntro; ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  iApply ewp_EConstant. iExists true. auto.
Qed.
(*
a few examples for EMatch, for now more than necessary
we should remove most of them once EMatch rules are well understood.
*)

(* match 1 with 1 -> true | _ -> false *)

Lemma simple_PInt_eq_match ι η :
  ⊢ EWP[ι] eval η
    (EMatch (EInt 1)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ ensures #r, ⌜r = true⌝ }}.
Proof.
  prove_match with (@lift_ret_spec Σ _ exn (λ v, ⌜v = #(1)%Z⌝))%I.
  { iApply ewp_EInt. encode. }
  iIntros_RET "-> !>".
  iApply deep_handle_cons. { iPureIntro; ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  - iApply ewp_EConstant; iExists true; auto.
  - congruence.
Qed.

(* match 2 with 1 -> true | _ -> false *)

Lemma simple_PInt_neq_match ι η :
  ⊢ EWP[ι] eval η
    (EMatch (EInt 2)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ ensures #r, ⌜r = false⌝ }}.
Proof.
  prove_match with (@lift_ret_spec Σ _ exn (λ v, ⌜v = #2%Z⌝))%I.
  { iApply ewp_EInt; encode. }
  iIntros_RET "-> !>".
  next_branch. iIntros (? []).
  iApply deep_handle_cons. { iPureIntro; ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  iApply ewp_EConstant; iExists false; auto.
Qed.

(* match 2 with 0 -> 0 | 1 -> 1 | 2 -> 2 *)

Lemma simple_PInt_012_match ι η :
  ⊢ EWP[ι] eval η
    (EMatch (EInt 2)
      [Branch (CVal (PInt 0)) (EInt 0);
       Branch (CVal (PInt 1)) (EInt 1);
       Branch (CVal (PInt 2)) (EInt 2)])
    {{ ensures #r, ⌜r = 2⌝ }}.
Proof.
  prove_match with (@lift_ret_spec Σ _ exn (λ v, ⌜v = #2%Z⌝))%I.
  { iApply ewp_EInt; encode. }
  iIntros_RET "-> !>".
  next_branch. iIntros (? []).
  next_branch. iIntros (? []).
  iApply deep_handle_cons. { iPureIntro; ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  { iApply ewp_EInt. iExists 2. auto. }
  congruence.
Qed.

(* checking now whether pat_pNil works with
match [] with _ :: _ -> 1 | _ -> 2 *)



Lemma simple_true_true_match `{Encode A} ι η :
  ⊢ EWP[ι] eval η
    (EMatch (EData "[]" [])
      [Branch (CVal (PData "::" [ PAny; PAny ])) (EInt 1);
       Branch (CVal (PConstant "[]")) (EInt 2)])
    {{ ensures #r, ⌜r = 2⌝ }}.
Proof.
  prove_match with (@lift_ret_spec Σ val exn (λ v, ⌜v = #(@nil A)⌝))%I.
  { iApply ewp_EConstant. encode. }

  iIntros_RET "->". change (VNil) with (#(@nil A)).
  next_branch. iIntros (? []).
  revert H0.
  instantiate (1 := (fun _ => False)); instantiate (1 := (fun _ => False)).
  iIntros "%no_match1".
  iApply deep_handle_cons. { iPureIntro; ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  { iApply ewp_EInt. by iExists 2. }
  congruence.
Qed.

End test_expr_rules.
