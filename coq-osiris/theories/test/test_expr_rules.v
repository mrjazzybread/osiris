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
Lemma ewp_ret_eq {A E} Ψ (v : A) R : R ⊢ EWP (@Ret A E v) <|Ψ|> {{ (λ x, ⌜x = v⌝%I ∗ R)↑ }}.
Proof.
  iIntros "H".
  Ret.
  iFrame.
  auto.
Qed.

(* Simpler case with no useful resource *)
Lemma ewp_ret_eq_emp {A E} Ψ (v : A) : ⊢ EWP (@Ret A E v) <|Ψ|> {{ (λ x, ⌜x = v⌝%I)↑ }}.
Proof.
  Ret.
  auto.
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

Lemma example_ref_1 env:
  ⊢ EWP (eval env (ERef (EInt 1))) {{ RET v, ∃ l : loc, ⌜v = VLoc l⌝ ∗ l ↦ V #1 }}.
Proof.
  iApply ewp_ERef.
  - (* 1 *)
    iApply ewp_ret_eq_emp.
  - (* ref *)
    iIntros (v) "->".
    iIntros (l) "(? & ?)". iExists _. iFrame. auto.
Qed.

(* [!x] *)
Lemma example_load env x l v :
  lookup_name env x = ret (VLoc l) ->
  l ↦ V v ⊢ EWP (eval env (ELoad (EVar x))) {{ RET v, l ↦ V v }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_ELoad.
  - Simp.
    iApply ewp_ret_eq_emp.
  - iIntros (?) "->".
    iExists _, _. iFrame. auto.
Qed.

(* [x := 2] *)
Lemma example_store env x l :
  lookup_name env x = ret (VLoc l) ->
  l ↦ V #1
    ⊢ EWP (eval env (EStore (EVar x) (EInt 2)))
    {{ RET r, ⌜r = VUnit⌝ ∗ l ↦ V #2 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_EStore.
  - Simp. iApply ewp_ret_eq_emp.
  - iApply ewp_ret_eq_emp.
  - iIntros (? ?) "(-> & ->)".
    iExists _. iFrame. iNext.
    iIntros "Hl /=".
    auto.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores env x l :
  lookup_name env x = ret (VLoc l) ->
  l ↦ V #1
    ⊢ EWP (eval env
            (ESeq
               (EStore (EVar x) (EInt 2))
               (EStore (EVar x) (EInt 4))))
    {{ RET r, ⌜r = VUnit⌝ ∗ l ↦ V #4 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_ESeq.
  iApply ewp_EStore.
  - Simp. iApply ewp_ret_eq_emp.
  - iApply ewp_ret_eq_emp.
  - iIntros (? ?) "(-> & ->)".
    iExists _. iFrame. iNext. iIntros "Hl /=".
    iApply ewp_EStore.
    + Simp. iApply ewp_ret_eq_emp.
    + iApply ewp_ret_eq_emp.
    + iIntros (? ?) "(-> & ->)".
      iExists _. iFrame. iNext. iIntros "$ //".
Qed.

(* [!(ref 1)]  *)
Lemma example_load_ref env :
  ⊢ EWP (eval env (ELoad (ERef (EInt 1)))) {{ RET r, ⌜r = #1⌝ }}.
Proof.
  iApply (ewp_ELoad _ _ (λ l, l ↦ V #1)).
  - (* ref 1 *)
    Bind.
    iApply ewp_ERef.
    + iApply ewp_ret_eq_emp.
    + iIntros (?) "->".
      iIntros (l) "Hl /=".
      by Ret.
  - (* load *)
    iIntros (l) "Hl".
    iExists _, _.
    iFrame.
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr env x lx n :
  lookup_name env x = ret (VLoc lx) ->
  lx ↦ V #n
  ⊢ EWP (eval env (EStore (EVar x) (EIntAdd (EInt 1) (ELoad (EVar x)))))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V #(1 + n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (ewp_EStore with "[] [Hx]").

  - (* l-value x *)
    Simp. iApply ewp_ret_eq_emp.

  - (* 1 + !x *)
    iApply (ewp_EIntAdd with "[] [Hx]").
    + (* as_int 1 *)
      Simp. iApply ewp_ret_eq_emp.
    + (* as_int !x *)
      Bind.
      iApply ewp_ELoad.
      * Simp. iApply ewp_ret_eq_emp.
      * iIntros (l) "->".
        iExists _, _; iFrame.
        iNext.
        iIntros "Hx".
        iApply (ewp_ret_eq with "Hx").

    + (* add's postcondition *)
      iIntros (n1 n2) "(-> & (-> & Hx))".
      iApply (goal_eq with "Hx"). reflexivity.

  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & -> & A) /=".
    iExists _. iFrame. iNext.
    rewrite M.add_repr_repr.
    auto.
Qed.

(* [x := !x + (y := 1 + !y; !y)] *)
Lemma example_incr_via_y env x lx y ly n :
  lookup_name env x = ret (VLoc lx) ->
  lookup_name env y = ret (VLoc ly) ->
  lx ↦ V #n ∗ ly ↦ V #0
  ⊢ EWP (eval env (EStore (EVar x) (ELoad (EVar x) +
         ESeq (EStore (EVar y) (EIntAdd (EInt 1) (ELoad (EVar y)))) (ELoad (EVar y))
       )))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V #(n + 1)%Z ∗ ly ↦ V #1 }}.
Proof.
  iIntros (Ex Ey) "(Hx & Hy)".
  iApply (ewp_EStore with "[] [Hx Hy]").

  - (* l-value x *)
    Simp. iApply ewp_ret_eq_emp.

  - (* !x + (...) *)
    iApply (ewp_EIntAdd with "[Hx] [Hy]").
    + (* as_int !x *)
      Bind.
      iApply ewp_ELoad.
      * Simp. iApply ewp_ret_eq_emp.
      * iIntros (l) "->".
        iExists _, _. iFrame. iNext.
        iIntros "Hx".
        iApply (ewp_ret_eq with "Hx").

    + (* as_int (y := 1 + !y; !y) *)
      Bind.
      iApply ewp_ESeq.
      (* y := 1 + !y: use previous example *)
      iApply (ewp_mono with "[Hy]").
      by iApply (example_incr with "Hy").
      (* !y *)
      iIntros ([v_|]) "H". 2: done.
      iApply ewp_ELoad.
      * Simp. iApply ewp_ret_eq_emp.
      * iDestruct "H" as "(-> & H)".
        iIntros (l) "->".
        iExists _, _. iFrame. iNext.
        iIntros "Hy". simpl.
        iApply ewp_ret_eq.
        iApply "Hy".

    + (* add's postcondition *)
      iIntros (n1 n2) "((-> & Hx) & (-> & Hy))".
      iFrame.
      iCombine "Hx" "Hy" as "H".
      iApply (goal_eq with "H"). reflexivity.

  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & -> & (Hx & Hy))".
    iExists _. iFrame.
    iNext. iIntros "Hx".
    rewrite M.add_repr_repr.
    auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double env x lx n :
  lookup_name env x = ret (VLoc lx) ->
  lx ↦ V #n
  ⊢ EWP (eval env (EStore (EVar x) (ELoad (EVar x) + ELoad (EVar x))))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V #(2 * n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (ewp_EStore with "[] [Hx]").
  { Simp. iApply ewp_ret_eq_emp. }
  - (* !x + !x *)
    iDestruct "Hx" as "(Hx1 & Hx2)".
    iApply (ewp_EIntAdd with "[Hx1] [Hx2]").
    + (* !x *)
      Bind.
      iApply (ewp_ELoad).
      { Simp. iApply ewp_ret_eq_emp. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (ewp_ret_eq with "Hx1").
    + (* !x *)
      Bind.
      iApply (ewp_ELoad).
      { Simp. iApply ewp_ret_eq_emp. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (ewp_ret_eq with "Hx1").
    + (* + *)
      iIntros (_n1 _n2) "((-> & Hx1) & (-> & Hx2))".
      iCombine "Hx1" "Hx2" as "Hx".
      iApply (goal_eq with "Hx"). reflexivity.
  - (* := *)
    iIntros (_l1 _v2) "(-> & -> & Hx)".
    iExists _. iFrame. iNext. iIntros "Hx".
    rewrite M.add_repr_repr.
    replace (n + n)%Z with (2 * n)%Z by lia.
    by iFrame.
Qed.

(* match 1 with _ -> true *)

Lemma simple_PAny_match env :
  ⊢ EWP eval env
    (EMatch (EInt 1)
      [Branch (CVal PAny) (EConstant "true")])
    {{ RET #r, ⌜r = true⌝ }}.
Proof.
  iApply ewp_EMatch.
  iApply (ewp_deep_handler _ iEff_bottom).
  { iApply ewp_EInt. iApply goal_eq_emp. reflexivity. }

  rewrite deep_handler_spec_unfold; iSplit.

  - iIntros (?) "->". iNext.
    iApply handle_cons.
    + specify_cpattern.
      pattern_match. apply eq_refl.
    + iIntros (δ) "_". iApply ewp_EConstant; simpl.
      by iExists true.
    + iIntros "[]".

  - iIntros (e k) "Hp".
    unfold iEff_bottom in *.
    unfold prot in *.
    rewrite upcl_bottom.
    done.
Qed.

(*
a few examples for EMatch, for now more than necessary
we should remove most of them once EMatch rules are well understood.
TODO: simpler rule/eval function for EMatch with iEff_bottom
*)

(* match 1 with 1 -> true | _ -> false *)

Lemma simple_PInt_eq_match env :
  ⊢ EWP eval env
    (EMatch (EInt 1)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ RET #r, ⌜r = true⌝ }}.
Proof.
  iApply ewp_EMatch.
  iApply (ewp_deep_handler _ iEff_bottom).
  { iApply ewp_EInt. iApply goal_eq_emp. reflexivity. }

  rewrite deep_handler_spec_unfold; iSplit.

  - iIntros (?) "->". iNext.
    iApply handle_cons.
    + specify_cpattern.
      pattern_match.
      apply eq_refl.
    + iIntros (δ) "_".
      iApply ewp_EConstant.
      by iExists true.
    + iIntros (?). done.

  - iIntros (e k) "Hp".
    unfold iEff_bottom in *.
    unfold prot in *.
    rewrite upcl_bottom.
    done.
Qed.

(* match 2 with 1 -> true | _ -> false *)

Lemma simple_PInt_neq_match env :
  ⊢ EWP eval env
    (EMatch (EInt 2)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ RET #r, ⌜r = false⌝ }}.
Proof.
  iApply ewp_EMatch.
  iApply (ewp_deep_handler _ iEff_bottom).
  { iApply ewp_EInt. iApply goal_eq_emp. reflexivity. }

  rewrite deep_handler_spec_unfold; iSplit.

  - iIntros (?) "->". iNext.
    iApply handle_cons.
    + specify_cpattern.
      pattern_match.
      discriminate.
    + iIntros (δ) "[]".
    + iIntros (?).
      iApply handle_cons.
      * specify_cpattern.
        pattern_match.
        apply eq_refl.
      * iIntros (δ) "_".
        iApply ewp_EConstant.
        by iExists false.
      * iIntros "[]".

  - iIntros (e k) "Hp".
    unfold iEff_bottom in *.
    unfold prot in *.
    rewrite upcl_bottom.
    done.
Qed.

(* match 2 with 0 -> 0 | 1 -> 1 | 2 -> 2 *)

Lemma simple_PInt_012_match env :
  ⊢ EWP eval env
    (EMatch (EInt 2)
      [Branch (CVal (PInt 0)) (EInt 0);
       Branch (CVal (PInt 1)) (EInt 1);
       Branch (CVal (PInt 2)) (EInt 2)])
    {{ RET #r, ⌜r = 2⌝ }}.
Proof.
  iApply ewp_EMatch.
  iApply (ewp_deep_handler _ iEff_bottom).
  { iApply ewp_EInt. iApply goal_eq_emp. reflexivity. }

  rewrite deep_handler_spec_unfold; iSplit.

  - iIntros (?) "->". iNext.
    iApply handle_cons.
    + specify_cpattern.
      pattern_match.
      discriminate.
    + iIntros (δ) "[]".
    + iIntros (_).
      iApply handle_cons.
      * specify_cpattern.
        pattern_match.
        discriminate.
      * iIntros (δ) "[]".
      * iIntros (_).
        iApply handle_cons.
        -- specify_cpattern.
           pattern_match.
           apply eq_refl.
        -- iIntros (δ) "_".
           iApply ewp_EInt.
           by iExists 2.
        -- by iIntros (?).

  - iIntros (e k) "Hp".
    unfold iEff_bottom in *.
    unfold prot in *.
    rewrite upcl_bottom.
    done.
Qed.

(* checking now whether pat_pNil works with
match [] with _ :: _ -> 1 | _ -> 2 *)

Lemma simple_true_true_match env :
  ⊢ EWP eval env
    (EMatch (EData "[]" (ETuple []))
      [Branch (CVal (PData "::" (PTuple [ PAny; PAny ]))) (EInt 1);
       Branch (CVal (PConstant "[]")) (EInt 2)])
    {{ RET #r, ⌜r = 2⌝ }}.
Proof.
  iApply ewp_EMatch.
  iApply (ewp_deep_handler _ iEff_bottom).
  { iApply ewp_EConstant. iApply goal_eq_emp. reflexivity. }

  rewrite deep_handler_spec_unfold; iSplit.

  - iIntros (?) "->". iNext.
    iApply handle_cons.
    + specify_cpattern.
      pattern_match.
      discriminate.
    + iIntros (δ) "[]".
    + iIntros "_".
      iApply handle_cons.
      * specify_cpattern.
        pattern_match.
        apply eq_refl.
      * iIntros (δ) "_".
        iApply ewp_EInt.
        by iExists 2.
      * by iIntros (?).

  - iIntros (e k) "Hp".
    unfold iEff_bottom in *.
    unfold prot in *.
    rewrite upcl_bottom.
    done.
    Unshelve.
2,4: apply Encode_unit.
(* check that the meaning of the lemma does not depend on the encoded type *)
Qed.

End test_expr_rules.
