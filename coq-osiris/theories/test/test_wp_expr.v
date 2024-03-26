From iris Require Import gen_heap proofmode.proofmode.
From osiris.lang Require Import locations sugar.
From osiris.program_logic Require Import ewp rules wp_expr.
From osiris.proofmode Require Import proofmode notations.

Section test_ewp_expr.
Context `{protocol_wf Σ P} `{!osirisGS Σ}.

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

(* Useful when goal is [R ⊢ ?Evar v] *)
Lemma goal_eq {A} (v : A) (R : iProp Σ) φ :
  φ = (λ x, ⌜x = v⌝ ∗ R)%I ->
  R ⊢ φ v.
Proof.
  iIntros (->) "R".
  auto.
Qed.

(* [ref 1] *)

Lemma example_ref_1 env:
  ⊢ EWP (eval env (ERef (EInt 1))) {{ RET v, ∃ l : loc, ⌜v = VLoc l⌝ ∗ l ↦ V (VInt int.one) }}.
Proof.
  iApply ewp_ERef.
  - (* 1 *)
    iApply ewp_ret_eq_emp.
  - (* ref *)
    iIntros (v) "->".
    iIntros (l) "(? & ?)". iExists _. iFrame. auto.
  - (* exn *)
    iIntros (?) "[]".
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
  - iIntros (?) "[]".
  - iIntros (?) "->".
    iExists _, _. iFrame. auto.
Qed.

(* [x := 2] *)
Lemma example_store env x l :
  lookup_name env x = ret (VLoc l) ->
  l ↦ V (VInt (int.repr 1))
    ⊢ EWP (eval env (EStore (EVar x) (EInt 2)))
    {{ RET r, ⌜r = VUnit⌝ ∗ l ↦ V (VInt (int.repr 2)) }}.
Proof.
  iIntros (Hx) "Hl".
  iApply ewp_EStore.
  - Simp. iApply ewp_ret_eq_emp.
  - iApply ewp_ret_eq_emp.
  - iIntros (?) "[]".
  - iIntros (?) "[]".
  - iIntros (? ?) "(-> & ->)".
    iExists _. iFrame. iNext.
    iIntros "Hl /=".
    auto.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores env x l :
  lookup_name env x = ret (VLoc l) ->
  l ↦ V (VInt (int.repr 1))
    ⊢ EWP (eval env
            (ESeq
               (EStore (EVar x) (EInt 2))
               (EStore (EVar x) (EInt 4))))
    {{ RET r, ⌜r = VUnit⌝ ∗ l ↦ V (VInt (int.repr 4)) }}.
Proof.
  iIntros (Hx) "Hl".
  iApply (ewp_ESeq with "[Hl]").
  - iApply ewp_EStore.
    + Simp. iApply ewp_ret_eq_emp.
    + iApply ewp_ret_eq_emp.
    + iIntros (?) "[]".
    + iIntros (?) "[]".
    + iIntros (? ?) "(-> & ->)".
      iExists _. iFrame. iNext. iIntros "Hl".
      iApply (goal_eq with "Hl"). reflexivity.
  - iIntros (?) "(% & _)". discriminate.
  - iIntros (?) "(%E & Hl)".
    iApply ewp_EStore.
    + Simp. iApply ewp_ret_eq_emp.
    + iApply ewp_ret_eq_emp.
    + iIntros (?) "[]".
    + iIntros (?) "[]".
    + iIntros (? ?) "(-> & ->)".
      iExists _. iFrame. iNext. iIntros "$ //".
Qed.

(* [!(ref 1)]  *)
Lemma example_load_ref env :
  ⊢ EWP (eval env (ELoad (ERef (EInt 1)))) {{ RET r, ⌜r = VInt (int.repr 1)⌝ }}.
Proof.
  iApply (ewp_ELoad _ _ ( | RET l => (l : loc) ↦ V (VInt (int.repr 1)); | EXN _ => False)%I).
  - (* ref 1 *)
    Bind.
    iApply ewp_ERef.
    + iApply ewp_ret_eq_emp.
    + iIntros (?) "->".
      iIntros (l) "Hl /=".
      by Ret.
    + iIntros (?) "[]".
  - iIntros (?) "[]".
  - (* load *)
    iIntros (l) "Hl".
    iExists _, _.
    iFrame.
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr env x lx n :
  lookup_name env x = ret (VLoc lx) ->
  lx ↦ V (VInt (int.repr n))
  ⊢ EWP (eval env (EStore (EVar x) (EIntAdd (EInt 1) (ELoad (EVar x)))))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V (VInt (int.repr (1 + n))) }}.
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
      * iIntros (?) "[]".
      * iIntros (l) "->".
        iExists _, _; iFrame.
        iNext.
        iIntros "Hx".
        iApply (ewp_ret_eq with "Hx").

    + iIntros (?) "[]".
    + iIntros (?) "[]".
    + (* add's postcondition *)
      iIntros (n1 n2) "(-> & (-> & Hx))".
      iApply (goal_eq with "Hx"). reflexivity.

  - iIntros (?) "[]".
  - iIntros (?) "(% & _)". discriminate.
  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & %Ev2 & A) /=".
    iExists _. iFrame. iNext.
    injection Ev2 as ->.
    rewrite int.M.add_repr_repr.
    auto.
Qed.

(* [x := !x + (y := 1 + !y; !y)] *)
Lemma example_incr_via_y env x lx y ly n :
  lookup_name env x = ret (VLoc lx) ->
  lookup_name env y = ret (VLoc ly) ->
  lx ↦ V (VInt (int.repr n)) ∗ ly ↦ V (VInt (int.repr 0))
  ⊢ EWP (eval env (EStore (EVar x) (ELoad (EVar x) +
         ESeq (EStore (EVar y) (EIntAdd (EInt 1) (ELoad (EVar y)))) (ELoad (EVar y))
       )))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V (VInt (int.repr (n + 1)%Z)) ∗ ly ↦ V (VInt (int.repr 1)) }}.
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
      * iIntros (?) "[]".
      * iIntros (l) "->".
        iExists _, _. iFrame. iNext.
        iIntros "Hx".
        iApply (ewp_ret_eq with "Hx").

    + (* as_int (y := 1 + !y; !y) *)
      Bind.
      iApply (ewp_ESeq with "[Hy]").
      * (* y := 1 + !y: use previous example *)
        iApply (example_incr with "Hy"). done.
      * iIntros (?) "[]".
      * (* !y *)
        iIntros (v_) "(-> & A)".
        iApply ewp_ELoad.
        -- Simp. iApply ewp_ret_eq_emp.
        -- iIntros (?) "[]".
        -- iIntros (l) "->".
           iExists _, _. iFrame. iNext.
           iIntros "Hy". simpl.
           iApply ewp_ret_eq.
           iApply "Hy".

    + iIntros (?) "[]".
    + iIntros (?) "[]".
    + (* add's postcondition *)
      iIntros (n1 n2) "((-> & Hx) & (-> & Hy))".
      iFrame.
      iCombine "Hx" "Hy" as "H".
      iApply (goal_eq with "H"). reflexivity.

  - iIntros (?) "[]".
  - iIntros (?) "(% & _)". discriminate.
  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & %Ev2 & (Hx & Hy))".
    injection Ev2 as ->.
    iExists _. iFrame.
    iNext. iIntros "Hx".
    rewrite int.M.add_repr_repr.
    auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double env x lx n :
  lookup_name env x = ret (VLoc lx) ->
  lx ↦ V (VInt (int.repr n))
  ⊢ EWP (eval env (EStore (EVar x) (EIntAdd (ELoad (EVar x)) (ELoad (EVar x)))))
    {{ RET r, ⌜r = VUnit⌝ ∗ lx ↦ V (VInt (int.repr (2 * n))) }}.
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
      { iIntros (?) "[]". }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (ewp_ret_eq with "Hx1").
    + (* !x *)
      Bind.
      iApply (ewp_ELoad).
      { Simp. iApply ewp_ret_eq_emp. }
      { iIntros (?) "[]". }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (ewp_ret_eq with "Hx1").
    + iIntros (?) "[]".
    + iIntros (?) "[]".
    + (* + *)
      iIntros (_n1 _n2) "((-> & Hx1) & (-> & Hx2))".
      iCombine "Hx1" "Hx2" as "Hx".
      iApply (goal_eq with "Hx"). reflexivity.
  - iIntros (?) "[]".
  - iIntros (?) "(% & _)". discriminate.
  - (* := *)
    iIntros (_l1 _v2) "(-> & %E & Hx)".
    injection E as ->.
    iExists _. iFrame. iNext. iIntros "Hx".
    rewrite int.M.add_repr_repr.
    replace (n + n)%Z with (2 * n)%Z by lia.
    by iFrame.
Qed.

End test_ewp_expr.
