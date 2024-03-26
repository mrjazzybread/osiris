From iris Require Import gen_heap proofmode.proofmode.
From osiris.program_logic Require Import wp rules wp_expr.
From osiris.proofmode Require Import proofmode.

Section test_wp_expr.
Context `{!osirisGS Σ}.

(* Useful when goal is [R ⊢ WP (ret v) {{ ?evar }}] *)
(* iApply-ing it will fail without providing much information if [R] or [v]
   depends on a variable [y] that was created after the creation of the evar, in
   which case, instantiate the evar with something like [λx, ∃y, ⌜x = y⌝ ∗ R] *)
Lemma wp_ret_eq {A E} (v : A) R : R ⊢ WP (@Ret A E v) {{ (λ x, ⌜x = v⌝%I ∗ R)↑ }}.
Proof.
  iIntros "H".
  wp.
  iFrame.
  auto.
Qed.

(* Simpler case with no useful resource *)
Lemma wp_ret_eq_emp {A E} (v : A) : ⊢ WP (@Ret A E v) {{ (λ x, ⌜x = v⌝%I)↑ }}.
Proof.
  wp.
  auto.
Qed.

(* Useful when goal is [R ⊢ ipure ?Evar v] *)
Lemma ipure_val {A E} R v :
  R ⊢ ipure ((λ r, ⌜r = Res v⌝ ∗ R) : @outcome A E → iProp Σ) v.
Proof.
  iIntros "H". iFrame. auto.
Qed.

(* Same with no R *)
Lemma ipure_val_emp {A E} v :
  ⊢ ipure ((λ r, ⌜r = Res v⌝) : @outcome A E → iProp Σ) v.
Proof.
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
  ⊢ WP (eval env (ERef (EInt 1))) {{ λ r, ∃ l : loc, ⌜r = Res #l⌝ ∗ l ↦ #1 }}.
Proof.
  iApply wp_ERef.
  - (* 1 *)
    wp_simp.
    iApply wp_ret_eq_emp.
  - (* ref *)
    iIntros (v) "->".
    iIntros (l) "(? & ?)". iExists _. iFrame. auto.
Qed.

(* [!x] *)
Lemma example_load env x l v :
  lookup_name env x = ret #l -> 
  l ↦ v ⊢ WP (eval env (ELoad (EVar x))) {{ λ r, ⌜r = Res v⌝ ∗ l ↦ v }}.
Proof.
  iIntros (Hx) "Hl".
  iApply wp_ELoad.
  wp_simp.
  iApply wp_ret_eq_emp.
  iIntros (?) "->".
  iExists _, _. iFrame. auto.
Qed.

(* [x := 2] *)
Lemma example_store env x l :
  lookup_name env x = ret #l -> 
  l ↦ #1
    ⊢ WP (eval env (EStore (EVar x) (EInt 2)))
    {{ λ r, ⌜r = Res #tt⌝ ∗ l ↦ #2 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply wp_EStore.
  wp_simp.
  iApply wp_ret_eq_emp.
  iApply wp_ret_eq_emp.
  iIntros (? ?) "(-> & ->)".
  iExists _. iFrame.
  auto.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores env x l :
  lookup_name env x = ret #l -> 
  l ↦ #1
    ⊢ WP (eval env 
            (ESeq
               (EStore (EVar x) (EInt 2))
               (EStore (EVar x) (EInt 4))))
    {{ λ r, ⌜r = Res #tt⌝ ∗ l ↦ #4 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply wp_ESeq.
  iApply wp_EStore.
  { wp_simp. iApply wp_ret_eq_emp. }
  { iApply wp_ret_eq_emp. }
  iIntros (? ?) "(-> & ->)".
  iExists _. iFrame.
  iNext.
  iIntros "Hl".
  iApply wp_EStore.
  { wp_simp. iApply wp_ret_eq_emp. }
  { iApply wp_ret_eq_emp. }
  iIntros (? ?) "(-> & ->)".
  iExists _. iFrame. auto.
Qed.

(* [!(ref 1)] *)
Lemma example_load_ref env :
  ⊢ WP (eval env (ELoad (ERef (EInt 1)))) {{ λ r, ⌜r = Res #1⌝ }}.
Proof.
  iApply wp_ELoad.
  - (* ref 1 *)
    iApply wp_bind.
    iApply wp_ERef.
    { iApply wp_ret_eq_emp. }
    iIntros (?) "->".
    iIntros (l) "(Hl & _) /=".
    instantiate (1 := (λ r, ∃ l, ⌜r = Res l⌝ ∗ l ↦ VInt (repr 1))%I).
    iApply wp_ret.
    iExists l. iFrame. auto.
  
  - (* load *)
    simpl.
    iIntros (l) "Hl".
    iDestruct "Hl" as (?) "(%E & Hl)". injection E as <-.
    iExists _, _.
    iFrame.
    auto.
Qed.

(* [!(ref 1)] -- with anticipated postcondition for [ref 1] *)
Lemma example_load_ref_ env :
  ⊢ WP (eval env (ELoad (ERef (EInt 1)))) {{ λ r, ⌜r = Res #1⌝ }}.
Proof.
  iApply (wp_ELoad _ _ ( | RET l =>l ↦ #1; | EXN _ => False)%I).
  - (* ref 1 *)
    iApply wp_bind.
    iApply wp_ERef.
    { iApply wp_ret_eq_emp. }
    iIntros (?) "->".
    iIntros (l) "(Hl & _) /=".
    iApply wp_ret.
    auto.
  
  - (* load *)
    simpl.
    iIntros (l) "Hl".
    iExists _, _.
    iFrame.
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr env x lx n :
  lookup_name env x = ret #lx ->
  lx ↦ #n
  ⊢ WP (eval env (EStore (EVar x) (EIntAdd (EInt 1) (ELoad (EVar x)))))
    {{ λ r, ⌜r = Res #tt⌝ ∗ lx ↦ VInt (repr (1 + n)) }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (wp_EStore with "[] [Hx]").

  - (* l-value x *)
    wp_simp. iApply wp_ret_eq_emp.

  - (* 1 + !x *)
    iApply (wp_EIntAdd with "[] [Hx]").
    + (* as_int 1 *)
      wp_simp. iApply wp_ret_eq_emp.
    + (* as_int !x *)
      iApply wp_bind.
      iApply wp_ELoad.
      { wp_simp.
        iApply wp_ret_eq_emp. }
      iIntros (l) "->".
      iExists _, _; iFrame.
      iNext.
      iIntros "Hx".
      iApply wp_ret_eq.
      iApply "Hx".
    + (* add's postcondition *)
      iIntros (n1 n2) "(-> & (-> & Hx))".
      iApply goal_eq. reflexivity.
      iApply "Hx".

  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & %Ev2 & A)".
    injection Ev2 as ->.
    iExists _. iFrame.
    rewrite add_repr_repr.
    auto.
Qed.

(* [x := !x + (y := 1 + !y; !y)] *)
Lemma example_incr_via_y env x lx y ly n :
  lookup_name env x = ret #lx ->
  lookup_name env y = ret #ly ->
  lx ↦ #n ∗ ly ↦ #0
  ⊢ WP (eval env (EStore (EVar x) (ELoad (EVar x) +
         ESeq (EStore (EVar y) (EIntAdd (EInt 1) (ELoad (EVar y)))) (ELoad (EVar y))
       )))
    {{ λ r, ⌜r = Res #tt⌝ ∗ lx ↦ VInt (repr (n + 1)) ∗ ly ↦ #1 }}.
Proof.
  iIntros (Ex Ey) "(Hx & Hy)".
  iApply (wp_EStore with "[] [Hx Hy]").

  - (* l-value x *)
    wp_simp. iApply wp_ret_eq_emp.

  - (* !x + (...) *)
    iApply (wp_EIntAdd with "[Hx] [Hy]").
    + (* as_int !x *)
      iApply wp_bind.
      iApply wp_ELoad.
      wp_simp. iApply wp_ret_eq_emp. iIntros (l) "->".
      iExists _, _. iFrame. iNext.
      iIntros "Hx".
      iApply wp_ret_eq.
      iApply "Hx".
    + (* as_int (y := 1 + !y; !y) *)
      iApply wp_bind.
      iApply wp_ESeq.
      (* y := 1 + !y: use previous example *)
      iApply wp_mono.
      2: now iApply (example_incr with "Hy").
      iIntros ([v_|[]]) "(_ & HX)". clear v_.
      (* !y *)
      iApply wp_ELoad.
      wp_simp.
      iApply wp_ret_eq_emp. iIntros (l) "->".
      iExists _, _. iFrame. iNext.
      iIntros "Hy". simpl.
      iApply wp_ret_eq.
      iApply "Hy".
    + (* add's postcondition *)
      iIntros (n1 n2) "((-> & Hx) & (-> & Hy))".
      iFrame.
      iApply goal_eq. reflexivity.
      iCombine "Hx" "Hy" as "H".
      iApply "H".

  - (* store's postcondition *)
    iIntros (l1 v2) "(-> & %Ev2 & (Hx & Hy))".
    injection Ev2 as ->.
    iExists _. iFrame.
    iNext. iIntros "Hx".
    rewrite add_repr_repr.
    auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double env x lx n :
  lookup_name env x = ret #lx ->
  lx ↦ #n
  ⊢ WP (eval env (EStore (EVar x) (EIntAdd (ELoad (EVar x)) (ELoad (EVar x)))))
    {{ λ r, ⌜r = Res #tt⌝ ∗ lx ↦ VInt (repr (2 * n)) }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (wp_EStore with "[] [Hx]").
  { wp_simp. iApply wp_ret_eq_emp. }
  - (* !x + !x *)
    iDestruct "Hx" as "(Hx1 & Hx2)".
    iApply (wp_EIntAdd with "[Hx1] [Hx2]").
    + (* !x *)
      iApply wp_bind.
      iApply (wp_ELoad).
      { wp_simp. iApply wp_ret_eq_emp. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (wp_ret_eq with "Hx1").
    + (* !x *)
      iApply wp_bind.
      iApply (wp_ELoad).
      { wp_simp. iApply wp_ret_eq_emp. }
      iIntros (l) "->".
      iExists _, _. iFrame. iNext. iIntros "Hx1". simpl.
      iApply (wp_ret_eq with "Hx1").
    + (* + *)
      iIntros (_n1 _n2) "((-> & Hx1) & (-> & Hx2))".
      iCombine "Hx1" "Hx2" as "Hx".
      iApply (goal_eq with "Hx"). reflexivity.
  - (* := *)      
    iIntros (_l1 _v2) "(-> & %E & Hx)".
    injection E as ->.
    iExists _. iFrame. iNext. iIntros "Hx".
    rewrite add_repr_repr.
    replace (n + n) with (2 * n) by lia.
    auto.
Qed.

End test_wp_expr.
