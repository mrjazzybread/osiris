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
Lemma imp_ret_eq `{Encode A} {E} {Ψ} (v : A) :
  ⊢ imp (@Ret val E #v) <|Ψ|> {{ λ x, ⌜x = v⌝ }}.
Proof.
  iApply imp_ret; auto.
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

Lemma example_ref_1 η:
  ⊢ imp (eval η (ERef (EInt 1))) {{ λ (l : loc), l ↦ #1%Z }}.
Proof.
  iApply imp_ERef.
  iApply imp_EInt.
Qed.

(* [!x] *)
Lemma example_load η x l v :
  lookup_name η x = ret (VLoc l) ->
  l ↦ v ⊢ imp (eval η (ELoad (EVar x))) {{ λ v', ⌜v' = v⌝ ∗ l ↦ v }}.
Proof.
  iIntros (Hx) "Hl".
  replace v with (#v) at 1 by apply solve_encode_val.
  iApply (imp_ELoad with "Hl").
  iApply imp_EPath. simpl. rewrite Hx.
  iApply imp_ret; auto.
Qed.

(* [x := 2] *)
Lemma example_store η x l :
  lookup_name η x = ret #l ->
  l ↦ #1%Z
    ⊢ imp (eval η (EStore (EVar x) (EInt 2)))
    {{ λ (_ : unit), l ↦ #2 }}.
Proof.
  iIntros (Hx) "Hl".
  iApply (imp_EStore2 (A:=Z)).
  - simpl_eval. rewrite Hx. iApply imp_widen.
    iApply (imp_ret_eq l).
  - iApply imp_EInt.
  - iIntros (? ?) "-> ->".
    iExists _. iFrame.
    auto.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores η x l :
  lookup_name η x = ret #l ->
  l ↦ #1%Z
  ⊢ imp (eval η
           (ESeq
              (EStore (EVar x) (EInt 2))
              (EStore (EVar x) (EInt 4))))
      {{ λ (_ : unit), l ↦ #4%Z }}.
Proof.
  iIntros (Hx) "Hl".
  iApply (imp_ESeq with "[Hl]").
  { iApply (imp_EStore (A:=Z) with "Hl").
    - iApply imp_EPath. rewrite /= Hx. iApply imp_ret_eq.
    - iApply imp_EInt. }
  iIntros "(% & Hl & ->)".
  iApply (imp_mono_ret with "[Hl]").
  { iApply (imp_EStore (A:=Z) with "Hl").
    - iApply imp_EPath. rewrite /= Hx. iApply imp_ret_eq.
    - iApply imp_EInt. }
  - iIntros ([]) "(% & Hl & ->)".
    iExact "Hl".
Qed.

(* [!(ref 1)]  *)
Lemma example_load_ref η :
  ⊢ imp (eval η (ELoad (ERef (EInt 1)))) {{ λ r, ⌜r = 1%Z⌝ }}.
Proof.
  iApply (imp_ELoad2 (λ l, l ↦ #1%Z)%I).
  - (* ref 1 *)
    iApply imp_ERef. iApply imp_EInt.
  - (* load *)
    iIntros (l) "Hl".
    iFrame.
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr η x lx n :
  lookup_name η x = ret #lx ->
  lx ↦ #n
  ⊢ imp (eval η (EStore (EVar x) (EIntAdd (EInt 1) (ELoad (EVar x)))))
    {{ λ (_ : unit),lx ↦ #(1 + n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (imp_EStore2 (A:=Z) with "[] [Hx]").

  - (* l-value x *)
    iApply imp_EPath. rewrite /= Ex. iApply imp_ret_eq.

  - (* 1 + !x *)
    instantiate (1 := (λ i, ⌜i = (1 + n)%Z⌝ ∗ lx ↦ #n)%I).
    iApply (imp_EIntAdd with "[] [Hx]").
    + (* 1 *)
      iApply imp_EInt.
    + (* !x *)
      iApply (imp_ELoad with "Hx").
      iApply imp_EPath. rewrite /= Ex. iApply imp_ret_eq.
    + (* add's postcondition *)
      iIntros "!>" (n1 n2) "-> (-> & $)".
      auto.

  - (* store's postcondition *)
    iIntros (l1 n2) "-> (-> & Hlx)".
    iFrame. auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double η x lx n :
  lookup_name η x = ret #lx ->
  lx ↦ #n
  ⊢ imp (eval η (EStore (EVar x) (ELoad (EVar x) + ELoad (EVar x))))
    {{ λ (_ : unit), lx ↦ #(2 * n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (imp_EStore2 (A:=Z) with "[] [Hx]").
  { iApply imp_EPath. rewrite /= Ex. iApply imp_ret_eq. }
  - (* !x + !x *)
    iDestruct "Hx" as "(Hx1 & Hx2)".
    iApply (imp_EIntAdd with "[Hx1] [Hx2]").
    + (* !x *)
      iApply (imp_ELoad with "Hx1").
      { iApply imp_EPath. rewrite /= Ex.
        iApply imp_ret_eq. }
    + (* !x *)
      iApply (imp_ELoad with "Hx2").
      { iApply imp_EPath. rewrite /= Ex.
        iApply imp_ret_eq. }
    + (* + *)
      iIntros "!>" (i j) "(-> & Hx1) (-> & Hx2)".
      iCombine "Hx1" "Hx2" as "Hx".
      iApply (goal_eq with "Hx"). reflexivity.
  - (* := *)
    iIntros (l i) "-> (-> & Hx)".
    iFrame. iIntros "!> !> Hx".
    replace (n + n)%Z with (2 * n)%Z by lia.
    by iFrame.
Qed.

(* match 1 with _ -> true *)

Lemma simple_PAny_match η :
  ⊢ imp eval η
    (EMatch (EInt 1)
      [Branch (CVal PAny) (EConstant "true")])
    {{ λ b, ⌜b = true⌝ }}.
Proof.
  iApply (imp_EMatch (A':=Z)). iApply imp_EInt.
  iIntros (?) "-> !>".
  iApply deep_handle_cons.
  { iPureIntro; ltac2:(let _ := specify_cpattern () in ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  iApply imp_EConstant; auto; encode.
Qed.

(* match 1 with 1 -> true | _ -> false *)

Lemma simple_PInt_eq_match η :
  ⊢ imp eval η
    (EMatch (EInt 1)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ λ b, ⌜b = true⌝ }}.
Proof.
  iApply (imp_EMatch (A':=Z)). iApply imp_EInt.
  iIntros (?) "-> !>".

  iApply deep_handle_cons.
  { iPureIntro; ltac2:(let _ := specify_cpattern () in ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]) ].
  - iApply imp_EConstant; auto; encode.
  - auto.
Qed.

(* checking now whether pat_pNil works with
match [] with _ :: _ -> 1 | _ -> 2 *)

Lemma simple_true_true_match `{Encode A} η :
  ⊢ imp eval η
    (EMatch (EData "[]" [])
      [Branch (CVal (PData "::" [ PAny; PAny ])) (EInt 1);
       Branch (CVal (PConstant "[]")) (EInt 2)])
    {{ λ i, ⌜i = 2%Z⌝ }}.
Proof.
  iApply (imp_EMatch (A':=list A)).
  instantiate (1 := (λ l, ⌜l=[]⌝)%I).
  iApply imp_EConstant; last done. encode.

  iIntros (?) "-> !>".
  iApply deep_handle_cons.
  { iPureIntro; ltac2:(let _ := specify_cpattern () in ()). pattern_match. }
  iSplit; [ iIntros (? []) | iIntros "%no_match1" ].
  iApply deep_handle_cons.
  { iPureIntro; ltac2:(let _ := specify_cpattern () in ()). pattern_match. apply eq_refl. }
  iSplit; [ iIntros (? ->) | iIntros ([]); auto ].
  iApply imp_EInt.
  Unshelve.
  refine (λ _, False). refine (λ _, False).
Qed.

End test_expr_rules.
