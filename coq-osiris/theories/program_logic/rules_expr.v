From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp rules.
From osiris.proofmode Require Import notations ewp_tactics.

Section ewp_rules_expr.

  Context `{protocol_wf Σ P} `{!osirisGS Σ}.

  Lemma ewp_ERef_exn η e φ1 φ Ψ :
    EWP eval η e <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ1 (O2Ret v) -∗ ∀ l, l ↦ V v -∗ φ (O2Ret (VLoc l))) -∗
    EWP eval η (ERef e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "H".
    - Alloc l "Hl".
      Bind.
      Ret.
      Ret.
      iApply ("P" with "H"). auto.
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_ERef η e φ1 φ Ψ :
    EWP eval η e <|Ψ|> {{ RET v, φ1 v }} -∗
    (∀ v, φ1 v -∗ ∀ l, l ↦ V v -∗ φ (VLoc l)) -∗
    EWP eval η (ERef e) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ERef_exn with "H"); auto.
  Qed.

  Lemma ewp_EStore_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP as_loc (eval η e1) <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l1 v2, φ1 (O2Ret l1) ∗ φ2 (O2Ret v2) -∗
      ∃ v1, l1 ↦ V v1 ∗ ▷(l1 ↦ V v2 -∗ φ (O2Ret VUnit))) -∗
    EWP eval η (EStore e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (e) "H1". iApply ewp_throw. iApply ("E1" with "H1").
    - iIntros (e) "H2". iApply ewp_throw. iApply ("E2" with "H2").
    - iIntros (l1 v2) "H1 H2".
      iSpecialize ("P" $! l1 v2 with "[$]").
      iDestruct "P" as (v1) "(Hl1 & P)".
      Store "Hl1".
      Ret.
      iApply ("P" with "Hl1").
  Qed.

  Lemma ewp_EStore η e1 e2 φ1 φ2 φ Ψ :
    EWP as_loc (eval η e1) <|Ψ|> {{ RET l1, φ1 l1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET v2, φ2 v2 }} -∗
    (∀ l1 v2, φ1 l1 ∗ φ2 v2 -∗
      ∃ v1, l1 ↦ V v1 ∗ ▷(l1 ↦ V v2 -∗ φ VUnit)) -∗
    EWP eval η (EStore e1 e2) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EStore_exn with "H1 H2"); auto.
  Qed.

  Lemma ewp_ELoad_exn η e φ1 φ Ψ :
    EWP as_loc (eval η e) <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l, φ1 (O2Ret l) -∗ ∃ q v, mapsto l q (V v) ∗ ▷(mapsto l q (V v) -∗ φ (O2Ret v))) -∗
    EWP eval η (ELoad e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([l|v]) "H1".
    - iSpecialize ("P" with "H1").
      iDestruct "P" as (q v) "(Hl & P)".
      (Load "Hl").
      Ret.
      iApply ("P" with "Hl").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_ELoad η e φ1 φ Ψ :
    EWP as_loc (eval η e) <|Ψ|> {{ RET l, φ1 l }} -∗
    (∀ l, φ1 l -∗ ∃ q v, mapsto l q (V v) ∗ ▷(mapsto l q (V v) -∗ φ v)) -∗
    EWP eval η (ELoad e) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELoad_exn with "H"); auto.
  Qed.

  Lemma ewp_ESeq_exn η e1 e2 φ1 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1, φ1 (O2Ret v1) -∗ EWP eval η e2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (ESeq e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "/= H1".
    - iApply ("P" with "H1").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_ESeq η e1 e2 φ1 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ RET v1, φ1 v1 }} -∗
    (∀ v1, φ1 v1 -∗ EWP eval η e2 <|Ψ|> {{ RET v, φ v }}) -∗
    EWP eval η (ESeq e1 e2) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ESeq_exn with "H"); auto.
  Qed.

  Lemma ewp_EIntAdd_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP as_int (eval η e1) <|Ψ|> {{ φ1 }} -∗
    EWP as_int (eval η e2) <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ n1 n2, φ1 (O2Ret n1) ∗ φ2 (O2Ret n2) -∗ φ (O2Ret (VInt (int.M.add n1 n2)))) -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". Throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". Throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2". Bind. Ret. Ret.
      iApply "P". iFrame.
  Qed.

  Lemma ewp_EIntAdd η e1 e2 φ1 φ2 φ Ψ :
    EWP as_int (eval η e1) <|Ψ|> {{ RET n1, φ1 n1 }} -∗
    EWP as_int (eval η e2) <|Ψ|> {{ RET n2, φ2 n2 }} -∗
    (∀ n1 n2, φ1 n1 ∗ φ2 n2 -∗ φ (VInt (int.M.add n1 n2))) -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ RET n, φ n }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EIntAdd_exn with "H1 H2"); auto.
  Qed.

  Lemma ewp_eval_bindings_cons η p e bs φ1 φs φ Ψ :
    EWP eval η e <|Ψ|> {{ φ1 }} -∗
    EWP eval_bindings η bs <|Ψ|> {{ φs }} -∗
    (∀ v : exn, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v : exn, φs (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v δ, φ1 (O2Ret v) ∗ φs (O2Ret δ) -∗
      EWP widen (irrefutably_extend δ p v)  <|Ψ|> {{ φ }}) -∗
    EWP eval_bindings η (Binding p e :: bs) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H". Throw. iApply ("E1" with "H").
    - iIntros (v) "H". Throw. iApply ("E2" with "H").
    - iIntros (v δ) "H1 H2". iApply ("P" $! v δ with "[$]").
  Qed.

  Lemma ewp_ELet η bs e φ1 φ Ψ :
    EWP eval_bindings η bs <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ δ, φ1 (O2Ret δ) -∗ EWP eval (δ ++ η) e <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet bs e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hη").
    iIntros ([δ|v]) "H/=".
    - iApply ("P" with "H").
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_EAssert_exn η e φ1 φ Ψ :
    (φ (O2Ret #()))
     ∧
    (EWP eval η e <|Ψ|> {{ φ1 }} ∗
     (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
     (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #())))
    ⊢ EWP eval η (EAssert e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H /=".
    iApply ewp_Choose.
    iNext. iSplit.
    - Ret. iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "(H & E & P)".
      Try.
      iApply ewp_bind_exn.
      iApply ewp_bind_exn.
      iApply (ewp_mono with "H").
      iIntros ([v|v]) "H /=".
      * iDestruct ("P" with "H") as "(-> & H)".
        Simp. Ret. Ret. Ret.
        iApply "H".
      * Throw. iApply ("E" with "H").
  Qed.

  Lemma ewp_EAssert η e R Ψ :
    R ∧ EWP eval η e <|Ψ|> {{ RET v, ⌜v = VTrue⌝ ∗ R }}
    ⊢ EWP eval η (EAssert e) <|Ψ|> {{ RET v, ⌜v = VUnit⌝ ∗ R }}.
  Proof.
    iIntros "H".
    iApply ewp_EAssert_exn.
    iSplit.
    - iSplit; auto. iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "H".
      iSplitL "H". iAssumption.
      iSplitL. by iIntros. iIntros (v) "(-> & $) //".
  Qed.

End ewp_rules_expr.
