From iris Require Import gen_heap proofmode.proofmode.
From osiris.lang Require Import locations.
From osiris.program_logic Require Import ewp rules.
From osiris.proofmode Require Import notations ewp_tactics.

Section ewp_expr_rules.

  Context `{protocol_wf Σ P} `{!osirisGS Σ}.

  Lemma ewp_ERef env e φ1 φ Ψ :
    EWP (eval env e) <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Ret v) -∗ ∀ l, l ↦ V v -∗ φ (O2Ret (VLoc l))) -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    EWP (eval env (ERef e)) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "He P E".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "He").
    iIntros ([v|v]) "H".
    - Alloc l "Hl".
      Bind.
      Ret.
      Ret.
      iApply ("P" with "H"). auto.
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_EStore env e1 e2 φ1 φ2 φ Ψ :
    EWP (as_loc (eval env e1)) <|Ψ|> {{ φ1 }} -∗
    EWP (eval env e2) <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l1 v2, φ1 (O2Ret l1) ∗ φ2 (O2Ret v2) -∗
      ∃ v1, l1 ↦ V v1 ∗ ▷(l1 ↦ V v2 -∗ φ (O2Ret VUnit))) -∗
    EWP (eval env (EStore e1 e2)) <|Ψ|> {{ φ }}.
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

  Lemma ewp_ELoad env e φ1 φ Ψ :
    EWP (as_loc (eval env e)) <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l, φ1 (O2Ret l) -∗ ∃ q v, mapsto l q (V v) ∗ ▷(mapsto l q (V v) -∗ φ (O2Ret v))) -∗
    EWP (eval env (ELoad e)) <|Ψ|> {{ φ }}.
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

  Lemma ewp_ESeq env e1 e2 φ1 φ Ψ :
    EWP (eval env e1) <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1, φ1 (O2Ret v1) -∗ EWP (eval env e2) <|Ψ|> {{ φ }}) -∗
    EWP (eval env (ESeq e1 e2)) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "/= H1".
    - iApply ("P" with "H1").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_EIntAdd env e1 e2 φ1 φ2 φ Ψ :
    EWP (as_int (eval env e1)) <|Ψ|> {{ φ1 }} -∗
    EWP (as_int (eval env e2)) <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ n1 n2, φ1 (O2Ret n1) ∗ φ2 (O2Ret n2) -∗ φ (O2Ret (VInt (int.M.add n1 n2)))) -∗
    EWP (eval env (EIntAdd e1 e2)) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". Throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". Throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2". Bind. Ret. Ret.
      iApply "P". iFrame.
  Qed.

End ewp_expr_rules.
