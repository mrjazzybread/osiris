From iris Require Import gen_heap proofmode.proofmode.
From osiris.program_logic Require Import wp rules.

Section wp_expr_rules.

  Context `{!osirisGS Σ}.

  Lemma wp_ERef env e φ1 φ :
    WP (eval env e) {{ φ1 }} -∗
    (∀ v, φ1 (Res v) -∗ ∀ l, mapsto l (DfracOwn 1) v ∗ meta_token l ⊤ -∗ φ (Res (VLoc l))) -∗
    WP (eval env (ERef e)) {{ φ }}.
  Proof.
    iIntros "He P".
    simpl.
    iApply wp_bind.
    iApply (wp_frame_wand with "P").
    iApply (wp_mono with "He").
    iIntros ([res|exn]) "H P". 2:auto.
    iApply wp_alloc.
    iNext.
    iIntros (l) "Hl".
    iApply wp_ret.
    iApply ("P" with "[$] [$]").
  Qed.

  Lemma wp_EStore env e1 e2 φ1 φ2 φ :
    WP (as_loc (eval env e1)) {{ φ1 }} -∗
    WP (eval env e2) {{ φ2 }} -∗
    (∀ l1 v2, φ1 (Res l1) ∗ φ2 (Res v2) -∗
      ∃ v1, mapsto l1 (DfracOwn 1) v1 ∗
         ▷(mapsto l1 (DfracOwn 1) v2 -∗ φ (Res #()))) -∗
    WP (eval env (EStore e1 e2)) {{ φ }}.
  Proof.
    iIntros "H1 H2 P".
    simpl.
    iApply (wp_par with "H1 H2").
    now iIntros ([]).
    now iIntros ([]).
    iIntros (l1 v2) "H1 H2".
    simpl.
    iSpecialize ("P" $! l1 v2 with "[$]").
    iDestruct "P" as (v1) "(Hl1 & P)".
    iApply (wp_store with "[$]").
    iNext.
    iIntros "Hl1".
    iApply wp_ret.
    iApply "P".
    iApply "Hl1".
  Qed.

  Lemma wp_ELoad env e φ1 φ :
    WP (as_loc (eval env e)) {{ φ1 }} -∗
    (∀ l, φ1 (Res l) -∗ ∃ q v, mapsto l q v ∗ ▷(mapsto l q v -∗ φ (Res v))) -∗
    WP (eval env (ELoad e)) {{ φ }}.
  Proof.
    iIntros "H P".
    simpl.
    iApply wp_bind.
    iApply (wp_frame_wand with "P [H]").
    iApply (wp_mono with "H").
    iIntros (v) "H1 P".
    destruct v as [l|[]]; simpl.
    iSpecialize ("P" with "H1").
    iDestruct "P" as (q v) "(Hl & P)".
    iApply (wp_load with "Hl").
    iNext.
    iIntros "Hl".
    iApply wp_ret.
    now iApply ("P" with "Hl").
  Qed.

  (* Change style to φ1, φ2, etc? *)
  Lemma wp_ESeq env e1 e2 φ :
    WP (eval env e1) {{ λ _, WP (eval env e2) {{ φ }} }} -∗
    WP (eval env (ESeq e1 e2)) {{ φ }}.
  Proof.
    iIntros "H".
    simpl.
    iApply wp_bind.
    iApply (wp_mono with "H").
    iIntros ([v|[]]) "//".
  Qed.

  Lemma wp_EIntAdd env e1 e2 φ1 φ2 φ :
    WP (as_int (eval env e1)) {{ φ1 }} -∗
    WP (as_int (eval env e2)) {{ φ2 }} -∗
    (∀ n1 n2, φ1 (Res n1) ∗ φ2 (Res n2) -∗ φ (Res (VInt (add n1 n2)))) -∗
    WP (eval env (EIntAdd e1 e2)) {{ φ }}.
  Proof.
    iIntros "H1 H2 P".
    simpl.
    iApply (wp_par with "H1 H2"). iIntros ([]). iIntros ([]).
    iIntros (n1 n2) "H1 H2".
    iApply wp_bind.
    iApply wp_ret.
    iApply wp_ret.
    iApply "P". iFrame.
  Qed.

End wp_expr_rules.
