Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.semantics Require Import step code.

(* ------------------------------------------------------------------------ *)

Section wp_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ}.

  (* Values *)
  Lemma ewp_value {X} E Ψ Φ v :
    Φ (O2Ret v) -∗ EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_ret_inv {X} E Ψ Φ v :
    EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Ret v).
  Proof. Admitted.

  Lemma ewp_throw {X} E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_throw_inv {X} E Ψ Φ v :
    EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Throw v).
  Proof. Admitted.

  Lemma ewp_outcome2 {X} E Ψ Φ v :
    Φ v -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.
  Lemma ewp_outcome2_inv {X} E Ψ Φ v :
    EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
  Proof. Admitted.

  Lemma ewp_outcome2_fupd {X} E Ψ Φ v :
    (|={E}=> Φ v) -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

  (* ------------------------------------------------------------------------ *)
  (** Monotonicity. *)
  Lemma wp_covariant {X} E (m : micro A X) φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ φ' }}.
  Proof. Admitted.

  (* TODO: Strong monotonicity principle over ordering on protocols *)

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)

  (** *Bind rule *)

End wp_rules.
