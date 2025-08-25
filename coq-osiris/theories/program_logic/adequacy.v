From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.
From iris.program_logic Require Import weakestpre adequacy.

From osiris.program_logic Require Import ewp basic_rules tactics.


(* -------------------------------------------------------------------------- *)
Section ewp_wp.

  Import ewp_rules_tactics.

  (*  We show an adequacy of a closed program using the fact that the adequacy of
    [EWP] is a consequence of the adequacy of [WP]. This is following the adequacy
    proof of [Hazel] (de Vilhena & Pottier) *)

  Lemma ewp_imp_wp {Σ}
    {irisGen: irisGS_gen HasNoLc (@osiris_lang val exn) Σ}
    E (m : micro val exn) (Φ : outcome2 val exn -> _) :
    EWP m @ E <| ⊥ |> {{ Φ }} -∗ WP m @ NotStuck; E {{ Φ }} : iProp Σ.
  Proof.
  Abort.

  (* This strategy no longer works, because the Iris-instantiate [WP] is not
     able to step through forks or joins. *)

End ewp_wp.


(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  Context {A X : Type} {Σ : gFunctors}.

  Context `{!osirisGpreS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations. *)

  Theorem ewp_adequacy (m : micro A X) σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ},
    (* If [⊢ ⟨ ⊥ ⟩ impure m (λ v. ⌜φ v⌝)] holds *)
    ⊢ EWP m @ ⊤ <| ⊥ |> {{ fun o =>  ⌜ φ o ⌝ }}) →
    (* Then executing [m] cannot terminate with an unhandled effect or a crash, *)
    adequate NotStuck m
      σ (* in any initial heap, *)
      (λ o _, φ o) (* and the returned outcome satisfies the postcondition [φ] *).
  Proof.
  Abort.

End adequacy.
