From iris.proofmode Require Import classes proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
Require Import free eval wp.

(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

Lemma tac_change_goal {Σ: gFunctors} Δ (P Q : iProp Σ) :
  (P -∗ Q) →
  environments.envs_entails Δ P →
  environments.envs_entails Δ Q.
Proof.
  intros H Henv.
  eapply coq_tactics.tac_eval; last done.
  intros Q''; subst Q''. assumption.
Qed.

(* [lem] must be of the form (P -∗ Q). Thanks to the tactic notation it can be
   lemma whose forall quantifiers have been instantiated with [_]. *)
Ltac tac_change_goal lem :=
  simple notypeclasses refine (tac_change_goal _ _ _ lem _).
Tactic Notation "tac_change_goal" uconstr(lem) := (tac_change_goal lem).

(* NOTE:
 * - The performance of the calls to [cbn] made by the functions below
 *   crucially depends on adequate unfolding settings being set for terms
 *   that can appear in the goal, using the [Arguments] command.
 *   (Such as [eval] and definition it uses transitively or combinators
 *   of the monad.)
 *
 * TODO:
-* - we still reduce too much:
 *   + we reduce under continuations;
 *   + because we reduce the whole Coq context, we reduce all the Iris
       hypotheses!
 *)

Ltac wp_step' :=
  (* The lazymatch stills misses a few cases and should be completed. *)
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ret _) _) =>
      tac_change_goal (wp_ret _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      tac_change_goal (wp_bind _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) (ret _) _ _) _) =>
      tac_change_goal (wp_par_ret_ret _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par _ (ret _) ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_right _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_left _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (try (ret _) _ _) _) =>
      tac_change_goal (wp_try_ret _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (stop Eval _) _) =>
      first [ tac_change_goal (wp_eval_ret _ _ _ _ _)
            | tac_change_goal (wp_eval _ _ _ _ _ _) ]
  | |- environments.envs_entails _ (wp _ _ (Stop Flip _ _) _) =>
      tac_change_goal (wp_flip _ _ _ _ _)
  end.

Ltac wp_step := (wp_step' || cbn).

Ltac wp :=
  iStartProof;
  cbn; (* TODO: better control the reduction strategy. *)
  (repeat
    lazymatch goal with
    | |- environments.envs_entails _ (bi_later _) => iNext
    | _ => wp_step
     end).

Ltac wp_par :=
  iApply wp_par; [wp | wp | ].

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ].

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  ];
  cbn.

Global Opaque call.
Ltac wp_call :=
  with_strategy transparent [call] unfold call; wp.


(* TODO not great *)
Ltac wp_set_postcondition :=
  match goal with
    |- @environments.envs_entails _ _
        (?ϕ ?v) =>
      is_evar ϕ;
      instantiate (1 := (λ w, ⌜w = v⌝)%I)
  end.


Ltac wp_ref ℓ H:=
  iApply wp_ref; iNext; iIntros (ℓ) H; wp.
Ltac wp_load H :=
  iApply (wp_load with H); iNext; iIntros H; wp.
Ltac wp_store H :=
  iApply (wp_store with H); iNext; iIntros H; wp.
