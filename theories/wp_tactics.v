From iris.proofmode Require Import proofmode.
From iris.bi Require Import weakestpre.
Require Import free eval wp.

(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

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

Ltac wp_step :=
  (* The lazymatch stills misses a few cases and should be completed. *)
  lazymatch goal with
  | |- environments.envs_entails _
        (wp _ _ (ret _) _) => iApply wp_ret
  | |- environments.envs_entails _
        (wp _ _ (bind _ _) _) => iApply wp_bind
  | |- environments.envs_entails _
        (wp _ _ (Par (ret _) (ret _) _ _) _) => iApply wp_par_ret_ret
  | |- environments.envs_entails _
        (wp _ _ (Par _ (ret _) ?k ?ko) _) =>
      iApply wp_par_ret_right
  | |- environments.envs_entails _
        (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      iApply wp_par_ret_left
  | |- environments.envs_entails _
        (wp _ _ (try (ret _) _ _) _) => iApply wp_try_ret
  | |- environments.envs_entails _
        (wp _ _ (eval.lookup _ _) _) => simpl (eval.lookup _ _)
  | |- environments.envs_entails _
        (wp _ _ (stop Eval _) _) =>
      (iApply wp_eval_ret + iApply wp_eval)
  | |- environments.envs_entails _
        (wp _ _ (Stop Flip _ _) _) => iApply wp_flip
  end;
  cbn.

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
