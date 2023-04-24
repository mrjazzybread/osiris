From iris.proofmode Require Import proofmode.
From iris.bi Require Import weakestpre.
Require Import free eval wp.

(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

(* TODO:
 * - instead of using [cbn], try to only reduce what should be reduced
 *   For example, continuations and hypotheses should never be reduced by
 *   tactics aimed for the goal.
 *
 * - Find a better way to hide continuations.
 *   The current behaviour is:
 *     if the goal is a [Par _ ret k ko] or [Par ret _ k ko], then remember
 *     [k] and [ko].
 *   Thus, continuations only appear once in the proof term as the other
 *   occurences are replaced by the fresh variable allocated by [remember].
 *
 *   This is important, as it prevents the proof term (and the duration
 *   of lemmas applications and Qed) to explode
 *
 *   Note : the use of an ad-hoc opaque identity function is also slow.
 *          => TODO: understand why and if fixable, use it instead.
 *)

Ltac wp_restore :=
  try lazymatch goal with
    | H: ?k = _ |- environments.envs_entails _
                    (wp _ _ (?k _) _) =>
        rewrite H (* -our__id_is_id *); clear H k
    end.

Ltac wp_remember k :=
  let Hk := fresh "Hk" in
  remember k eqn:Hk.

Ltac wp_step :=
  wp_restore;
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
      wp_remember k;
      wp_remember ko;
      iApply wp_par_ret_right
  | |- environments.envs_entails _
        (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      wp_remember k;
      wp_remember ko;
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
  | H: ?k = _ |- environments.envs_entails _
                  (wp _ _ (?k _) _) =>
      rewrite H; clear H k
  end;
  cbn.

Ltac wp :=
  iStartProof;
  cbn; (* TODO: better control the reduction strategy. *)
  (repeat
    lazymatch goal with
    | |- environments.envs_entails _ (bi_later _) => iNext
    | _ => wp_step
     end);
  repeat wp_restore.

Ltac wp_par :=
  iApply wp_par; [wp | wp | ]; wp_restore.

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ]; wp_restore.

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  ];
  simpl; wp_restore.

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
