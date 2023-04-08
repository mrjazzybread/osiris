Require Import base lang free eval step safe wp refinement.

(* -------------------------------------------------------------------------- *)

(* Do not allow [crash] to be unfolded. We wish to preserve the error
   message carried by [crash]. It would be lost if [crash] was unfolded. *)

Global Opaque crash.

(* Evaluate the message carried by [crash]. *)

Ltac wp_crash :=
  match goal with |- context[crash ?msg] =>
    let msg' := eval cbv in msg in
    change msg with msg'
  end.

(* -------------------------------------------------------------------------- *)

(* Simplify goals that introduce simple values. *)

Ltac wp_intros :=
  simpl;
  repeat match goal with
  | |- ?v = _ → _ => intro; try subst v
  | |- ∀ v, _     => intro
  end.

(* -------------------------------------------------------------------------- *)

(* Deal with a goal of the form [safe m φ] when we already have
   a hypothesis [H] of the form [safe m φ']. *)

Ltac wp_use H :=
  first [
    eapply H
  | eapply safe_covariant; [ eapply H |]
  ];
  simpl; wp_intros.

(* -------------------------------------------------------------------------- *)

(* Reduce and reason about a goal of the form [safe m φ]. *)

Ltac wp_step :=
  first [
    apply prove_safe_ret; cbn
  | apply prove_safe_bind; cbn
  | apply prove_safe_eval_ret; cbn
  | apply prove_safe_eval; cbn
  | apply prove_safe_flip; intro; cbn
  | apply prove_safe_par_ret_ret; cbn
  | apply prove_safe_Par_ret_left; cbn
  | apply prove_safe_Par_ret_right; cbn
  | apply prove_safe_if_left; [ cbn | cbn ]
      (* this line is intended to help reason about [EAssert] *)
  | eapply refinement_simpl; [ typeclasses eauto .. | cbn ]
      (* TODO this line should subsume [prove_safe_par_ret_ret],
              but in my tests, this does not work; investigate *)
      (* TODO develop examples where [refinement_simpl] is used *)
      (* TODO explain why there is no risk of divergence here,
              due to a trivial refinement that does not make progress *)
  ]

(* Simplify a goal of the form [wp m φ] or [safe m φ]. *)

with wp :=
  unfold wp;
  cbn;
  repeat wp_step;
  try wp_crash.

(* -------------------------------------------------------------------------- *)

(* Reason about a goal of the form [safe (Par m1 m2 k next) φ]. *)

Ltac wp_par :=
  eapply prove_safe_par; [ wp | wp |].
    (* [wp_intros] in the third subgoal would be desirable but does not
       work as expected; [simpl] is ineffective. Also, we might wish to
       let the user name the hypotheses. *)
