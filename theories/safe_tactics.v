Require Import base lang free eval step safe refinement.

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
  | apply prove_safe_loop_ret; cbn
  | apply prove_safe_loop; cbn
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
  unfold is_safe;
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

(* -------------------------------------------------------------------------- *)

(* Do not allow [call] to be unfolded. We do not want symbolic execution
   to automaticaly step into function calls. *)

Global Opaque call.
Ltac wp_call :=
  with_strategy transparent [call] unfold call;
    (* TODO make sure that we unfold just the root occurrence *)
  wp.

(* -------------------------------------------------------------------------- *)

(* Do not allow [concatenating] to be unfolded. We want symbolic execution
   to stop at [concatenating], that is, when the environment is extended
   with new bindings. This gives the user a chance to prove specifications
   about these bindings using [wp_specify]. *)

Global Opaque concatenating.

(* The tactic [wp_continue] expands away [concatenating] and invokes [wp]
   to continue simplifying the goal. *)

Lemma concatenating_def eval η e δ :
  concatenating eval η e δ =
  let η := concat δ η in eval η e.
Proof.
  reflexivity.
Qed.

Ltac wp_continue :=
  rewrite concatenating_def; wp.

(* The tactic [wp_specify x φ] should be used when the goal begins with
   [concatenating eval η e δ], that is, when the environment is about to
   be extended with the environment fragment [δ].

   The tactic looks up the variable [x] in the environment fragment [δ]
   so as to find the value [v] of this variable. Then, it produces two
   subgoals:
   - the subgoal [φ v],
     letting the user prove that [v] satisfies the specification [φ];
   - the original goal,
     generalized under the form [∀ v, φ v → ...],
     which means that [v] becomes an opaque value
     about which nothing is known except that [φ v] holds. *)

Ltac wp_specify x φ :=
  match goal with |- context[concatenating eval _ _ ?δ] =>
    let o := eval cbn in (lookup δ x) in
    match o with
    | Ret ?v =>
        let H := fresh "spec" in
        assert (spec: φ v); [| revert spec; generalize v ]
          (* not perfect, as [generalize] could abstract [v] away
             also inside φ, which would be undesirable *)
    end
  end.
