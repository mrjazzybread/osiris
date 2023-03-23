Require Import base lang free eval step safe wp.

(* Simplify a goal of the form [safe m φ]. *)

Ltac wp_simplify :=
  cbn.

(* Simplify goals that introduce simple values. *)

Ltac wp_intros :=
  simpl;
  repeat match goal with
  | |- ?v = _ → _ => intro; try subst v
  | |- ∀ v, _     => intro
  end.

(* Deal with a goal of the form [safe m φ] when we already have
   a hypothesis [H] of the form [safe m φ']. *)

Ltac wp_use H :=
  first [
    eapply H
  | eapply safe_covariant; [ eapply H |]
  ];
  simpl; wp_intros.

(* Deal with a goal of the form [safe (if b then ok else _)]. *)

Ltac wp_scoped_case_analysis :=
  match goal with |- safe (if ?b then Ret VUnit else _) _ =>
    (* We wish to perform a case analysis on [b], but first, we must
       limit the scope of this case analysis by claiming that this
       runtime assertion always succeeds. *)
    eapply safe_covariant with (φ := λ v, v = VUnit);
    [ destruct b; [
        (* trivial goal here: [VUnit = VUnit] *)
        wp_step; apply eq_refl
      | (* user goal here: must prove that the assertion succeeds *)
        idtac
      ]
    | wp_intros (* user goal here: continuation *) ]
  end

(* Reduce and reason about a goal of the form [safe m φ]. *)

with wp_step :=
  first [
    apply prove_safe_ret; wp_simplify
  | apply prove_safe_bind; wp_simplify
  | apply prove_safe_stop; wp_simplify
  | apply prove_safe_flip; intro; wp_simplify
  | apply prove_safe_par_ret_ret; wp_simplify
  | apply prove_safe_Par_ret_left; wp_simplify
  | apply prove_safe_Par_ret_right; wp_simplify
  | wp_scoped_case_analysis
  ].

(* Reason about a goal of the form [safe (Par m1 m2 k next) φ]. *)

Ltac wp_par :=
  eapply prove_safe_par.

(* Apply brute force. *)

Ltac wp :=
  unfold wp;
  wp_simplify;
  repeat wp_step.
    (* TODO not clearly correct: should we iterate? *)
