Require Import monads lang free eval spec handle wp handle_spec.

(* Rewrite [decide (x = x)] to [true]. *)

Ltac wp_decide :=
  match goal with
  | |- context[decide ?P] =>
      let H := fresh "decision" in
      set (H := decide P);
      cbv in H;
      unfold H;
      clear H
  end.

Goal
  (if decide ("x" = "x") then True else False).
Proof.
  wp_decide. simpl. tauto.
Qed.

Goal
  (if decide ("x" = "y") then False else True).
Proof.
  wp_decide. simpl. tauto.
Qed.

(* Simplify a goal of the form [handle m ∋ φ]. *)

Ltac wp_simplify :=
  cbn;
  repeat progress (wp_decide; cbn);
  try rewrite !fold_bind.

(* Reduce and reason about a goal of the form [handle m ∋ φ]. *)

Ltac wp :=
  (* Expose [handle (eval η e) ∋ φ] in the goal. *)
  try unfold wp, run;
  (* Repeatedly simplify. *)
  wp_simplify;
  repeat first [
    apply prove_handle_ret; wp_simplify
  | apply prove_handle_bind; wp_simplify
  ].
