Require Import monads lang free eval step safe wp.

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

(* Simplify a goal of the form [safe m φ]. *)

Ltac wp_simplify :=
  cbn;
  repeat progress (wp_decide; cbn).

(* Simplify goals that introduce simple values. *)

Ltac wp_intro :=
  match goal with |- ∀ v, v = VUnit → _ => intros v ?; subst v end.

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
    | wp_intro (* user goal here: continuation *) ]
  end

(* Reduce and reason about a goal of the form [safe m φ]. *)

with wp_step :=
  first [
    apply prove_safe_ret; wp_simplify
  | apply prove_safe_bind; wp_simplify
  | apply prove_safe_stop; wp_simplify
  | apply prove_safe_flip; intro; wp_simplify
  | wp_scoped_case_analysis
  ].

(* Apply brute force. *)

Ltac wp :=
  unfold wp;
  wp_simplify;
  repeat wp_step.
    (* TODO not clearly correct: should we iterate? *)
