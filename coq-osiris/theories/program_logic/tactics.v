From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.

From osiris Require Import semantics.
From osiris Require Import program_logic.wp.

(* -------------------------------------------------------------------------- *)

(* WP tactics. *)

Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

(* This tactic unfolds [wp] applied to the computation [m]. *)

Ltac wp_unfold m :=
  setoid_rewrite (wp_unfold _ _ m); rewrite /wp_pre /=.

(* This tactic unfolds one occurrence of [wp] at the head of the goal. *)

Ltac wp_unfold_head :=
  iApply wp_unfold; rewrite /wp_pre /=.

(* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
   of the form [ret a], or it is not. In the second branch, the equality
   [is_ret m = None] appears under the name [Hret]. *)

Ltac wp_case_is_ret m Hret :=
  case_eq (is_ret m); [
    intros ? Hret;
    apply invert_is_ret_Some in Hret; subst m
  | intros Hret
  ].

(* [wp_case_is_throw m Hthrow] performs a case analysis on [m]: either it is
   of the form [throw a], or it is not. In the second branch, the equality
   [is_throw m = None] appears under the name [Hthrow]. *)

Ltac wp_case_is_throw m Hthrow :=
  case_eq (is_throw m); [
    intros ? Hthrow;
    apply invert_is_throw_Some in Hthrow; subst m
  | intros Hthrow
  ].

(* The following tactics corresponds to the branch [is_ret _ = Some _] in
   the definition of [wp]. This branch is a conjunction
     state_interp σ ∗ φ v
   [destruct_wp_ret] is used when this form appears in the hypothesis "Hwp". *)

Ltac destruct_wp_ret :=
  iMod "Hwp"; iModIntro; iDestruct "Hwp" as "[%Hsi Hwp]".

Ltac destruct_wp_nonret :=
  iMod "Hwp" as "[%Hcanstep Hwp]".

(* Working with the state interpretation invariant. *)

(* [intro_state] introduces [σ] and [state_interp σ]. *)
(* [spec_state H] specializes the hypothesis H with [state_interp σ]. *)

Ltac intro_state := iIntros (σ????) "Hsi".

Ltac spec_state H := iSpecialize (H $! _ _ _ _ _ with "Hsi").

(* [tick_wp] is used when the goal is
   [|==> ▷ (state_interp σ' ∗ wp E m' φ)]. *)

Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro.

(* The following two tactics correspond to the branch [is_ret _ = None] in
   the definition of [wp]. This branch is a conjunction
     ⌜can_step (σ, m)⌝ ∗ ∀ σ' m', ...
   [construct_wp_nonret] is used when this form appears in the goal.
   [destruct_wp_nonret] is used when it appears in the hypothesis "Hwp". *)

Ltac construct_wp_nonret :=
  iSplitR; [
    (* Prove [can_step]: *)
    iPureIntro; eauto with step can_step
  | (* Introduce a hypothetical step: *)
    iIntros (σ' m' ? ) "%Hstep"
  ].
