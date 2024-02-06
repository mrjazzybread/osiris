From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.

From osiris Require Import semantics.
From osiris Require Import program_logic.wp.

Ltac wp_unfold m :=
  setoid_rewrite (wp_unfold _ _ m); rewrite /wp_pre /=.

Ltac wp_unfold_head :=
  iApply wp_unfold; rewrite /wp_pre /=.

Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

Ltac wp_case_is_ret m Hret :=
  case_eq (is_ret m); [
    intros ? Hret;
    apply invert_is_ret_Some in Hret; subst m
  | intros Hret
  ].

Ltac wp_case_is_throw m Hthrow :=
  case_eq (is_throw m); [
    intros ? Hthrow;
    apply invert_is_throw_Some in Hthrow; subst m
  | intros Hthrow
  ].

Ltac destruct_wp_ret :=
  iMod "Hwp"; iModIntro; iDestruct "Hwp" as "[%Hsi Hwp]".

Ltac destruct_wp_nonret :=
  iMod "Hwp" as "[%Hcanstep Hwp]".

Ltac intro_state := iIntros (σ????) "Hsi".

Ltac spec_state H := iSpecialize (H $! _ _ _ _ _ with "Hsi").

Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro.

Ltac construct_wp_nonret :=
  iSplitR; [
    (* Prove [can_step]: *)
    iPureIntro; eauto with step can_step
  | (* Introduce a hypothetical step: *)
    iIntros (σ' m' ? ) "%Hstep"
  ].
