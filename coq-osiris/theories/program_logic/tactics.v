From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.

From osiris Require Import semantics.
From osiris Require Import program_logic.wp.

Module wp_rules_tactics.
(* -------------------------------------------------------------------------- *)

(* WP tactics that is used in [rules.v]. *)

Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

(* This tactic unfolds [wp] applied to the computation [m]. *)

Ltac wp_unfold m :=
  setoid_rewrite (wp_unfold _ _ m); rewrite /wp_pre /=.

(* This tactic unfolds one occurrence of [wp] at the head of the goal. *)

Ltac wp_unfold_head :=
  iApply wp_unfold; rewrite /wp_pre /=.

(* Reason about case analysis on [is_ret]*)
Ltac destruct_is_ret :=
  repeat match goal with
    (* Inversion for if a computation is a ret *)
    | [H : is_ret ?x = Some _ |- _] =>
        apply invert_is_ret_Some in H;
        try subst x
    (* Inversion if some bind is equivalent to a return *)
    | [H : bind _ _ = ret _ |- _] =>
        let Hm := fresh "Hm_ret" in
        let Hk := fresh "Hk_ret" in
        let a := fresh "a" in
        apply invert_bind_eq_ret in H;
        destruct H as (a & Hm & Hk);
        subst
    (* Inversion if some try is equivalent to a return *)
    | [H : try _ _ _ = ret _ |- _] =>
        let Hm := fresh "Hm_ret" in
        let Hk := fresh "Hk_ret" in
        let a := fresh "a" in
        apply invert_try_eq_ret_disj in H;
        destruct H as [(a & Hm & Hk) | (a & Hm & Hk)];
        subst
    (* Absurd goal *)
    | [H : is_not_ret (ret _) |- _] =>
        by inversion H
    end.

Ltac destruct_is_throw :=
  repeat match goal with
    (* Inversion for if a computation is a ret *)
    | [H : is_throw ?x = Some _ |- _] =>
        apply invert_is_throw_Some in H;
        try subst x
    end.

Ltac destruct_is_not_ret_or_throw :=
  match goal with
  (* Inversion for if a computation is not a [ret] or [throw] *)
  | [H : is_not_ret ?a, H' : is_not_throw ?a |- _] =>
      let Houtcome := fresh "Houtcome" in
      pose proof (is_not_ret_or_throw_to_outcome a H H') as Houtcome
  end.

(* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
   of the form [ret a], or it is not. In the second branch, the equality
   [is_ret m = None] appears under the name [Hret]. *)

Tactic Notation "wp_case_is_ret" constr(x) ident(Hret) :=
  case_eq (is_ret x);
  [ intros ? Hret;
    try destruct_is_ret |
    intros Hret;
    try destruct_is_not_ret_or_throw].

Tactic Notation "wp_case_is_ret" constr(x) :=
  let Hret := fresh "Hret" in
  wp_case_is_ret x Hret.

(* [wp_case_is_throw m Hthrow] performs a case analysis on [m]: either it is
   of the form [throw a], or it is not. In the second branch, the equality
   [is_throw m = None] appears under the name [Hthrow]. *)

Tactic Notation "wp_case_is_throw" constr(x) ident(Hthrow) :=
  case_eq (is_throw x);
  [ intros ? Hthrow;
    try destruct_is_throw |
    intros Hthrow;
    try destruct_is_not_ret_or_throw ].

Tactic Notation "wp_case_is_throw" constr(x) :=
  let Hthrow := fresh "Hthrow" in
  wp_case_is_throw x Hthrow.

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

Ltac spec_state :=
  lazymatch goal with
  | |- context [environments.Esnoc _ ?Hwp
      (bi_forall (fun σ1 : store =>
        bi_forall (fun _ : nat =>
          bi_forall (fun κ : list nat =>
            bi_forall (fun _ : list nat =>
              bi_forall (fun _ : nat => bi_wand (store_interp σ1) _))))))] =>
      match goal with
        | |- context [environments.Esnoc _ ?SI (store_interp ?σ)] =>
          let Hstep := fresh "Hstep" in
          iSpecialize (Hwp $! _ 0%nat nil nil 0%nat with SI);
          iMod Hwp;
          iDestruct Hwp as (Hred) Hwp
      end
  end.

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

(* -------------------------------------------------------------------------- *)

(* Misc tactics *)

Ltac to_outcome_is_Some Hm :=
  apply to_outcome_is_Some in Hm;
  destruct Hm as [ (?&?&?) | (?&?&?) ]; subst.

(* Try a tactic that acts on the conclusion of an Iris proof mode, and reverts
    the goal state into its original form. *)
Tactic Notation "try_and_revert" tactic(tac) :=
  match goal with
  | |- environments.envs_entails _ ?x =>
      try tac;
      match goal with
      | |- environments.envs_entails _ ?x' =>
          change x' with x
      end
  end.

(* Takes in an additional [revert_tac] tactic in case [change] is not enough to
  revert the goal back to its original form *)
Tactic Notation "try_and_revert"
    tactic(unrevertible_tac) tactic(revertible_tac) tactic(manual_revert):=
  unrevertible_tac;
  match goal with
  | |- environments.envs_entails _ ?x =>
      revertible_tac;
      match goal with
      | |- environments.envs_entails _ ?x' =>
          change x' with x
      end
  end;
  manual_revert.

(* Temporarily unfold [wp] to expose the [fupd] in order to apply [iMod] to a
    hypothesis. (The [try and revert] folds the [wp] definition back into shape) *)
Ltac try_iMod H :=
  match goal with
  | |- environments.envs_entails _ (wp ?s ?E ?e ?Φ) =>
      try_and_revert
        (rewrite !(wp_unfold s E e Φ))
        (rewrite /wp_pre /=; iMod H)
        (rewrite <- (wp_unfold s E e Φ))
  end.

End wp_rules_tactics.
