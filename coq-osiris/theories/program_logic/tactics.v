From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.

From osiris Require Import semantics.
From osiris Require Import program_logic.wp.


(* WP tactics that is used in [rules.v]. *)

Module wp_rules_tactics.

(* -------------------------------------------------------------------------- *)

(* Tactics relevant to [step] relation *)

(* Try to search the environment if there is something known about the head of
  the computation, i.e. [m] ; if so, try to extract as much information as
  possible *)
Tactic Notation "step_inv_aux" constr(m) constr(lem) tactic(tac) :=
  (* Generate some fresh names *)
  let Hred := fresh "Hred" in
  let m' := fresh "m'" in
  let Hstep' := fresh "Hstep'" in
  match goal with
    [ H' : reducible m _ |- _ ] =>
      pose proof (reducible_not_val _ _ H') as Hred;
      destruct lem as (m' & Hstep' & ->); [ by tac | ]
  end.

(* Invert hypotheses of the shape
    [step (σ, bind _ _) _] and [step (σ, try _ _ _) _] *)
Tactic Notation "step_inv" hyp(Hstep) :=
  match type of Hstep with
  | step (_, bind ?m _) _ =>
      (step_inv_aux m (invert_step_bind Hstep) (apply to_outcome_is_not_ret))
  | step (_, try ?m _ _) _ =>
      (step_inv_aux m (invert_step_try Hstep) (apply can_step_reducible))
  end.

(* Change goals of form [step _ _] to [prim_step _ _ _ _ _ ] *)
Tactic Notation "to_prim_step" hyp(H) :=
  match type of H with
  | step (?σ, ?m) (?σ', ?m') =>
      let H' := fresh "H'" in
      rename H into H';
      assert (H: prim_step m σ [] m' σ' []) by (constructor; eauto);
      clear H'
  end.

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


(* Use one credit in a goal *)
Ltac spec_credit H :=
  match goal with
  | |- context[environments.Esnoc _ ?Hc (lc 1)] =>
      iSpecialize (H with Hc)
  end.

(* [tick_wp] is used when the goal is
   [|==> ▷ (state_interp σ' ∗ wp E m' φ)]. *)

Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro.


(* -------------------------------------------------------------------------- *)
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

(* Takes in an additional [force_conversion] tactic in case [change] is not enough to
  revert the goal back to its original form *)
Tactic Notation "try_and_revert"
    tactic(unconvertible_tac) tactic(convertible_tac) tactic(force_conversion):=
  unconvertible_tac;
  match goal with
  | |- environments.envs_entails _ ?x =>
      convertible_tac;
      match goal with
      | |- environments.envs_entails _ ?x' =>
          change x' with x
      end
  end;
  force_conversion.

(* Temporarily unfold [wp] to expose the [fupd] in order to apply [iMod] to a
    hypothesis. (The [try and revert] folds the [wp] definition back into shape) *)
Ltac try_iMod H :=
  match goal with
  | |- environments.envs_entails _ (wp ?s ?E ?e ?Φ) =>
      first [
      try_and_revert
        (rewrite !(wp_unfold s E e Φ))
        (rewrite /wp_pre /=; iMod H)
        (rewrite <- (wp_unfold s E e Φ))
      |
      wp_unfold_all;
      destruct (to_outcome e); [ by iMod H |];
      intro_state; iMod H; spec_state ]
  end.

(* -------------------------------------------------------------------------- *)

(* Assert that [bind m1 m2] is not an outcome, deduced by [m1] not being an
    outcome *)
Tactic Notation "not_outcome:" "bind" constr(m1) constr(m2) :=
  match goal with
  | [H: to_outcome m1 = None |- _ ] =>
      apply (to_outcome_None_bind m1 m2) in H;
      try rewrite H
  end.

(* Assert that [try m _ _] is not an outcome, deduced by [m] not being an
    outcome *)
Tactic Notation "not_outcome:" "try" constr(m) constr(f) constr(h) :=
  match goal with
  | [H: to_outcome m = None |- _ ] =>
      apply (to_outcome_None_try m f h) in H;
      try rewrite H
  end.

(* Discharge pure subgoal that follows immediately by [tac] *)
Tactic Notation "discharge_pure" tactic(tac) :=
  match goal with
  | |- environments.envs_entails _ (bi_sep (bi_pure _) _) =>
      iSplitL ""; [ iPureIntro; by tac | ]
  | |- environments.envs_entails _ (bi_sep  _ (bi_pure _)) =>
      iSplitL ""; [ | iPureIntro; by tac ]
  end.

(* Discharge emp subgoal *)
Ltac discharge_emp :=
  match goal with
  | |- environments.envs_entails _ (bi_sep emp _) =>
      iSplitL ""; [ done | ]
  | |- environments.envs_entails _ (bi_sep  _ emp) =>
      iSplitR ""; [ | done ]
  end.

(* Conclude that some computation is reducible by information in the context *)
Ltac reducible :=
  (* Coq weirdness: Without this [idtac], the matched goal is not what you would
    expect when this tactic is passed into [discharge_pure] *)
  idtac
  ;
  try
  match goal with
  | [ |- match ?s with | NotStuck => _ | MaybeStuck => _ end] =>
      destruct s; last done
  end
  ;
  try progress
    match goal with
    | [ H : reducible ?m ?σ |- reducible (bind ?m _) ?σ] =>
        apply (reducible_bind _ _ _ H)
    | [ H : reducible ?m ?σ |- reducible (try ?m _ _) ?σ] =>
        apply (reducible_try _ _ _ _ H)
    | [ H : simp ?m1 ?m2 |- _ ] =>
        epose proof (invert_simp_final _ H) as [|];
        [ prove_final |
          subst; try destruct_is_ret; try destruct_is_throw |
          by apply can_step_reducible ]
    end
  ;
  try (apply can_step_reducible; eauto with step can_step)
.

(* -------------------------------------------------------------------------- *)
(* More [wp] tactics *)

Ltac wp_frame := iFrame; cbn; discharge_emp.

(* [intro_step] introduces [prim_step] along with the new expression and state *)
Ltac intro_step :=
  let Hstep := fresh "Hstep" in
  let efs := fresh "efs" in
  iIntros (???efs Hstep) "H£";
  destruct Hstep as (Hstep&?);
  (* [efs] doesn't keep track of anything for now so it's trivial to substitute *)
  subst efs.

(* The following two tactics correspond to the branch [is_ret _ = None] in
   the definition of [wp]. This branch is a conjunction
     ⌜can_step (σ, m)⌝ ∗ ∀ σ' m', ...
   [construct_wp_nonret] is used when this form appears in the goal.
   [destruct_wp_nonret] is used when it appears in the hypothesis "Hwp". *)

Ltac construct_wp_nonret :=
  (* Prove [can_step]: *)
  (discharge_pure reducible);
  (* Introduce a hypothetical step: *)
  intro_step.

(* -------------------------------------------------------------------------- *)
(* Modality-relevant tactics *)

(* Introduce a mask. *)
Ltac wp_mask_intro Hmod :=
  iApply fupd_mask_intro; [ set_solver | ]; iIntros Hmod.

(* Try to introduce modalities "as much as possible" *)
Ltac try_iModIntro :=
  repeat iModIntro; try iNext; repeat iModIntro.

(* Try to "cleanup" the goal; remove any modalities from the premise that can
   be discharged trivially and then introduce any "straight forward" modalities
  that can be introduced *)
Ltac wp_cleanup_mod :=
  repeat match goal with
    | |- context[environments.Esnoc _
                  ?Hmod (fupd empty empty _)] =>
        iMod Hmod
    end;
  try_iModIntro.

(* Try to eliminate the mask that's currently in context *)
Ltac wp_mask_elim :=
  wp_cleanup_mod;
  match goal with
  | |- environments.envs_entails _ (fupd ?mask1 ?mask2 _) =>
    try match goal with
      | |- context[environments.Esnoc _
                    ?Hmod (fupd mask1 mask2 emp)] =>
          iMod Hmod as "_"
      end
  end;
  wp_cleanup_mod.

(* -------------------------------------------------------------------------- *)
(* WP step tactics *)
(* Try to take a step of [wp] *)

Ltac wp_try_step := try construct_wp_nonret; destruct_step.
Ltac wp_try_final_step := try construct_wp_nonret; simp_final_step_diagram.

Ltac wp_step :=
  try wp_unfold_head; try intro_state;
  wp_mask_intro "Hmod";
  wp_try_step;
  wp_mask_elim;
  try wp_frame.

Ltac wp_final_step_diagram :=
  try wp_unfold_head; try intro_state;
  wp_mask_intro "Hmod";
  wp_try_final_step;
  wp_mask_elim;
  try wp_frame.

(* Try to take a step of [wp] but leave the mask associated with [Hmod] unresolved *)
Tactic Notation "wp_step_mask" constr(Hmod) :=
  try wp_unfold_head; try intro_state;
  wp_mask_intro Hmod; wp_try_step.

(* -------------------------------------------------------------------------- *)
(* Specialize hypothesis that expects a [step] relation and extract out
    information *)
Ltac spec_step :=
  match goal with
    | |- context[environments.Esnoc _ ?Hwp
        (bi_forall (fun _ : micro _ _ =>
            bi_forall (fun _ : store =>
              bi_forall (fun κ : list _ =>
                bi_wand (bi_pure (wp.prim_step ?m ?σ _ _ _ _)) _))))] =>
      match goal with
      | [Hstep : step (σ, m) _ |- _] =>
          to_prim_step Hstep;
          (* Specialize step relation *)
          iSpecialize (Hwp $! _ _ _ Hstep);
          spec_credit Hwp;
          (* Destruct the hypothesis *)
          iMod Hwp;
          tick_wp;
          iMod Hwp as "[SI [Hwp _]]"
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Misc tactics *)

Ltac to_outcome_is_Some Hm :=
  apply to_outcome_is_Some in Hm;
  destruct Hm as [ (?&?&?) | (?&?&?) ]; subst.

End wp_rules_tactics.
