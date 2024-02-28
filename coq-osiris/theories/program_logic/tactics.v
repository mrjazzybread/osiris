From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.

From osiris Require Import semantics.
From osiris Require Import program_logic.wp.


(* WP tactics that is used in [rules.v]. *)

Module wp_rules_tactics.

(* -------------------------------------------------------------------------- *)

(* Tactics relevant to [step] relation *)

(* Juice out more information of goals of form [step (σ, bind _ _) _] *)
Tactic Notation "step_bind" hyp(Hstep) :=
  match type of Hstep with
  | step (?σ, bind ?m ?k) _ =>
      match goal  with
        [ H' : reducible m σ |- _ ] =>
          apply reducible_not_val in H';
          let m' := fresh "m'" in
          let Hstep' := fresh "Hstep'" in
          destruct (invert_step_bind Hstep) as (m' & Hstep' & ->);
          [ by apply to_outcome_is_not_ret | ]
      end
  end.

(* Juice out more information of goals of form [step (σ, try _ _ _) _] *)
Tactic Notation "step_try" hyp(Hstep) :=
  match type of Hstep with
  | step (?σ, try ?m ?k ?h) _ =>
      match goal  with
        [ H' : reducible m σ |- _ ] =>
          let Hred := fresh "Hred" in
          assert (Hred := H');
          apply reducible_not_val in H';
          (* destruct Hstep as (Hstep & ?); subst *)
          let m' := fresh "m'" in
          let Hstep' := fresh "Hstep'" in
          destruct (invert_step_try Hstep) as (m' & Hstep' & ->);
          [ by apply can_step_reducible | ];
          clear Hred
      end
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
      try_and_revert
        (rewrite !(wp_unfold s E e Φ))
        (rewrite /wp_pre /=; iMod H)
        (rewrite <- (wp_unfold s E e Φ))
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

(* Conclude that any computation is reducible by information in the context *)
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
  match goal with
  | [ H : reducible ?m ?σ |- reducible (bind ?m _) ?σ] =>
      apply (reducible_bind _ _ _ H)
  | [ H : reducible ?m ?σ |- reducible (try ?m _ _) ?σ] =>
      apply (reducible_try _ _ _ _ H)
  | |- reducible _ _ =>
      apply can_step_reducible; eauto with step can_step
  end.

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

(* TODO comment *)
Ltac wp_intro_mask Hmod :=
  match goal with
  | |- environments.envs_entails _ (fupd ?mask _ _) =>
      iMod (@fupd_mask_subseteq _ _ mask ∅) as "Hmod";
      first set_solver;
      iModIntro;
      construct_wp_nonret
  end.

(* Take care of the modality of the goal if Hmod is a result of [fupd_mask_subseteq]
      TODO: see if this is necessary *)
Ltac wp_resolve_mask Hmod :=
  iMod Hmod as "_";
  iMod (@fupd_mask_subseteq _ _ _ ∅) as Hmod;
  [ set_solver | iModIntro ];
  do 2 iModIntro;
  iMod Hmod; iModIntro;
  (* Also does the framing *)
  wp_frame.

Ltac masked_step :=
  wp_intro_mask "Hmod";
  destruct_step;
  wp_resolve_mask "Hmod".

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
