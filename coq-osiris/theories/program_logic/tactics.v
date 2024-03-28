From iris.proofmode Require Import tactics.

From osiris Require Import program_logic.ewp.
From osiris.semantics Require Import step code.

(** *Local tactics for [ewp] rules *)
Module ewp_rules_tactics.

  Ltac ewp_unfold m :=
    setoid_rewrite (ewp_unfold m); rewrite /ewp_pre /=.
  Ltac ewp_unfold_all :=
    rewrite !ewp_unfold /ewp_pre /=.
  (* This tactic unfolds one occurrence of [ewp] at the head of the goal. *)
  Ltac ewp_unfold_head :=
    iApply ewp_unfold; rewrite /ewp_pre /=.

  (* ------------------------------------------------------------------------ *)
  (* Working with the state interpretation invariant. *)

  (* [intro_state] introduces [σ] and [state_interp σ]. *)

  Ltac intro_state := iIntros (σ????) "Hsi".

  (* -------------------------------------------------------------------------- *)
  (** * Modality and mask (fupd) tactics *)

  (* The Iris [wp] has mask-changing updates in order to enforce that during
      a step of computation, no invariants can be opened. In order to control
    the introduction of this mask change, and restore the mask, we provide
    custom tactics analogous to "iModIntro" (here, [wp_mask_intro) and
      "iMod [H]" (here, [wp_mask_elim]) (where [H] corresponds to a premise with
      mask-changing information that restores the previous mask *)

  (* Introduce a mask when there is a goal of shape (fupd E1 E2 _)
      (i.e. The starting goal is of shape ⊢ |={E1, E2}=> P
            and the updated goal is ⊢ P , where (|={E2, E1}=> emp) is introduced
            as a premise)

    The first mask [E1] indicates the set of invariants that can be opened
    currently (i.e. before taking the mask-changing update) and the second mask
    [E2] indicates the set of invariants that can be opened after the mask
    change.

    This tactic (through [fupd_mask_intro]) behaves as an "iModIntro" for
    mask-changing updates and introduce a premise of shape (fupd E1 E2 emp).
    This premise can be used later to restore the mask [E1] *)

  Ltac ewp_mask_intro Hmod :=
    iApply fupd_mask_intro; [ set_solver | ]; iIntros Hmod.

  (* Try to introduce modalities "as much as possible" *)
  Ltac try_iModIntro :=
    repeat iModIntro; try iNext; repeat iModIntro.

  (* Try to "cleanup" the goal; remove any modalities from the premise that can
    be discharged trivially and then introduce any "straight forward" modalities
    that can be introduced *)
  Ltac ewp_cleanup_mod :=
    repeat match goal with
      | |- context[environments.Esnoc _
                    ?Hmod (fupd empty empty _)] =>
          iMod Hmod
      end;
    try_iModIntro.


  Ltac ewp_mask_elim :=
    ewp_cleanup_mod;
    match goal with
    | |- environments.envs_entails _ (fupd ?mask1 ?mask2 _) =>
      try match goal with
        | |- context[environments.Esnoc _ ?Hmod (fupd mask1 mask2 emp)] =>
            iMod Hmod as "_"
        end
    end;
    ewp_cleanup_mod.

  (* ------------------------------------------------------------------------ *)
  (* [intro_step] introduces [prim_step] along with the new expression and state *)
  Ltac intro_step :=
    let Hstep := fresh "Hstep" in
    iIntros (???Hstep).

  (* Discharge pure subgoal that follows immediately by [tac] *)
  Tactic Notation "discharge_pure" tactic(tac) :=
    match goal with
    | |- environments.envs_entails _ (bi_sep (bi_pure _) _) =>
        iSplitL ""; [ iPureIntro; by tac | ]
    | |- environments.envs_entails _ (bi_sep  _ (bi_pure _)) =>
        iSplitL ""; [ | iPureIntro; by tac ]
    end.

  Ltac construct_wp_nonret :=
    (* Prove [can_step]: *)
    (discharge_pure (auto with step can_step));
    (* Introduce a hypothetical step: *)
    intro_step.

  Ltac inv H := inversion H; subst; clear H.

  Ltac destruct_stop_code :=
    match goal with
    | [H: is_handleable (Stop ?c _ _) = Some _ |- _] =>
        destruct c; try done
    end.

  Tactic Notation "ewp_case_is_handleable" constr(x) ident(Hhm) :=
    case_eq (is_handleable x);
    [ intros ? Hhm; destruct x;
      try destruct_stop_code;
      try (inversion Hhm; subst; clear Hhm);
      try solve [by destruct_step] |
      intros Hhm ].

  Tactic Notation "ewp_case_is_handleable" constr(x) :=
    let Hhm := fresh "Hhm" in
    ewp_case_is_handleable x Hhm.


  Ltac spec_state :=
    lazymatch goal with
    | |- context
          [environments.Esnoc _ ?Hwp
             (bi_forall (fun σ1 : store =>
              bi_forall (fun _ : nat =>
              bi_forall (fun κ : list nat =>
              bi_forall (fun _ : list nat =>
              bi_forall (fun _ : nat => bi_wand (osiris_state_interp σ1) _))))))]  =>
        match goal with
        | |- context [environments.Esnoc _ ?SI (osiris_state_interp ?σ)] =>
            let Hstep := fresh "Hstep" in
            iSpecialize (Hwp $! σ 0%nat nil nil 0%nat with SI);
            try (iMod Hwp;
                 iDestruct Hwp as (Hred) Hwp)
        end
    end.

  (* Specialize hypothesis that expects a [step] relation and extract out
    information *)
  Ltac spec_step :=
    match goal with
    | |- context[environments.Esnoc _ ?Hwp
        (bi_forall (fun σ'0 =>
        bi_forall (fun m' =>
        bi_wand (bi_pure (step (pair ?σ ?m) _)) _)))] =>
        match goal with
        | [Hstep : step (σ, m) _ |- _] =>
            (* Specialize step relation *)
            iSpecialize (Hwp $! _ _ Hstep);
            (* Destruct the hypothesis *)
            iMod Hwp
        end
    end.

  (* ------------------------------------------------------------------------ *)

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

  (* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
    of the form [ret a], or it is not. In the second branch, the equality
    [is_ret m = None] appears under the name [Hret]. *)
  (* TODO cleanup *)

  Tactic Notation "wp_case_is_ret" constr(x) ident(Hret) :=
    case_eq (is_ret x);
    [ intros ? Hret;
      try destruct_is_ret |
      intros Hret].

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
      intros Hthrow].

  Tactic Notation "wp_case_is_throw" constr(x) :=
    let Hthrow := fresh "Hthrow" in
    wp_case_is_throw x Hthrow.

End ewp_rules_tactics.
