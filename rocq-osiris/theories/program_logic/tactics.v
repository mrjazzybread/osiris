From iris.proofmode Require Import ltac_tactics.
From osiris.semantics Require Import step code.
From osiris.program_logic Require Import thread_step ewp.

From Ltac2 Require Import Ltac2.

From Ltac2 Require Import Ltac2.

(** *Local tactics for [ewp] rules *)
Module ewp_rules_tactics.

  Ltac ewp_unfold m :=
    rewrite /impure;
    setoid_rewrite (ewp_unfold m); rewrite /ewp_pre /=.
  Ltac ewp_unfold_all :=
    rewrite /impure !ewp_unfold /ewp_pre /=.
  (* This tactic unfolds one occurrence of [ewp] at the head of the goal. *)
  Ltac ewp_unfold_head :=
    iApply ewp_unfold; rewrite /ewp_pre /=.

  (* ------------------------------------------------------------------------ *)
  (* Working with the state interpretation invariant. *)

  (* [intro_state] introduces [σ], [π] and [state_interp (σ, π)]. *)

  Ltac intro_state := iIntros (σ π) "(Hsi & Hti)".

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
  (* [intro_step] introduces [wp_step] along with the new expression and state *)
  Ltac intro_step :=
    let Hstep := fresh "Hstep" in
    iIntros (??? Hstep).

  (* Discharge pure subgoal that follows immediately by [tac] *)
  Tactic Notation "discharge_pure" tactic(tac) :=
    lazymatch goal with
    | |- environments.envs_entails _ (bi_sep (bi_pure _) _) =>
        iSplitL ""; [ iPureIntro; by tac | ]
    | |- environments.envs_entails _ (bi_sep  _ (bi_pure _)) =>
        iSplitL ""; [ | iPureIntro; by tac ]
    end.

  Ltac prove_can_progress :=
    unfold stop;
    (eauto with step can_progress) ||
    (apply can_step_can_progress; auto with step can_step).

  Ltac construct_wp_nonret :=
    (* Prove [can_step]: *)
    (discharge_pure prove_can_progress);
    (* Introduce a hypothetical step: *)
    intro_step.

  Ltac2 destruct_stop_code () :=
    match! goal with
    | [ _ : is_ewp_case (Stop ?c _ _) = _ |- _] =>
        destruct $c;
        Control.enter
          (fun _ =>
             try (match! goal with
                  | [ x: val * val |- _] =>
                      let x_hyp := Control.hyp x in
                      destruct $x_hyp as [??]
                  end);
             try ltac1:(done))
    end.

  Ltac2 rec intros_until_ewp_case (hm : ident) :=
    match! goal with
    | [ |- is_ewp_case _ = _ -> _ ] =>
        intros $hm
    | [ |- _ ] =>
        intros ?; intros_until_ewp_case hm
    end.

  Ltac2 destruct_thread_step () := ltac1:(destruct_thread_step).

  Ltac2 ewp_case (m : constr)  :=
    ltac1:(m |- case_eq (is_ewp_case m)) (Ltac1.of_constr m);
    Control.extend []
      (fun _ =>
         let hm := Fresh.in_goal @Hhm in
         intros_until_ewp_case hm;
         Control.enter
           (fun _ =>
              lazy_match! goal with
              | [ _ : is_ewp_case _ = WPStep |- _ ] => ()
              | [ h : is_ewp_case ?m = WPOutcome ?o |- _ ] =>
                  (* If the [m] we matched against is a var, substitute it. *)
                  (match Constr.Unsafe.kind m with
                  | Constr.Unsafe.Var id =>
                      apply inv_is_ewp_case_outcome in $h;
                      subst $id
                   | _ => ()
                  end);
                  try (complete (fun () =>
                                   destruct $o;
                                   try discriminate;
                                   Control.enter destruct_thread_step))
              | [ |- _ ] =>
                  destruct $m; try0 destruct_stop_code; try discriminate;
                  Control.enter
                    (fun _ =>
                       try (complete destruct_thread_step))
              end))
      [ ].

  Tactic Notation "ewp_case" constr(x)  :=
    let f := ltac2:(x |- ewp_case (Option.get (Ltac1.to_constr x))) in
    f x.

  Lemma combine_seps {PROP : bi} (P Q : PROP) :
    P -∗ Q -∗ P ∗ Q.
  Proof.
    ltac1:(iStartProof; iIntros "HP HQ"; iFrame).
  Qed.

  Lemma combine_pure_sep {PROP : bi} (P : Prop) (Q : PROP) :
    ⌜P⌝ -∗ Q -∗ ⌜P⌝ ∗ Q.
  Proof. apply combine_seps. Qed.

  Ltac spec_state :=
    lazymatch goal with
    | |- context
          [environments.Esnoc _ ?Hwp
             (bi_forall (fun σ1 : step.store =>
              bi_forall (fun π1 : post_map _ => _)))] =>
        lazymatch goal with
        (* When both state interps are in the same hypothesis. *)
        | |- context [environments.Esnoc _ ?SI (bi_sep (osiris_state_interp ?σ) (osiris_thread_interp ?π))] =>
            let Hstep := fresh "Hstep" in
            iSpecialize (Hwp $! σ π with SI);
            try (iMod Hwp;
                 iDestruct Hwp as (Hstep) Hwp)
        (* When the state interps are in two different hypotheses *)
        | |- context [environments.Esnoc _ ?SI (osiris_state_interp ?σ)] =>
            lazymatch goal with
            | |- context [environments.Esnoc _ ?TI (osiris_thread_interp ?π)] =>
                let Hstep := fresh "Hstep" in
                iPoseProof (combine_seps with SI) as SI;
                iSpecialize (SI with TI);
                iSpecialize (Hwp $! σ π with SI);
                try (iMod Hwp;
                     iDestruct Hwp as (Hstep) Hwp)
            | |- _ => fail "Cannot find thread interp hypothesis"
            end
        | |- _ => fail "Cannot find state interp hypothesis"
        end
    end.

  (* Specialize hypothesis that expects a [step] relation and extract out
    information *)
  Ltac spec_step :=
    lazymatch goal with
    | |- context
          [environments.Esnoc _ ?Hwp
             (bi_forall (fun σ'0 =>
              bi_forall (fun m' =>
              bi_forall (fun μ0 =>
              bi_wand (bi_pure ((thread_step (pair (pair ?σ _) _) _))) _))))] =>
        lazymatch goal with
        | [ Hstep : thread_step (σ, _, _) _ |- _] =>
            (* Specialize step relation *)
            iSpecialize (Hwp $! _ _ _ Hstep);
            (* Destruct the hypothesis *)
            iMod Hwp
        | |- _ => fail "Could not find stepping hypothesis"
        end
    | |- _ => fail "Could not find hypothesis to specialize"
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
