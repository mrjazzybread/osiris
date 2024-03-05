From iris.proofmode Require Import tactics.

From osiris Require Import program_logic.ewp.
From osiris.semantics Require Import step code.

(* Local tactics for [ewp] rules *)
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

  Ltac intro_state := iIntros (σ) "Hsi".

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

End ewp_rules_tactics.
