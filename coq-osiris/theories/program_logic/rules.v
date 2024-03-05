Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.semantics Require Import step code.

(* Local tactics for [ewp] rules *)
(* LATER: move to a separate file *)
Module ewp_rules_tactics.

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

(* ------------------------------------------------------------------------ *)

Section wp_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  (* Values *)
  Lemma ewp_value E Ψ Φ v :
    Φ (O2Ret v) -∗ EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_ret_inv E Ψ Φ v :
    EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Ret v).
  Proof. Admitted.

  Lemma ewp_throw E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_throw_inv E Ψ Φ v :
    EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Throw v).
  Proof. Admitted.

  Lemma ewp_crash_inv E Ψ Φ :
    EWP (Crash : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ False.
  Proof. Admitted.

  Lemma ewp_outcome2 E Ψ Φ v :
    Φ v -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.
  Lemma ewp_outcome2_inv E Ψ Φ v :
    EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
  Proof. Admitted.

  Lemma ewp_outcome2_fupd E Ψ Φ v :
    (|={E}=> Φ v) -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

  (* ------------------------------------------------------------------------ *)
  (** Monotonicity. *)
  Lemma ewp_mono E m φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ φ' }}.
  Proof. Admitted.

  (* TODO: Strong monotonicity principle over ordering on protocols *)

  Lemma ewp_pers_smono E E' Ψ Ψ' Φ Φ' m :
    E ⊆ E' →
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E'}=∗ Φ' v) -∗
    EWP m @ E' <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros (HE) "He #HΦ".
  Admitted.

  Corollary ewp_pers_mono E Ψ Φ Φ' m :
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E}=∗ Φ' v) -∗
    EWP m @ E <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros "He #HΦ".
    by iApply (ewp_pers_smono with "He").
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd E m Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => |={E}=> Φ v }} -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (ewp_pers_mono with "He").
    auto.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)
  Lemma ewp_try {B X'} E m (f : A -> micro B X') (h : X -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{| RET v => EWP (f v) @ E <| Ψ |> {{ Φ }};
                        | EXN v => EWP (h v) @ E <| Ψ |> {{ Φ }}}} -∗
    EWP (try m f h) @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

  (** *Bind rule *)
  Lemma ewp_bind {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ RET v, EWP (k v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof. Admitted.

End wp_rules.

(* ------------------------------------------------------------------------ *)
(* Invert cases where there are premises of the form
          [EWP (ret _) _] [EWP crash _] or [EWP (throw _) _] *)
Local Ltac ewp_invert :=
  match goal with
  | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
      match goal with
      (* EWP throw *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
          iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
      (* EWP ret *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
          iMod (ewp_ret_inv with "[$]") as "HΦ"
      (* EWP crash *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ Crash _ _)] =>
          iMod (ewp_crash_inv with "[$]") as "%"
      end
  end.
(* ------------------------------------------------------------------------ *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Implicit Type Ψ : P.
  Import ewp_rules_tactics.

  Notation do v := (stop CPerform v).

  Lemma ewp_do E Ψ v Φ:
    prot_spec Ψ v Φ ⊢ EWP (do v) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP".
    ewp_unfold_head.
    iApply prot_mono; iFrame.
    iIntros (?) "HΦ". iNext.
    by iApply ewp_outcome2.
  Qed.

  Lemma ewp_perform_inv {B X'} E Ψ v Φ (k : _ -> micro B X'):
    EWP (Stop CPerform v k) @ E <| Ψ |> {{ Φ }} -∗
    prot_spec Ψ v (fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }}).
  Proof.
    iIntros "HP".

    ewp_unfold_all.
    iApply prot_mono; iFrame.
    iIntros (?) "HΦ". by iNext.
  Qed.

  Definition shallow_handler E Ψ Φ
    (h : Outcome -> microvx) (* Handler for outcomes *)
    (eh : Eff -> C.continuation -> microvx) (* Effect handler *)
    Ψ' Φ' :=
    ((∀ v, Φ v -∗ ▷ EWP (h v) @ E <| Ψ' |> {{ Φ' }}) ∧
    (∀ v k l, prot_spec Ψ v (fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }}) -∗
       mapsto l (DfracOwn 1) (K k) ==∗
       ▷ EWP (eh v l) @ E <| Ψ' |> {{ Φ' }}))%I.

  Definition handler (h : Outcome -> microvx) (eh : Eff -> C.continuation -> microvx) :
    _ -> microvx :=
    fun x =>
      match x with
        | O3Ret v => h (O2Ret v)
        | O3Throw e => h (O2Throw e)
        | O3Perform e c => eh e c
      end.

  (* Specification for handlers (shallow by default) *)
  Lemma ewp_handler E Ψ Φ Ψ' Φ' e h eh:
    EWP e @ E <| Ψ |> {{ Φ }} -∗
    shallow_handler E Ψ Φ h eh Ψ' Φ' -∗
    EWP (Handle e (handler h eh)) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)
    iLöb as "IH" forall (e h eh).

    iIntros "He Hsh".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      by ewp_mask_intro "Hmod"; ewp_mask_elim.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "[$]") as "HP".
      iSpecialize ("Hsh" $! _ _ with "HP").

      iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH _]]"; first done.
      iSpecialize ("Hsh" with "HH"). iMod "Hsh".

      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iFrame. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)

      (* TODO: Need [ewp_step] *)

  Admitted.

End wp_handler_rules.

