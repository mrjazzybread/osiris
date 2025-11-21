From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import wp_step ewp tactics basic_rules stop_rules.
From osiris.semantics Require Import code.

From osiris.program_logic.pure Require Import pure.

From Coq Require Import FunctionalExtensionality.

(* -------------------------------------------------------------------------- *)
(** *Shallow and deep handlers *)

(* Shallow handlers are use-once handlers;
    If the handled expression performs an effect caught by the handler,
    we are done (and the handlers are not installed).
    If not, the handler is installed around the captured continuation. *)

Definition shallow_handler η e bs :=
  Handle (eval η e) (shallow_eval_branches η bs bs).

(* Deep handlers are installed permanently;
   Regardless of whether the handled expression performs an effect
   caught by the handler, the handler is installed around the captured
   continuation. *)

Definition deep_handler η e bs :=
  Handle (eval η e) (wrap_eval_branches η bs).

(* -------------------------------------------------------------------------- *)
(** *Reasoning about effect handlers *)

(* Definition of handler specifications *)
Section handler_specifications.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  (* -------------------------------------------------------------------------- *)
  (** * Shallow handler specification. *)
  (* The shallow handler specification is defined over the [Handle] primitive in
   [basic_rules.v] *)
  (* -------------------------------------------------------------------------- *)

  (* -------------------------------------------------------------------------- *)
  (** * Deep handler specification. *)
  (* We follow the deep handler judgment in [hazel] (the one-shot case),
      which reflects the recursive behavior of deep handlers. *)

  Definition deep_handler_spec_pre
    (deep_handler_spec:
      coPset -d>
      thread -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ) :
      coPset -d>
      thread -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ :=
    (λ E ι Ψ Φ h Ψ' Φ',
      ((* [Return] and [Exception] branch *)
      (∀ o, Φ o -∗ ▷ EWP (h o) @ E <| (ι, Ψ') |> {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' Φ'',
            ▷ deep_handler_spec E ι Ψ Φ h Ψ'' Φ'' -∗
            EWP (stop CResume (k, o)) @ E <| (ι, Ψ'') |> {{ Φ'' }} >> -∗
        ▷ EWP (h (O3Perform v k)) @ E <| (ι, Ψ') |> {{ Φ' }})))%I.

  (* Some definition sealing (and auxilliary functions) *)
  Local Instance deep_handler_spec_pre_contractive: Contractive deep_handler_spec_pre.
  Proof.
    rewrite /deep_handler_spec_pre /= => n wp wp' Hwp E m Φ.
    repeat intro. repeat (f_contractive || f_equiv).
    repeat intro. repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  Local Definition deep_handler_spec_def := fixpoint deep_handler_spec_pre.

  Local Definition deep_handler_spec_aux : seal (@deep_handler_spec_def).
  Proof. by eexists. Qed.
  (* Top-level definition for [deep_handler] *)
  Definition deep_handler_spec := deep_handler_spec_aux.(unseal).

  Lemma deep_handler_spec_unfold {E} ι Ψ Φ Ψ' Φ' h :
    deep_handler_spec E ι Ψ Φ h Ψ' Φ' ⊣⊢
    deep_handler_spec_pre deep_handler_spec_def E ι Ψ Φ h Ψ' Φ'.
  Proof.
    rewrite /deep_handler_spec seal_eq /deep_handler_spec_def;
    apply (@fixpoint_unfold _ _ _ deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_mono E ι Ψ φ h ψ' φ1 φ2 :
    (∀ o, φ1 o -∗ φ2 o) -∗
    deep_handler_spec E ι Ψ φ h ψ' φ1 -∗
    deep_handler_spec E ι Ψ φ h ψ' φ2.
  Proof.
    rewrite !deep_handler_spec_unfold /deep_handler_spec_pre.
    iIntros "Hcov Hhandler".
    iSplit.
    { iIntros (o) "Hφ".
      iDestruct "Hhandler" as "[Hhandler _]".
      iSpecialize ("Hhandler" $! o with "Hφ").
      iModIntro.
      iApply (ewp_mono with "Hhandler Hcov"). }

    { iIntros (v k) "HProt".
      iDestruct "Hhandler" as "[_ Hhandler]".
      iSpecialize ("Hhandler" $! v k with "HProt").
      iModIntro.
      iApply (ewp_mono with "Hhandler Hcov"). }
  Qed.

End handler_specifications.

Ltac deep_handler_spec_unfold :=
  rewrite deep_handler_spec_unfold /deep_handler_spec_pre /=.

(* LATER: refactor *)
Local Ltac ewp_invert :=
  match goal with
  (* EWP throw *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
      iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
  (* EWP ret *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
      iPoseProof (ewp_ret_inv with "[$]") as "HΦ"
  (* EWP crash *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (Crash _) _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "HΦ"
  end.

(* -------------------------------------------------------------------------- *)
(** *Reasoning rules over effect handlers *)

Section handler_proof.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  Import ewp_rules_tactics.

  (* Specification of [shallow_handler] at the [expr] level. *)
  Corollary ewp_shallow_handler E ι Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| (ι, Ψ) |> {{ Φ }} -∗
    (* The shallow handler specification is met *)
    shallow_handler_spec E ι Ψ Φ (shallow_eval_branches η bs bs) Ψ' Φ' -∗
    EWP (shallow_handler η e bs) @ E <| (ι, Ψ') |> {{ Φ' }}.
  Proof.
    iIntros "He Hspec".
    rewrite /shallow_handler.
    (* Follows immediately by the reasoning rule on [Handle]. *)
    by iApply (ewp_handle with "He").
  Qed.

  (* Specification of [deep_handler] at the [expr] level. *)
  Lemma ewp_deep_handler E ι Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| (ι, Ψ) |> {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E ι Ψ Φ (λ o, eval_branches η o bs) Ψ' Φ' -∗
    EWP (deep_handler η e bs) @ E <| (ι, Ψ') |> {{ Φ' }}.
  Proof.
    (* We abstract away [eval η e]. *)
    rewrite /deep_handler; remember (eval η e); clear.

    (* We proceed by Löb-induction after generalizing [η] [m] and [bs]. *)
    iLöb as "IH" forall (m η bs Ψ' Φ' E).

    (* Expand the definition of [EWP] to inspect the possible steps that
        can result from [deep_handler η e bs]. *)
    iIntros "He Hsh"; ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".

    (* Case analysis on the steps from [deep_handler η e bs]. *)
    construct_wp_nonret; destruct_wp_step;
      iMod "Hmod" as "_"; try rewrite -x.


    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      simpl_wrap_eval_branches;
      ewp_invert; iFrame;
      deep_handler_spec_unfold;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      iMod "Hsh"; ewp_mask_intro "Hmod"; ewp_mask_elim; done.

    { (* [StepHandlePerform] *)
      deep_handler_spec_unfold.
      iDestruct "Hsh" as "[_ Hsh]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi")
        as ">[Hsi [HH _]]"; [ exact H | ].

      iFrame.
      (* Install the handler around the location [l]. *)
      simpl_wrap_eval_branches; iApply ewp_wrap_deep.
      ewp_mask_intro "Hmod".
      ewp_mask_elim.
      iIntros (?) "Hl".
      iSpecialize ("Hsh" $! e l').

      iSpecialize ("Hsh" with "[HP HH Hl]").
      { rewrite /prot.
        iApply (monotonic_prot with "[HH Hl] HP").
        iIntros (?) "Hk"; iIntros (??) "H".
        rewrite /deep_handler_spec seal_eq.

        iPoseProof (ewp_resume E l' w (λ o : outcome2 val exn,
                          Handle (stop CResume (l, o)) (wrap_eval_branches η bs)) inject2 Φ'' (ι, Ψ'') with "Hl") as "Hl".
        unfold cont; simpl.
        iApply "Hl".
        iSpecialize ("IH" with "Hk H").
        iPoseProof (ewp_handle_inv with "HH IH") as "Hhandle".
        iIntros "H".
        iNext.
        replace
          (@Handle val exn
          (@stop (prod loc (outcome2 val exn)) val exn CResume
             (@pair C.continuation (outcome2 val exn) l w))
          (fun o : outcome.outcome3 C.eff C.continuation C.val C.exn =>
           @try2 val val exn exn (wrap_eval_branches η bs o) (@inject2 val exn)))
          with
          ((Handle (stop CResume (pair l w))
          (fun o : outcome.outcome3 C.eff C.continuation C.val C.exn =>
             wrap_eval_branches η bs o))).
        by simpl_wrap_eval_branches.
        f_equal. extensionality o. rewrite try2_inject2_right. done. }

      done. }

    { (* [StepHandleFork] *)
      ewp_mask_intro "Hmod".
      iModIntro. ewp_mask_elim. iFrame. destruct x.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_wp_step.
      epose proof (ForkS _ _ _ _ _ _ _ H) as Hstep0.
      iSpecialize ("He" $! _ _ _ _ Hstep0).
      ewp_mask_elim. iMod "He" as "($ & He & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleJoin] *)
      ewp_mask_intro "Hmod". iModIntro. ewp_mask_elim. iFrame.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_wp_step.
      epose proof (JoinS _ _ _ _ _ _ H) as Hstep0.
      iSpecialize ("He" $! _ _ _ _ Hstep0).
      ewp_mask_elim. iMod "He" as "($ & He & _)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleSelf] *)
      ewp_mask_intro "Hmod". iModIntro. ewp_mask_elim. iFrame.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_wp_step.
      epose proof (SelfS _ _ _ _ _) as Hstep0.
      iSpecialize ("He" $! _ _ _ _ Hstep0).
      ewp_mask_elim. iMod "He" as "($ & He & _)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "He Hsh"). }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ _ _ Hstep with "Hsi He") as ">H".
      iMod "H". ewp_mask_elim. iMod "H" as "($ & H & _)". iModIntro.
      iSpecialize ("IH" with "H").
      iApply ("IH" with "Hsh"). }
  Qed.

  Lemma deep_handle_nil_ret η v E ψ Φ :
   EWP match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP (eval_branches η (O3Ret v) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_eval_branches.
  Qed.

  Lemma shallow_handle_nil_ret η v all_bs E ψ Φ :
   EWP match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP (shallow_eval_branches η [] all_bs (O3Ret v)) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_throw η e E ψ Φ :
   EWP throw e @ E <|ψ|> {{ Φ }} -∗
   EWP (eval_branches η (O3Throw e) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_eval_branches.
  Qed.

  Lemma shallow_handle_nil_throw η all_bs e E ψ Φ :
    EWP throw e @ E <|ψ|> {{ Φ }} -∗
    EWP (shallow_eval_branches η [] all_bs (O3Throw e)) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_perform η eff k ι Ψ sk Φ :
    isCont k sk -∗
    Ψ allows perform eff
    << λ o,
      (isShot k -∗ ▷ EWP (sk o) <| (ι, Ψ) |> {{ Φ }}) >> -∗
    EWP (eval_branches η (O3Perform eff k) []) <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "Hl Hperf".
    simpl_eval_branches. iApply ewp_stop_perform.
    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS Ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iModIntro.
      rewrite try2_inject2.
      iApply "Hcov". rewrite try2_inject2_right. iApply "H". }
    done.
  Qed.

  Lemma shallow_handle_nil_perform η eff k all_branches ι Ψ sk Φ :
    isCont k sk -∗
    Ψ allows perform eff
    << λ o,
      ▷ EWP Handle (sk o) (shallow_eval_branches η all_branches all_branches) <| (ι, Ψ) |> {{ Φ }} >> -∗
    EWP (shallow_eval_branches η [] all_branches (O3Perform eff k)) <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "Hk Hperf". simpl_shallow_eval_branches.
    iApply ewp_wrap_shallow.

    iIntros (l) "Hl". iNext. cbn.

    iApply ewp_stop_perform.

    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS Ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iNext. rewrite try2_inject2. iApply "Hcov". rewrite try2_inject2_right.
      iIntros "_".
      iApply (bi.later_mono with "H").
      iIntros "H".
      unfold stop.
      iApply "H". }
    iApply (monotonic_prot (Ψ:=upcl OS Ψ) with "[Hk]").
    { iIntros (o) "H".
      iPoseProof (ewp_handle_inv with "Hk") as "Hcov".
      unfold cont; simpl.
      iApply "Hcov". iApply "H". }
    done.
  Qed.

  Lemma deep_handle_cons η o cp e bs E ι Ψ Φ Q φ :
    Q -∗
    ⌜cpattern η η cp o (λ δ, Q ⊢ EWP (eval δ e) @ E <| (ι, Ψ) |> {{ Φ }}) φ⌝ -∗
    (Q -∗ ⌜φ⌝ -∗ EWP (eval_branches η o bs) @ E <| (ι, Ψ) |> {{ Φ }}) -∗
    EWP (eval_branches η o (Branch cp e :: bs)) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    simpl_eval_branches.
    iIntros "Q %Hpure Hmono".
    iApply ewp_try.
    iApply ewp_mono; first by iApply pure_ewp.
    iIntros ([|[]]); simpl.
    - iIntros "%HmonQ". iApply (HmonQ with "Q").
    - iApply ("Hmono" with "Q").
  Qed.

  Lemma deep_handle_cons_no_resources η o cp e bs E ι Ψ Φ φ :
    ⌜cpattern η η cp o (λ δ, ⊢ EWP (eval δ e) @ E <| (ι, Ψ) |> {{ Φ }}) φ⌝ -∗
    (⌜φ⌝ -∗ EWP (eval_branches η o bs) @ E <| (ι, Ψ) |> {{ Φ }}) -∗
    EWP (eval_branches η o (Branch cp e :: bs)) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    simpl_eval_branches.
    iIntros "%Hpure Hmono".
    iApply ewp_try.
    iApply ewp_mono; first iApply pure_ewp; try done.
    iIntros ([|[]]); simpl.
    - iIntros "%Heval"; iApply Heval.
    - iApply "Hmono".
  Qed.

  Lemma deep_handle_cons_skip η o cp e bs E ι Ψ Φ :
    valid_cpattern_match cp o = false ->
    EWP (eval_branches η o bs) @ E <| (ι, Ψ) |> {{ Φ }} -∗
    EWP (eval_branches η o (Branch cp e :: bs)) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros (Hvalid) "Hmatch".
    iAssert (bi_pure True) as "Htrue". done.
    iApply deep_handle_cons_no_resources.
    { iPureIntro. unfold cpattern.
      rewrite invert_valid_match; [ | assumption ].
      constructor. apply I. }
    { iIntros "_". iApply "Hmatch". }
  Qed.

End handler_proof.
