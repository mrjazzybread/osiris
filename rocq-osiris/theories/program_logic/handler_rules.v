From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import thread_step ewp tactics basic_rules stop_rules.
From osiris.semantics Require Import code.

From osiris.program_logic.pure Require Import pure.

From Stdlib Require Import FunctionalExtensionality.

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
      (∀ o, Φ o -∗ ▷ EWP[ι] (h o) @ E <| Ψ' |> {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' Φ'',
            ▷ deep_handler_spec E ι Ψ Φ h Ψ'' Φ'' -∗
            EWP[ι] (stop CResume (k, o)) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
        ▷ EWP[ι] (h (O3Perform v k)) @ E <| Ψ' |> {{ Φ' }})))%I.

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

  Lemma deep_handler_spec_unfold {ι E} Ψ Φ Ψ' Φ' h :
    deep_handler_spec ι E Ψ Φ h Ψ' Φ' ⊣⊢
    (deep_handler_spec_pre deep_handler_spec_def ι E Ψ Φ h Ψ' Φ').
  Proof.
    rewrite /deep_handler_spec seal_eq /deep_handler_spec_def.
    apply (@fixpoint_unfold _ _ _ _ deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_def_unfold {E} ι Ψ Φ Ψ' Φ' h :
    deep_handler_spec_def E ι Ψ Φ h Ψ' Φ' ≡
    ((∀ o, Φ o -∗ ▷ EWP[ι] (h o) @ E <| Ψ' |> {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' Φ'',
            ▷ deep_handler_spec_def E ι Ψ Φ h Ψ'' Φ'' -∗
            EWP[ι] (stop CResume (k, o)) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
        ▷ EWP[ι] (h (O3Perform v k)) @ E <| Ψ' |> {{ Φ' }}))%I.
  Proof.
    rewrite /deep_handler_spec_def.
    apply (fixpoint_unfold deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_mono ι E Ψ φ h ψ' φ1 φ2 :
    (∀ o, φ1 o -∗ φ2 o) -∗
    deep_handler_spec ι E Ψ φ h ψ' φ1 -∗
    deep_handler_spec ι E Ψ φ h ψ' φ2.
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

  Lemma prove_deep_handler_spec ι E Ψ (φ : outcome2 val exn → iProp Σ) (h : outcome3 val exn → microvx) Ψ' φ' :
    ((∀ o, φ o -∗ ▷ EWP[ι] h o @ E <| Ψ' |> {{ φ' }}) ∧
      (∀ (v : val) (k : cont),
      Ψ allows perform v << λ o : outcome2 val exn,
        ∀ (Ψ'' : iEff Σ) (Φ'' : outcome2 val exn -d> iPropO Σ),
          ▷ deep_handler_spec_def E ι Ψ φ h Ψ'' Φ'' -∗
          EWP[ι] stop CResume (k, o) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
      ▷ EWP[ι] h (O3Perform v k) @ E <| Ψ' |> {{ φ' }})) -∗
   deep_handler_spec E ι Ψ φ h Ψ' φ'.
  Proof.
    rewrite deep_handler_spec_unfold /deep_handler_spec_pre /=.
    iIntros "$".
  Qed.

  Lemma inv_deep_handler_spec E ι Ψ φ h Ψ' φ' :
    deep_handler_spec E ι Ψ φ h Ψ' φ' -∗
    (∀ o, φ o -∗ ▷ EWP[ι] h o @ E <| Ψ' |> {{ φ' }}) ∧
    (∀ (v : val) (k : cont),
      Ψ allows perform v << λ o : outcome2 val exn,
        ∀ (Ψ'' : iEff Σ) (Φ'' : outcome2 val exn -d> iPropO Σ),
          ▷ deep_handler_spec_def E ι Ψ φ h Ψ'' Φ'' -∗
          EWP[ι] stop CResume (k, o) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
      ▷ EWP[ι] h (O3Perform v k) @ E <| Ψ' |> {{ φ' }}).
  Proof.
    iIntros "Hdh".
    by rewrite deep_handler_spec_unfold /deep_handler_spec_pre /=.
  Qed.

End handler_specifications.

Ltac deep_handler_spec_unfold :=
  rewrite deep_handler_spec_unfold /deep_handler_spec_pre /=.

(* -------------------------------------------------------------------------- *)
(** *Reasoning rules over effect handlers *)

Section handler_proof.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  Import ewp_rules_tactics.

  (* Specification of [shallow_handler] at the [expr] level. *)
  Corollary ewp_shallow_handler E Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The shallow handler specification is met *)
    shallow_handler_spec E Ψ Φ (shallow_eval_branches η bs bs) Ψ' Φ' -∗
    EWP (shallow_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros "He Hspec".
    rewrite /shallow_handler.
    (* Follows immediately by the reasoning rule on [Handle]. *)
    by iApply (ewp_handle with "He").
  Qed.

  (* Specification of [deep_handler] at the [expr] level. *)
  Lemma ewp_deep_handler ι E Ψ Φ Ψ' Φ' η e bs:
    EWP[ι] (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E ι Ψ Φ (λ o, eval_branches η o bs) Ψ' Φ' -∗
    EWP[ι] (deep_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We abstract away [eval η e]. *)
    rewrite /deep_handler; remember (eval η e); clear.

    iIntros "Hwp Hdh".

    deep_handler_spec_unfold.
    (* We proceed by Löb-induction after generalizing [η] [m] and [bs]. *)
    iLöb as "IH" forall (m η bs Ψ' Φ' E).

    (* Expand the definition of [EWP] to inspect the possible steps that
        can result from [deep_handler η e bs]. *)
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".

    (* Case analysis on the steps from [deep_handler η e bs]. *)
    rename π into π'.
    construct_wp_nonret; destruct_thread_step;
      iMod "Hmod" as "_"; try rewrite -x.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      simpl_wrap_eval_branches;
      ewp_invert; iFrame;
      iDestruct "Hdh" as "[Hdh _]";
      iSpecialize ("Hdh" with "HΦ");
      iMod "Hdh"; ewp_mask_intro "Hmod"; ewp_mask_elim; done.

    { (* [StepHandlePerform] *)
      iDestruct "Hdh" as "[_ Hdh]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi")
        as ">[Hsi [HH _]]"; [ exact H | ].

      iFrame.
      (* Install the handler around the location [l]. *)
      simpl_wrap_eval_branches.
      ewp_mask_intro "Hmod".
      ewp_mask_elim.
      iApply ewp_wrap_deep.
      iIntros (?) "Hl".
      iSpecialize ("Hdh" $! e l').

      iSpecialize ("Hdh" with "[HP HH Hl]").
      { iApply (monotonic_prot with "[HH Hl] HP").
        iIntros (?) "Hk"; iIntros (??) "H".

        iPoseProof (ewp_resume ι E l' w (λ o : outcome2 val exn,
                          Handle (stop CResume (l, o)) (wrap_eval_branches η bs)) inject2 Φ'' Ψ'' with "Hl") as "Hl".
        simpl.
        iApply "Hl". iIntros "Hshot !>".
        rewrite deep_handler_spec_def_unfold.
        iSpecialize ("IH" with "Hk H").
        iPoseProof (ewp_handle_inv with "HH IH") as "Hhandle".
        replace
          (Handle (stop CResume (l, w)) (pftry2 (wrap_eval_branches η bs) inject2))
          with
          (Handle (stop CResume (l, w)) (wrap_eval_branches η bs));
          last first.
        { f_equal. extensionality o. by rewrite try2_inject2_right. }
        simpl_wrap_eval_branches.
        iApply "Hhandle". }
      iApply "Hdh". }

    { (* [StepHandleFork] *)
      ewp_mask_intro "Hmod".
      iModIntro. ewp_mask_elim. iFrame. destruct x.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_thread_step.
      epose proof (ForkS _ _ _ _ _ _ _ H) as Hstep0.
      iSpecialize ("Hwp" $! _ _ _ Hstep0).
      ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "Hwp Hdh"). }

    { (* [StepHandleJoin] *)
      ewp_mask_intro "Hmod". iModIntro. ewp_mask_elim. iFrame.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iMod "Hwp".
      destruct (π !! ι0); last done.
      iDestruct "Hwp" as "(%φ' & $ & Hwp)".
      iIntros "!> !> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "Hwp Hdh"). }

    { (* [StepHandleSelf] *)
      ewp_mask_intro "Hmod". iModIntro. ewp_mask_elim. iFrame.
      rewrite ewp_unfold /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_thread_step.
      epose proof (SelfS _ _ _ _ _) as Hstep0.
      iSpecialize ("Hwp" $! _ _ _ Hstep0).
      ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "Hwp Hdh"). }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ _ _ Hstep with "Hsi Hwp") as ">Hwp".
      iMod "Hwp". ewp_mask_elim. iMod "Hwp" as "(Hwp & $)". iModIntro.
      iApply ("IH" with "Hwp Hdh"). }
  Qed.

  Lemma deep_handle_nil_ret ι η v E ψ Φ :
   EWP[ι] match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP[ι] (eval_branches η (O3Ret v) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_eval_branches.
  Qed.

  Lemma shallow_handle_nil_ret ι η v all_bs E ψ Φ :
   EWP[ι] match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP[ι] (shallow_eval_branches η [] all_bs (O3Ret v)) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_throw ι η e E ψ Φ :
   EWP[ι] throw e @ E <|ψ|> {{ Φ }} -∗
   EWP[ι] (eval_branches η (O3Throw e) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_eval_branches.
  Qed.

  Lemma shallow_handle_nil_throw ι η all_bs e E ψ Φ :
    EWP[ι] throw e @ E <|ψ|> {{ Φ }} -∗
    EWP[ι] (shallow_eval_branches η [] all_bs (O3Throw e)) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_perform η eff k ι Ψ sk Φ :
    isCont k sk -∗
    Ψ allows perform eff
    << λ o,
      (isShot k -∗ ▷ EWP[ι] (sk o) <| Ψ |> {{ Φ }}) >> -∗
    EWP[ι] (eval_branches η (O3Perform eff k) []) <| Ψ |> {{ Φ }}.
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
      ▷ EWP[ι] Handle (sk o) (shallow_eval_branches η all_branches all_branches) <| Ψ |> {{ Φ }} >> -∗
    EWP[ι] (shallow_eval_branches η [] all_branches (O3Perform eff k)) <| Ψ |> {{ Φ }}.
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

  Lemma deep_handle_cons ι η o cp e bs E Ψ Φ Hη φ :
    ⌜cpattern η η cp o Hη φ⌝ -∗
    (∀ η, ⌜Hη η⌝ -∗ EWP[ι] (eval η e) @ E <| Ψ |> {{ Φ }}) ∧
    (⌜φ⌝ -∗ EWP[ι] (eval_branches η o bs) @ E <| Ψ |> {{ Φ }}) -∗
    EWP[ι] (eval_branches η o (Branch cp e :: bs)) @ E <| Ψ |> {{ Φ }}.
  Proof.
    simpl_eval_branches.
    iIntros "%Hpat Hmono".
    iApply ewp_try.
    iApply ewp_mono; first by iApply pure_ewp.
    iIntros ([|[]]); simpl.
    - iDestruct "Hmono" as "[Hmono _]".
      iApply ("Hmono" $! _).
    - iDestruct "Hmono" as "[_ $]".
  Qed.

  Lemma deep_handle_cons_skip ι η o cp e bs E Ψ Φ :
    valid_cpattern_match cp o = false ->
    EWP[ι] (eval_branches η o bs) @ E <| Ψ |> {{ Φ }} -∗
    EWP[ι] (eval_branches η o (Branch cp e :: bs)) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hvalid) "Hmatch".
    iApply deep_handle_cons.
    { iPureIntro. unfold cpattern.
      rewrite invert_valid_match; [ | assumption ].
      instantiate (1 := True); instantiate (1 := λ _, False).
      constructor. apply I. }
    iSplit.
    - iIntros (?) "[]".
    - iIntros (_). iApply "Hmatch".
  Qed.

End handler_proof.
