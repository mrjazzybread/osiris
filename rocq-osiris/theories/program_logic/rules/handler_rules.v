From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import thread_step ewp tactics.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
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

  Context {A A' B X : Type} `{Encode A, Encode A', Encode B}.

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
      iEff Σ -d>
      (exn -d> iPropO Σ) -d>
      (A -d> iPropO Σ) -d>
      env -d>
      list branch -d>
      iEff Σ -d>
      (exn -d> iPropO Σ) -d>
      (A' -d> iPropO Σ) -d>
      iPropI Σ) :
      coPset -d>
      iEff Σ -d>
      (exn -d> iPropO Σ) -d>
      (A -d> iPropO Σ) -d>
      env -d>
      list branch -d>
      iEff Σ -d>
      (exn -d> iPropO Σ) -d>
      (A' -d> iPropO Σ) -d>
      iPropI Σ :=
    (λ E Ψ ζ Φ η bs Ψ' ζ' Φ',
      ((* [Return] and [Exception] branch *)
      (∀ a, Φ a -∗ ▷ imp (eval_branches η (O3Ret #a) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
      (∀ e, ζ e -∗ ▷ imp (eval_branches η (O2Throw e) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << λ o, ∀ Ψ'' ζ'' Φ'',
            ▷ deep_handler_spec E Ψ ζ Φ η bs Ψ'' ζ'' Φ'' -∗
            imp (stop CResume (k, o)) @ E <|Ψ''|> ⟨⟨ ζ'' ⟩⟩ {{ Φ'' }} >> -∗
        ▷ imp (eval_branches η (O3Perform v k) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }})))%I.

  (* Some definition sealing (and auxilliary functions) *)
  Local Instance deep_handler_spec_pre_contractive: Contractive deep_handler_spec_pre.
  Proof.
    rewrite /deep_handler_spec_pre /= => n wp wp' Hwp E m ζ Φ.
    repeat intro. repeat (f_contractive || f_equiv).
    repeat intro. repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  Local Definition deep_handler_spec_def := fixpoint deep_handler_spec_pre.

  Local Definition deep_handler_spec_aux : seal (@deep_handler_spec_def).
  Proof. by eexists. Qed.
  (* Top-level definition for [deep_handler] *)
  Definition deep_handler_spec := deep_handler_spec_aux.(unseal).

  Definition may_resume o k E Ψ ζ (Φ : A' → iProp Σ) : iProp Σ :=
    imp (resume k o) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.

  Lemma deep_handler_spec_unfold {E} Ψ ζ Φ Ψ' ζ' Φ' η bs :
    deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ' Φ' ⊣⊢
    (deep_handler_spec_pre deep_handler_spec_def E Ψ ζ Φ η bs Ψ' ζ' Φ').
  Proof.
    rewrite /deep_handler_spec seal_eq /deep_handler_spec_def.
    apply (@fixpoint_unfold _ _ _ _ deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_def_unfold {E} Ψ ζ Φ Ψ' ζ' Φ' η bs :
    deep_handler_spec_def E Ψ ζ Φ η bs Ψ' ζ' Φ' ≡
      ((∀ x, Φ x -∗ ▷ imp (eval_branches η (O2Ret #x) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
       (∀ e, ζ e -∗ ▷ imp (eval_branches η (O2Throw e) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' ζ'' Φ'',
            ▷ deep_handler_spec_def E Ψ ζ Φ η bs Ψ'' ζ'' Φ'' -∗
            imp (stop CResume (k, o)) @ E <|Ψ''|> ⟨⟨ ζ'' ⟩⟩ {{ Φ'' }} >> -∗
        ▷ imp (eval_branches η (O3Perform v k) bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}))%I.
  Proof.
    rewrite /deep_handler_spec_def.
    apply (fixpoint_unfold deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_mono E Ψ ζ Φ η bs Ψ' Φ1 Φ2 ζ1 ζ2 :
    (∀ a, Φ1 a -∗ Φ2 a) -∗
    (∀ e, ζ1 e -∗ ζ2 e) -∗
    deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ1 Φ1 -∗
    deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ2 Φ2.
  Proof.
    rewrite !deep_handler_spec_unfold /deep_handler_spec_pre.
    iIntros "Hmonoret Hmonoexn Hhandler".
    iSplit.
    { iIntros (a) "HΦ".
      iDestruct "Hhandler" as "[Hhandler _]".
      iSpecialize ("Hhandler" with "HΦ").
      iModIntro.
      iApply (imp_mono with "Hhandler Hmonoret Hmonoexn"). }

    iSplit.
    { iIntros (e) "Hζ".
      iDestruct "Hhandler" as "[_ [Hhandler _]]".
      iSpecialize ("Hhandler" with "Hζ").
      iNext.
      iApply (imp_mono with "Hhandler Hmonoret Hmonoexn"). }

    { iIntros (v k) "HProt".
      iDestruct "Hhandler" as "[_ [ _ Hhandler]]".
      iSpecialize ("Hhandler" $! v k with "HProt").
      iModIntro.
      iApply (imp_mono with "Hhandler Hmonoret Hmonoexn"). }
  Qed.

  Lemma prove_deep_handler_spec E Ψ ζ (Φ : A → iProp Σ) η bs Ψ' ζ' Φ' :
    ((∀ a, Φ a -∗ ▷ imp eval_branches η (O2Ret #a) bs @ E <| Ψ' |> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
     (∀ e, ζ e -∗ ▷ imp eval_branches η (O2Throw e) bs @ E <| Ψ' |> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
     (∀ (v : val) (k : cont),
        Ψ allows perform v
          << λ o, ∀ Ψ'' ζ'' Φ'',
        ▷ deep_handler_spec E Ψ ζ Φ η bs Ψ'' ζ'' Φ'' -∗
        may_resume o k E Ψ'' ζ'' Φ'' >> -∗
        ▷ imp eval_branches η (O3Perform v k) bs @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }})) -∗
     deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ' Φ'.
  Proof.
    rewrite deep_handler_spec_unfold /deep_handler_spec_pre /=.
    iIntros "Hdh"; iSplit ; last iSplit.
    { iDestruct "Hdh" as "[$ _]". }
    { iDestruct "Hdh" as "[_ [$ _]]". }
    iDestruct "Hdh" as "[_ [_ Hdh]]".
    rewrite /deep_handler_spec seal_eq.
    iApply "Hdh".
  Qed.

  Lemma inv_deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ' Φ' :
    deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ' Φ' -∗
    (∀ a, Φ a -∗ ▷ imp eval_branches η (O2Ret #a) bs @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
    (∀ e, ζ e -∗ ▷ imp eval_branches η (O2Throw e) bs @ E <| Ψ' |> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}) ∧
    (∀ (v : val) (k : cont),
       Ψ allows perform v << λ o : outcome2 val exn,
         ∀ (Ψ'' : iEff Σ) ζ'' (Φ'' : A' -d> iPropO Σ),
         ▷ deep_handler_spec_def E Ψ ζ Φ η bs Ψ'' ζ'' Φ'' -∗
         may_resume o k E Ψ'' ζ'' Φ'' >> -∗
       ▷ imp eval_branches η (O3Perform v k) bs @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}).
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

  Context {A X : Type} `{Encode A}.

  Import ewp_rules_tactics.

  (* Specification of [deep_handler] at the [expr] level. *)
  Lemma imp_deep_handler `{Encode A'} E Ψ ζ (Φ : A → iProp Σ) Ψ' ζ' (Φ' : A' → iProp Σ) η e bs:
    imp (eval η e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E Ψ ζ Φ η bs Ψ' ζ' Φ' -∗
    imp (deep_handler η e bs) @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}.
  Proof.
    (* We abstract away [eval η e]. *)
    rewrite /deep_handler; remember (eval η e); clear.

    iIntros "Hwp Hdh".

    deep_handler_spec_unfold.
    (* We proceed by Löb-induction after generalizing [η] [m] and [bs]. *)
    iLöb as "IH" forall (m η bs Ψ' ζ' Φ' E).

    (* Expand the definition of [EWP] to inspect the possible steps that
        can result from [deep_handler η e bs]. *)
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".

    (* Case analysis on the steps from [deep_handler η e bs]. *)
    rename π into π'.
    construct_wp_nonret; destruct_thread_step;
      iMod "Hmod" as "_"; try rewrite -x.

    { (* [StepHandleRet] *)
      simpl_wrap_eval_branches.
      iPoseProof (invert_imp_ret with "Hwp") as ">(%a & -> & HΦ)".
      iFrame.
      iDestruct "Hdh" as "[Hdh _]"; iSpecialize ("Hdh" with "HΦ").
      ewp_mask_intro "Hmod"; ewp_mask_elim. done. }

    { (* [StepHandleThrow] *)
      simpl_wrap_eval_branches.
      iPoseProof (invert_imp_throw with "Hwp") as ">Hζ".
      iFrame.
      iDestruct "Hdh" as "[_ [Hdh _]]"; iSpecialize ("Hdh" with "Hζ").
      ewp_mask_intro "Hmod"; ewp_mask_elim. done. }

    { (* [StepHandlePerform] *)
      iDestruct "Hdh" as "[_ [_ Hdh]]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (basic_rules.ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi")
        as ">[Hsi [HH _]]"; [ eassumption | ].

      iFrame.
      (* Install the handler around the location [l]. *)
      simpl_wrap_eval_branches.
      ewp_mask_intro "Hmod".
      ewp_mask_elim.
      iApply imp_wrap_deep.
      iIntros (?) "Hl".
      iSpecialize ("Hdh" $! e l').

      iSpecialize ("Hdh" with "[HP HH Hl]").
      { iApply (monotonic_prot with "[-HP] HP").
        iIntros (?) "Hk"; iIntros (???) "H".
        iApply (imp_resume with "Hl").
        iIntros "Hshot !>".
        rewrite deep_handler_spec_def_unfold.
        iSpecialize ("IH" with "Hk H").
        iPoseProof (basic_rules.ewp_handle_inv with "HH IH") as "Hhandle".
        iApply (imp_try2 (A1:=A') with "[Hhandle]"). rewrite /wrap_eval_branches seal_eq /pre_wrap_eval_branches /=.
        iApply "Hhandle". iSplit.
        - iIntros (a) "HΦ''".
          iApply imp_ret; auto.
        - iIntros (ex) "Hζ''".
          iApply imp_throw; auto. }
      iApply "Hdh". }

    { (* [StepHandleFork] *)
      ewp_mask_intro "Hmod".
      iModIntro. ewp_mask_elim. iFrame. destruct x.
      rewrite /impure (ewp_unfold (Stop CFork (v, v0) k)) /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iModIntro.
      construct_wp_nonret. destruct_thread_step.
      epose proof (ForkS _ _ _ _ _ _ H1) as Hstep0.
      iSpecialize ("Hwp" $! _ _ _ Hstep0).
      ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "Hwp Hdh"). }

    { (* [StepHandleJoin] *)
      ewp_mask_intro "Hmod". iModIntro. ewp_mask_elim. iFrame.
      rewrite /impure (ewp_unfold (Stop CJoin ι k)) /ewp_pre /=.
      ewp_unfold_head.
      intro_state. spec_state. iMod "Hwp".
      destruct (π !! ι); last done.
      iDestruct "Hwp" as "(%φ' & $ & Hwp)".
      iIntros "!> !> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
      iModIntro. rewrite /continue.
      iApply ("IH" with "Hwp Hdh"). }

    { (* [StepHandleCrash] *)
      by iPoseProof (invert_imp_Crash with "Hwp") as ">HFalse". }

    { (* [StepHandleLeft] *)
      eapply BaseS in H1 as Hstep.
      iCombine "Hsi Hti" as "Hsi".
      iPoseProof (basic_rules.ewp_step _ _ _ Hstep with "Hsi Hwp") as ">Hwp".
      iMod "Hwp". ewp_mask_elim. iMod "Hwp" as "(Hwp & $)". iModIntro.
      iApply ("IH" with "Hwp Hdh"). }
  Qed.

  Lemma deep_handle_nil_ret η v E Ψ ζ (Φ : A → iProp Σ) :
   imp match_failure () @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
   imp (eval_branches η (O3Ret v) []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hfail"; simpl_eval_branches.
    iApply "Hfail".
  Qed.

  Lemma shallow_handle_nil_ret η v all_bs E Ψ ζ (Φ : A → iProp Σ) :
   imp match_failure () @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
   imp (shallow_eval_branches η [] all_bs (O3Ret v)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_throw η e E Ψ ζ (Φ : A → iProp Σ) :
   imp throw e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
   imp (eval_branches η (O3Throw e) []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    by iIntros; simpl_eval_branches.
  Qed.

  Lemma shallow_handle_nil_throw η all_bs e E Ψ ζ (Φ : A → iProp Σ) :
    imp throw e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp (shallow_eval_branches η [] all_bs (O3Throw e)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_branches.
  Qed.

  Lemma deep_handle_nil_perform {E} η eff k Ψ ζ (Φ : A → iProp Σ) :
    Ψ allows perform eff << λ o, ▷ may_resume o k E Ψ ζ Φ >> -∗
    imp (eval_branches η (O3Perform eff k) []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hk". simpl_eval_branches.
    iApply basic_rules.ewp_stop_perform.
    iApply (monotonic_prot with "[] Hk").
    iIntros (o) "Ho !>"; rewrite try2_inject2.
    iApply "Ho".
  Qed.

  Lemma shallow_handle_nil_perform η eff k all_branches Ψ sk ζ (Φ : A → iProp Σ) :
    isCont k sk -∗
    Ψ allows perform eff
    << λ o,
      ▷ imp Handle (sk o) (shallow_eval_branches η all_branches all_branches) <|Ψ|> ⟨⟨ ζ ⟩⟩  {{ Φ }} >> -∗
    imp (shallow_eval_branches η [] all_branches (O3Perform eff k)) <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hk Hperf". simpl_shallow_eval_branches.
    iApply imp_wrap_shallow.

    iIntros (l) "Hl". iNext. cbn.

    iApply imp_stop_perform.

    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl Ψ) with "[Hl]").
    { iIntros (o) "H".
      iNext. rewrite try2_inject2.
      iApply (imp_resume with "Hl"). rewrite try2_inject2_right.
      iIntros "_".
      iApply (bi.later_mono with "H").
      iIntros "H".
      unfold stop.
      iApply "H". }
    iApply (monotonic_prot (Ψ:=upcl Ψ) with "[Hk]").
    { iIntros (o) "H".
      iPoseProof (basic_rules.ewp_handle_inv with "Hk") as "Hcov".
      unfold cont; simpl.
      iApply "Hcov". iApply "H". }
    done.
  Qed.

  Lemma deep_handle_cons η o cp e bs E Ψ ζ (Φ : A → iProp Σ) Hη φ :
    ⌜cpattern η η cp o Hη φ⌝ -∗
    (∀ η, ⌜Hη η⌝ -∗ imp (eval η e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (⌜φ⌝ -∗ imp (eval_branches η o bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (eval_branches η o (Branch cp e :: bs)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    simpl_eval_branches.
    iIntros "%Hpat Hmono". unfold cpattern in Hpat.
    destruct (eval_cpat η η cp o).
    - iApply "Hmono". iFrame "%".
    - iApply "Hmono". iFrame "%".
  Qed.

  Lemma deep_handle_cons_skip η o cp e bs E Ψ ζ (Φ : A → iProp Σ) :
    valid_cpattern_match cp o = false →
    imp (eval_branches η o bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp (eval_branches η o (Branch cp e :: bs)) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hvalid) "Hmatch".
    iApply deep_handle_cons.
    { iPureIntro. unfold cpattern.
      instantiate (2 := λ _, False).
      instantiate (1 := True).
      rewrite invert_valid_match; [ done | assumption ]. }
    iSplit.
    - iIntros (?) "[]".
    - iIntros (_). iApply "Hmatch".
  Qed.

End handler_proof.
