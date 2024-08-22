From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp tactics basic_rules.
From osiris.semantics Require Import code.

(* -------------------------------------------------------------------------- *)
(** *Shallow and deep handlers *)

(* Shallow handlers are use-once handlers;
    If the handled expression performs an effect caught by the handler,
    we are done (and the handlers are not installed).
    If not, the handler is installed around the captured continuation. *)

Definition shallow_handler η e bs :=
  Handle (eval η e) (shallow_eval_match η bs bs).

(* Deep handlers are installed permanently;
   Regardless of whether the handled expression performs an effect
   caught by the handler, the handler is installed around the captured
   continuation. *)

Definition deep_handler η e bs :=
  Handle (eval η e) (install_deep_eval_match η bs).

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
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ) :
      coPset -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      iEff Σ -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ :=
    (λ E Ψ Φ h Ψ' Φ',
      ((* [Return] and [Exception] branch *)
      (∀ o, Φ o -∗ ▷ EWP (h o) @ E <| Ψ' |> {{ Φ' }}) ∧

      (* [Effect] branch (one-shot) *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' Φ'',
            ▷ deep_handler_spec E Ψ Φ h Ψ'' Φ'' -∗
            EWP (stop CResume (k, o)) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
        ▷ EWP (h (O3Perform v k)) @ E <| Ψ' |> {{ Φ' }})))%I.

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

  Lemma deep_handler_spec_unfold {E} Ψ Φ Ψ' Φ' h :
    deep_handler_spec E Ψ Φ h Ψ' Φ' ⊣⊢
    deep_handler_spec_pre deep_handler_spec_def E Ψ Φ h Ψ' Φ'.
  Proof.
    rewrite /deep_handler_spec seal_eq /deep_handler_spec_def;
    apply (@fixpoint_unfold _ _ _ deep_handler_spec_pre).
  Qed.

  Lemma deep_handler_spec_mono E ψ φ h ψ' φ1 φ2 :
    (∀ o, φ1 o -∗ φ2 o) -∗
    deep_handler_spec E ψ φ h ψ' φ1 -∗
    deep_handler_spec E ψ φ h ψ' φ2.
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

(* LATER: refactor *)
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
          match goal with
          | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
            iMod (ewp_crash_inv with "[$][$]") as "%"
          end
      end
  end.

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
    shallow_handler_spec E Ψ Φ (shallow_eval_match η bs bs) Ψ' Φ' -∗
    EWP (shallow_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros "He Hspec".
    rewrite /shallow_handler.
    (* Follows immediately by the reasoning rule on [Handle]. *)
    by iApply (ewp_handle with "He").
  Qed.

  (* Specification of [deep_handler] at the [expr] level. *)
  Lemma ewp_deep_handler E Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E Ψ Φ (deep_eval_match η bs) Ψ' Φ' -∗
    EWP (deep_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We abstract away [eval η e]. *)
    rewrite /deep_handler; remember (eval η e); clear.

    (* We proceed by Löb-induction after generalizing [η] [m] and [bs]. *)
    iLöb as "IH" forall (m η bs Ψ' Φ' E).

    (* Expand the definition of [EWP] to inspect the possible steps that
        can result from [deep_handler η e bs]. *)
    iIntros "He Hsh"; ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".

    (* Case analysis on the steps from [deep_handler η e bs]. *)
    construct_wp_nonret; destruct_step;
      iMod "Hmod" as "_"; try rewrite -x;
      rewrite !deep_handler_spec_unfold /deep_handler_spec_pre /=.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh"; ewp_mask_intro "Hmod"; ewp_mask_elim;
      by simpl_install_deep_eval_match.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi")
        as ">[Hsi [HH _]]"; [ exact H | ].

      iFrame. simpl_install_deep_eval_match; rewrite !fold_pre_install_deep_eval_match.
      (* Install the handler around the location [l]. *)
      iApply ewp_install_deep.
      ewp_mask_intro "Hmod".
      ewp_mask_elim. (* TODO this eliminates a ▷ in the goal
                             but not in "Hsh", so we lose; FIXME *)
      iIntros (?) "Hl".
      iSpecialize ("Hsh" $! e l').

      iSpecialize ("Hsh" with "[HP HH Hl]").
      { rewrite /prot.
        iApply (monotonic_prot with "[HH Hl] HP").
        iIntros (?) "Hk"; iIntros (??) "H".
        rewrite /deep_handler_spec seal_eq.
        iApply (ewp_resume with "Hl").
        iSpecialize ("IH" with "Hk H").
        iPoseProof (ewp_handle_inv with "HH IH") as "Hhandle".
        iNext. iIntros "H".
        by rewrite try2_ret_right. }
      done. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iSpecialize ("IH" with "H").
      rewrite deep_handler_spec_unfold.
      iApply ("IH" with "Hsh"). }
  Qed.

  Lemma deep_handle_nil_ret η v ψ Φ :
   EWP match_failure () <|ψ|> {{ Φ }} -∗
   EWP (deep_eval_match η [] (O3Ret v)) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_deep_eval_match.
  Qed.

  Lemma shallow_handle_nil_ret η v all_bs ψ Φ :
   EWP match_failure () <|ψ|> {{ Φ }} -∗
   EWP (shallow_eval_match η [] all_bs (O3Ret v)) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_match.
  Qed.

  Lemma deep_handle_nil_throw η e ψ Φ :
   EWP throw e <|ψ|> {{ Φ }} -∗
   EWP (deep_eval_match η [] (O3Throw e)) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_deep_eval_match.
  Qed.

  Lemma shallow_handle_nil_throw η all_bs e ψ Φ :
    EWP throw e <|ψ|> {{ Φ }} -∗
    EWP (shallow_eval_match η [] all_bs (O3Throw e)) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_eval_match.
  Qed.

  Lemma deep_handle_nil_perform η eff k ψ sk Φ :
    k ↦ K sk -∗
    ψ allows perform eff
    << λ o,
      ▷ (k ↦ Shot -∗ EWP (sk o) <|ψ|> {{ Φ }}) >> -∗
    EWP (deep_eval_match η [] (O3Perform eff k)) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hl Hperf".
    simpl_deep_eval_match. iApply ewp_stop_perform.
    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iModIntro.
      iApply "Hcov". rewrite try2_ret_right. iApply "H". }
    done.
  Qed.

  Lemma shallow_handle_nil_perform η eff k all_branches ψ sk Φ :
    k ↦ K sk -∗
    ψ allows perform eff
    << λ o,
      ▷ EWP Handle (sk o) (λ o,
          shallow_eval_match η all_branches all_branches o) <|ψ|> {{ Φ }} >> -∗
    EWP (shallow_eval_match η [] all_branches (O3Perform eff k)) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hk Hperf". simpl_shallow_eval_match.
    iApply ewp_install_shallow.

    iIntros (l) "Hl". iNext. cbn.

    iApply ewp_stop_perform.

    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iNext. iApply "Hcov". rewrite try2_ret_right.
      iApply (bi.later_mono with "H").
      iIntros "H _".
      iApply "H". }
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hk]").
    { iIntros (o) "H".
      iPoseProof (ewp_handle_inv with "Hk") as "Hcov".
      iApply "Hcov". iApply "H". }
    done.
  Qed.

  Lemma deep_handle_cons η o cp e bs E ψ Φ φ1 φ2 :
    cpattern η cp o φ1 φ2 ->
    (∀ δ, ⌜φ1 δ⌝ -∗ EWP (eval δ e) @ E <|ψ|> {{ Φ }}) -∗
    (⌜φ2⌝ -∗ EWP (deep_eval_match η bs o) @ E <|ψ|> {{ Φ }}) -∗
    EWP (deep_eval_match η (Branch cp e :: bs) o) @ E <|ψ|> {{ Φ }}.
  Proof.
    unfold cpattern; simpl_deep_eval_match.
    iIntros (Hpat) "Heval Hcov".
    destruct Hpat as [ (δ' & Hsimp & Hewp) | (exc & Hsimp & Hφ) ];
      simpl; iApply ewp_try;
      (iApply ewp_simp; [ eassumption | ]).
    - iApply ewp_value; simpl. by iApply "Heval".
    - iApply ewp_throw; simpl. iApply ("Hcov" $! Hφ).
  Qed.

  Lemma deep_handle_cons' η o cp e bs E ψ Φ φ :
    ⌜cpattern η cp o (λ δ, ⊢ EWP (eval δ e) @ E <|ψ|> {{ Φ }} ) φ⌝ -∗
    (⌜φ⌝ -∗ EWP (deep_eval_match η bs o) @ E <|ψ|> {{ Φ }}) -∗
    EWP (deep_eval_match η (Branch cp e :: bs) o) @ E <|ψ|> {{ Φ }}.
  Proof.
    unfold cpattern; simpl_deep_eval_match.
    iIntros (Hpat) "Hcov".
    destruct Hpat as [ (δ & Hsimp & Hewp) | (exc & Hsimp & Hφ) ];
      simpl; iApply ewp_try;
      (iApply ewp_simp; [ eassumption | ]).
    - iApply ewp_value; simpl. iApply Hewp.
    - iApply ewp_throw; simpl. iApply ("Hcov" $! Hφ).
  Qed.

  Lemma deep_handle_cons_unary η o cp e bs E ψ Φ Q φ :
    cpattern η cp o (λ δ, Q -∗ EWP (eval δ e) @ E <|ψ|> {{ Φ }}) φ ->
    Q -∗
    (⌜φ⌝ -∗ EWP (deep_eval_match η bs o) @ E <|ψ|> {{ Φ }}) -∗
    EWP (deep_eval_match η (Branch cp e :: bs) o) @ E <|ψ|> {{ Φ }}.
  Proof.
    unfold cpattern. simpl_deep_eval_match.
    destruct 1 as [(δ & Hsimp & Hewp) | (exc & Hsimp & Hewp)];
      iIntros "Q Hno_match";
      iApply ewp_try;
      iApply (ewp_simp _ _ _ _ _ Hsimp).
    { iApply ewp_value; simpl. iApply (Hewp with "Q"). }
    { iApply ewp_throw; simpl. iApply ("Hno_match" $! Hewp). }
  Qed.

  Lemma deep_handle_cons_skip η o cp e bs E ψ Φ :
    valid_cpattern_match cp o = false ->
    EWP (deep_eval_match η bs o) @ E <|ψ|> {{ Φ }} -∗
    EWP (deep_eval_match η (Branch cp e :: bs) o) @ E <|ψ|> {{ Φ }}.
  Proof.
    iIntros (Hvalid) "Hmatch".
    iAssert (bi_pure True) as "Htrue". done.
    iApply deep_handle_cons'.
    { iPureIntro. unfold cpattern.
      rewrite invert_valid_match; [ | assumption ].
      apply total_throw. apply I. }
    { iIntros "_". iApply "Hmatch". }
  Qed.

End handler_proof.
