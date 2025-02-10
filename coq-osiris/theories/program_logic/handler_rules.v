From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp tactics basic_rules.
From osiris.semantics Require Import code.

From osiris.program_logic.pure Require Import pure.

(* -------------------------------------------------------------------------- *)
(** *Shallow and deep handlers *)

(* Shallow handlers are use-once handlers;
    If the handled expression performs an effect caught by the handler,
    we are done (and the handlers are not installed).
    If not, the handler is installed around the captured continuation. *)

Definition shallow_handler η e bs :=
  Handle (eval η e) (λ o, shallow_match η o bs bs).

(* Deep handlers are installed permanently;
   Regardless of whether the handled expression performs an effect
   caught by the handler, the handler is installed around the captured
   continuation. *)

Definition deep_handler η e bs :=
  Handle (eval η e) (λ o, deep_match η o bs).

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
    shallow_handler_spec E Ψ Φ (λ o, shallow_match η o bs bs) Ψ' Φ' -∗
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
    deep_handler_spec E Ψ Φ (λ o, deep_match_go η o bs) Ψ' Φ' -∗
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
      by simpl_deep_match.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi")
        as ">[Hsi [HH _]]"; [ exact H | ].

      iFrame. simpl_deep_match; rewrite !fold_pre_deep_match.
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

  Lemma deep_handle_nil_ret η v E ψ Φ :
   EWP match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP (deep_match_go η (O3Ret v) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_deep_match_go.
  Qed.

  Lemma shallow_handle_nil_ret η v all_bs E ψ Φ :
   EWP match_failure () @ E <|ψ|> {{ Φ }} -∗
   EWP (shallow_match η (O3Ret v) [] all_bs) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_match.
  Qed.

  Lemma deep_handle_nil_throw η e E ψ Φ :
   EWP throw e @ E <|ψ|> {{ Φ }} -∗
   EWP (deep_match_go η (O3Throw e) []) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_deep_match_go.
  Qed.

  Lemma shallow_handle_nil_throw η all_bs e E ψ Φ :
    EWP throw e @ E <|ψ|> {{ Φ }} -∗
    EWP (shallow_match η (O3Throw e) [] all_bs) @ E <|ψ|> {{ Φ }}.
  Proof.
    by iIntros; simpl_shallow_match.
  Qed.

  Lemma deep_handle_nil_perform η eff k ψ sk Φ :
    k ↦ K sk -∗
    ψ allows perform eff
    << λ o,
      ▷ (k ↦ Shot -∗ EWP (sk o) <|ψ|> {{ Φ }}) >> -∗
    EWP (deep_match_go η (O3Perform eff k) []) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hl Hperf".
    simpl_deep_match_go. iApply ewp_stop_perform.
    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iModIntro.
      rewrite try2_inject2.
      iApply "Hcov". rewrite try2_ret_right. iApply "H". }
    done.
  Qed.

  Lemma shallow_handle_nil_perform η eff k all_branches ψ sk Φ :
    k ↦ K sk -∗
    ψ allows perform eff
    << λ o,
      ▷ EWP Handle (sk o) (λ o,
          shallow_match η o all_branches all_branches) <|ψ|> {{ Φ }} >> -∗
    EWP (shallow_match η (O3Perform eff k) [] all_branches) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hk Hperf". simpl_shallow_match.
    iApply ewp_install_shallow.

    iIntros (l) "Hl". iNext. cbn.

    iApply ewp_stop_perform.

    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iNext. rewrite try2_inject2. iApply "Hcov". rewrite try2_ret_right.
      iApply (bi.later_mono with "H").
      iIntros "H _".
      iApply "H". }
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hk]").
    { iIntros (o) "H".
      iPoseProof (ewp_handle_inv with "Hk") as "Hcov".
      iApply "Hcov". iApply "H". }
    done.
  Qed.

  Lemma deep_handle_cons η o cp e bs E ψ Φ Q φ :
    Q -∗
    ⌜cpattern η η cp o (λ δ, Q ⊢ EWP (eval δ e) @ E <|ψ|> {{ Φ }}) φ⌝ -∗
    (Q -∗ ⌜φ⌝ -∗ EWP (deep_match_go η o bs) @ E <|ψ|> {{ Φ }}) -∗
    EWP (deep_match_go η o (Branch cp e :: bs)) @ E <|ψ|> {{ Φ }}.
  Proof.
    simpl_deep_match_go.
    iIntros "Q %Hpure Hmono".
    iApply ewp_try.
    iApply ewp_mono; first by iApply pure_ewp.
    iIntros ([|]); simpl.
    - iIntros "%HmonQ". iApply (HmonQ with "Q").
    - iApply ("Hmono" with "Q").
  Qed.

  Lemma deep_handle_cons_no_resources η o cp e bs E ψ Φ φ :
    ⌜cpattern η η cp o (λ δ, ⊢ EWP (eval δ e) @ E <|ψ|> {{ Φ }}) φ⌝ -∗
    (⌜φ⌝ -∗ EWP (deep_match_go η o bs) @ E <|ψ|> {{ Φ }}) -∗
    EWP (deep_match_go η o (Branch cp e :: bs)) @ E <|ψ|> {{ Φ }}.
  Proof.
    simpl_deep_match_go.
    iIntros "%Hpure Hmono".
    iApply ewp_try.
    iApply ewp_mono; first iApply pure_ewp; try done.
    iIntros ([|]); simpl.
    - iIntros "%Heval"; iApply Heval.
    - iApply "Hmono".
  Qed.

  Lemma deep_handle_cons_skip η o cp e bs E ψ Φ :
    valid_cpattern_match cp o = false ->
    EWP (deep_match_go η o bs) @ E <|ψ|> {{ Φ }} -∗
    EWP (deep_match_go η o (Branch cp e :: bs)) @ E <|ψ|> {{ Φ }}.
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
