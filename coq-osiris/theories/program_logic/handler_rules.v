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
  Handle (eval η e) (λ o, shallow_eval_match η o bs).

(* Deep handlers are installed permanently;
     Regardless of whether the handled expression performs an effect
    caught by the handler, the handler is installed around the captured
    continuation. *)

Definition deep_handler η e bs :=
  Handle (eval η e) (λ o, deep_eval_match η o bs).

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
    shallow_handler_spec E Ψ Φ (λ o, shallow_eval_match η o bs) Ψ' Φ' -∗
    EWP (shallow_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros "He Hspec".
    rewrite /shallow_handler.
    (* Follows immediately by the reasoning rule on [Handle]. *)
    by iApply (ewp_handle with "He").
  Qed.

  Definition deep_handler_body := pre_eval_match_aux eval true.

  Definition shallow_handler_body := pre_eval_match_aux eval false.

  (* Specification of [deep_handler] at the [expr] level. *)
  Lemma ewp_deep_handler E Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E Ψ Φ (λ o, deep_handler_body η o bs bs) Ψ' Φ' -∗
    EWP (deep_handler η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We abstract away [eval η e]. *)
    rewrite /deep_handler; remember (eval η e); clear.

    (* We proceed by Löb-induction after generalizing [η] [m] and [bs]. *)
    iLöb as "IH" forall (m η bs Ψ' Φ').

    (* Expand the definition of [EWP] to inspect the possible steps that
        can result from [deep_handler η e bs]. *)
    iIntros "He Hsh"; ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".

    (* Case analysis on the steps from [deep_handler η e bs]. *)
    construct_wp_nonret; destruct_step; cbn -[deep_eval_match];
      iMod "Hmod" as "_"; try rewrite -x; cbn -[deep_eval_match];
    rewrite !deep_handler_spec_unfold /deep_handler_spec_pre /=.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      by ewp_mask_intro "Hmod"; ewp_mask_elim.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".

      (* [Perform e] satisfies the protocol specification *)
      iPoseProof (ewp_perform_inv with "[$]") as "HP"; iMod "HP".

      (* We allocate a new location that contains the continuation *)
      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H | ].

      iFrame; rewrite {2}/deep_eval_match; cbn -[deep_eval_match].

      (* Install the handler around the location [l]. *)
      iApply (ewp_install with "HH").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iIntros (?) "Hl"; cbn.

      iAssert (Ψ allows perform e
        << λ o : outcome2 val exn, (* We need the annotation here; LATER: remove? *)
            ∀ Ψ'' Φ'',
              ▷ deep_handler_spec_def E Ψ Φ
                (λ o, deep_handler_body η o bs bs) Ψ'' Φ'' -∗
              EWP stop CResume (l', o) @ E <| Ψ'' |> {{ Φ'' }} >>)%I
        with "[HP Hl]" as "HΨ".
      { iApply (monotonic_prot with "[Hl] HP"); iFrame.
        iIntros (?) "Hwp"; cbn; iIntros (??) "H".
        iSpecialize ("IH" with "Hwp").

        rewrite /deep_handler_spec seal_eq.

        (* Resume the continuation that stored the installed handler *)
        iApply (ewp_resume with "Hl"). iNext.
        iIntros "Hl". cbn.
        iSpecialize ("IH" with "H").

        (* Rewriting under binders for handle.. LATER: Remove? *)
        erewrite (eq_handle_handle (k w) _); first done.
        intros; cbn. rewrite try2_ret_right; reflexivity. }
      (* We're forgetting the [Shot] information here.
           Do we want to strengthen this?  *)

      by iSpecialize ("Hsh" with "HΨ"). }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iSpecialize ("IH" with "H").
      rewrite deep_handler_spec_unfold.
      iApply ("IH" with "Hsh"). }
  Qed.

  Lemma handle_nil_ret deep η v all_branches ψ Φ :
   EWP match_failure () <|ψ|> {{ Φ }} -∗
   EWP (pre_eval_match_aux eval deep η (O3Ret v) [] all_branches) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros.
  Qed.

  Lemma handle_nil_throw deep η e all_branches ψ Φ :
   EWP throw e <|ψ|> {{ Φ }} -∗
   EWP (pre_eval_match_aux eval deep η (O3Throw e) [] all_branches) <|ψ|> {{ Φ }}.
  Proof.
    by iIntros.
  Qed.

  Lemma deep_handle_nil_perform η eff k all_branches ψ sk Φ :
    k ↦ K sk -∗
    ψ allows perform eff
    << λ o,
      ▷ (k ↦ Shot -∗ EWP (sk o) <|ψ|> {{ Φ }}) >> -∗
    EWP (deep_handler_body η (O3Perform eff k) [] all_branches) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hl Hperf".
    iApply ewp_stop_perform.
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
          shallow_handler_body η o all_branches all_branches) <|ψ|> {{ Φ }} >> -∗
    EWP (shallow_handler_body η (O3Perform eff k) [] all_branches) <|ψ|> {{ Φ }}.
  Proof.
    iIntros "Hl Hperf".
    iApply (ewp_install with "Hl").

    iIntros (l) "Hl". iNext. cbn.

    iApply ewp_stop_perform.

    rewrite /prot /iEff_car.
    iApply (monotonic_prot (Ψ:=upcl OS ψ) with "[Hl]").
    { iIntros (o) "H".
      iPoseProof (ewp_resume with "Hl") as "Hcov".
      iModIntro.
      iApply "Hcov". rewrite try2_ret_right.
      iApply (bi.later_mono with "H").
      iIntros "H _".
      iApply "H". }
    done.
  Qed.

  Lemma handle_cons deep η o cp e bs all_branches ψ Φ φ Q :
    cpattern η cp o (λ δ, Q ⊢ EWP (eval δ e) <|ψ|> {{ Φ }}) φ ->
    Q -∗
    (⌜φ⌝ -∗ EWP (pre_eval_match_aux eval deep η o bs all_branches) <|ψ|> {{ Φ }}) -∗
    EWP (pre_eval_match_aux eval deep η o (Branch cp e :: bs) all_branches) <|ψ|> {{ Φ }}.
  Proof.
    unfold cpattern.
    iIntros (Hpat) "Q Hcov".
    destruct Hpat as [ (δ & Hsimp & Hewp) | (exc & Hsimp & Hφ) ];
      simpl; iApply ewp_try;
      (iApply ewp_simp; [ eassumption | ]).
    - iApply ewp_value; simpl. iApply (Hewp with "Q").
    - iApply ewp_throw; simpl. iApply ("Hcov" $! Hφ).
  Qed.


End handler_proof.
