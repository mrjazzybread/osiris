From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp tactics basic_rules.
From osiris.semantics Require Import code.

(* -------------------------------------------------------------------------- *)
(** *Reasoning about effect handlers *)

Section handler_specifications.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

(* -------------------------------------------------------------------------- *)
  (** * Deep handler specification. *)

  Definition deep_handler_spec_pre
    (deep_handler_spec:
      coPset -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ) :
      coPset -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      (outcome3 val exn -> microvx) -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      iPropI Σ :=
    (λ E Ψ Φ h Ψ' Φ',
      ((* [Return] and [Exception] branch *)
      (∀ o, Φ o -∗ ▷ EWP (h o) @ E <| Ψ' |> {{ Φ' }}) ∧

      (* [Effect] branch *)
      (∀ v k, Ψ allows perform v
          << fun o : outcome2 val exn => ∀ Ψ'' Φ'',
            ▷ deep_handler_spec E Ψ Φ h Ψ'' Φ'' -∗
            EWP (stop CResume (k, o)) @ E <| Ψ'' |> {{ Φ'' }} >> -∗
        ▷ EWP (h (O3Perform v k)) @ E <| Ψ' |> {{ Φ' }})))%I.

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
  Definition deep_handler_spec := deep_handler_spec_aux.(unseal).

  Lemma deep_handler_spec_unfold {E} Ψ Φ Ψ' Φ' h :
    deep_handler_spec E Ψ Φ h Ψ' Φ' ⊣⊢
    deep_handler_spec_pre deep_handler_spec_def E Ψ Φ h Ψ' Φ'.
  Proof.
    rewrite /deep_handler_spec seal_eq /deep_handler_spec_def;
    apply (@fixpoint_unfold _ _ _ deep_handler_spec_pre).
  Qed.


  (* TODO : Prove rule about [deep_handler_spec] (probably needs to be done at
      the expr level). *)

End handler_specifications.

(* TODO : Move *)
Definition outcome3_to_micro (o : outcome3 val exn) :=
  match o with
  | O3Ret a => Ret a
  | O3Throw e => Throw e
  | O3Perform e k => Stop CPerform e (fun v => stop CResume (k, v))
  end.

(* TODO : Move *)
Notation "l ↦ v" := (gen_heap.mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Opaque eval_match.

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


Section handler_proof.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Import ewp_rules_tactics.

  Definition shallow_match η e bs :=
    Handle (eval η e) (λ o, eval_shallow_match η o bs).

  Definition deep_match η e bs :=
    Handle (eval η e) (λ o, eval_deep_match η o bs).

  Lemma ewp_shallow_match E Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The shallow handler specification is met *)
    shallow_handler_spec E Ψ Φ (λ o, eval_shallow_match η o bs) Ψ' Φ' -∗
    EWP (shallow_match η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iIntros "He Hspec".
    rewrite /shallow_match.
    by iApply (ewp_handle with "He").
  Qed.

  Lemma ewp_deep_match E Ψ Φ Ψ' Φ' η e bs:
    EWP (eval η e) @ E <| Ψ |> {{ Φ }} -∗
    (* The deep handler specification is met *)
    deep_handler_spec E Ψ Φ (λ o, pre_eval_match_aux eval true η o bs bs) Ψ' Φ' -∗
    EWP (deep_match η e bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [η] [e] and [bs]. *)
    rewrite /deep_match. remember (eval η e). clear.
    iLöb as "IH" forall (m η bs Ψ' Φ').

    iIntros "He Hsh".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    Opaque eval_deep_match.
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; try rewrite -x; cbn;
    rewrite !deep_handler_spec_unfold /deep_handler_spec_pre /=.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      by ewp_mask_intro "Hmod"; ewp_mask_elim.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "[$]") as "HP".
      iMod "HP".

      iDestruct (gen_heap.gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H0 | ].
      iFrame.

      Transparent eval_deep_match.
      rewrite {2}/eval_deep_match.
      Opaque eval_deep_match.
      cbn.

      iApply (ewp_install with "HH").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iIntros (?) "Hl"; cbn.

      iAssert (Ψ allows perform e
        << λ o : outcome2 val exn,
            ∀ Ψ'' Φ'',
              ▷ deep_handler_spec_def E Ψ Φ (λ o, pre_eval_match_aux eval true η o bs bs) Ψ'' Φ'' -∗
              EWP stop CResume (l', o) @ E <| Ψ'' |> {{ Φ'' }} >>)%I
        with "[HP Hl]" as "HΨ".
      { iApply prot_mono_post; iFrame.
        iIntros (?) "Hwp"; cbn.
        iIntros (??) "H".
        iSpecialize ("IH" with "Hwp").

        rewrite /deep_handler_spec seal_eq.

        iApply (ewp_resume with "Hl"). iNext.
        iIntros (?) "Hl". cbn.
        iSpecialize ("IH" with "H").

        erewrite (eq_handle_handle (k w) (λ o : outcome3 C.val C.exn, try2 (eval_match η o bs) inject2)).
        2 : intros; rewrite try2_ret_right; reflexivity.
        done. } (* We're forgetting the [Shot] information here *)

      iSpecialize ("Hsh" with "HΨ"). Transparent eval_deep_match.
      rewrite /eval_deep_match /pre_eval_match. done. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iSpecialize ("IH" with "H").
      rewrite deep_handler_spec_unfold.
      iApply ("IH" with "Hsh"). }
  Qed.

End handler_proof.

Section alternative_handler_specifications.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

 (* -------------------------------------------------------------------------- *)
  (** * Shallow handler specification. *)

  Definition shallow_handler_spec_pre
    (shallow_handler_spec:
      coPset -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      env -d>
      handler -d>
      iPropI Σ) :
      coPset -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      P -d>
      (outcome2 val exn -d> iPropO Σ) -d>
      env -d>
      handler -d>
      iPropI Σ :=
    (λ E Ψ Φ Ψ' Φ' η bs,

     (* [Return] and [Exception] branch *)
      (∀ (o : outcome2 val exn) e,
        Φ o -∗
        ⌜try_cextend_pure η o bs = Some e⌝ -∗
        EWP e @ E <| Ψ' |> {{ Φ' }}) ∧

     (* Effectful branch. *)
      (∀ v k η' e,
        ⌜try_cextend_eff η v k bs = Some (η', e)⌝ -∗
        Ψ allows perform v
          << λ o, ▷ EWP (stop CResume (k, o)) @ E <| Ψ |> {{ Φ }} -∗
                   ▷ EWP (eval η' e) @ E <| Ψ' |> {{ Φ' }} >>) ∧

     (* Effectful branch that fell through *)
      (∀ v k,
        ⌜try_cextend_eff η v k bs = None⌝ -∗
        Ψ allows perform v
          << fun o => ▷ EWP (stop CInstall (k, η, bs)) @ E <| prot_bottom |>
              {{ RET l, shallow_handler_spec E Ψ Φ Ψ' Φ' η bs -∗
                  ▷ EWP (stop CResume (l, o)) @ E <| Ψ' |> {{ Φ' }} }} >>)) %I.


  Local Instance shallow_handler_spec_pre_contractive:
    Contractive shallow_handler_spec_pre.
  Proof.
    rewrite /shallow_handler_spec_pre /= => n wp wp' Hwp E m Φ.
    repeat intro. repeat (f_contractive || f_equiv).
    repeat intro. repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  Definition shallow_handler_spec_def := fixpoint shallow_handler_spec_pre.
  Local Definition shallow_handler_spec_aux : seal (@shallow_handler_spec_def).
  Proof. by eexists. Qed.
  Definition shallow_handler_spec := shallow_handler_spec_aux.(unseal).

  Lemma shallow_handler_spec_unfold {E} Ψ Φ Ψ' Φ' η bs :
    shallow_handler_spec E Ψ Φ Ψ' Φ' η bs ⊣⊢
    shallow_handler_spec_pre shallow_handler_spec_def E Ψ Φ Ψ' Φ' η bs.
  Proof.
    rewrite /shallow_handler_spec seal_eq /shallow_handler_spec_def;
    apply (@fixpoint_unfold _ _ _ shallow_handler_spec_pre).
  Qed.

End alternative_handler_specifications.


(* ------------------------------------------------------------------------ *)
  (* Local tactics *)

Local Ltac spec_unfold :=
  rewrite !shallow_handler_spec_unfold /shallow_handler_spec_pre /=.
