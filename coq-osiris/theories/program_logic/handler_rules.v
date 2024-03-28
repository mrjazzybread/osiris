From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp tactics.
From osiris.semantics Require Import code.

(* -------------------------------------------------------------------------- *)
(** *Reasoning about effect handlers *)

Section handler_specifications.

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
        ▷ EWP e @ E <| Ψ' |> {{ Φ' }}) ∧

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
          << fun o => ∀ Ψ'' Φ'',
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

  Definition deep_handler_spec_def := fixpoint deep_handler_spec_pre.

  Local Definition deep_handler_spec_aux : seal (@deep_handler_spec_def).
  Proof. by eexists. Qed.
  Definition deep_handler_spec := deep_handler_spec_aux.(unseal).

  (* TODO : Prove rule about [deep_handler_spec] (probably needs to be done at
      the expr level). *)

End handler_specifications.

Section handler_proof.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Lemma shallow_handler_spec_unfold {E} Ψ Φ Ψ' Φ' η bs :
    shallow_handler_spec E Ψ Φ Ψ' Φ' η bs ⊣⊢
    shallow_handler_spec_pre shallow_handler_spec_def E Ψ Φ Ψ' Φ' η bs.
  Proof.
    rewrite /shallow_handler_spec seal_eq /shallow_handler_spec_def;
    apply (@fixpoint_unfold _ _ _ shallow_handler_spec_pre).
  Qed.

  Local Ltac spec_unfold :=
    rewrite !shallow_handler_spec_unfold /shallow_handler_spec_pre /=.

  Lemma ewp_shallow_handler E Ψ Φ Ψ' Φ' η o bs:
    ⌜try_cextend_pure η o bs = None⌝ -∗
    shallow_handler_spec E Ψ Φ Ψ' Φ' η bs -∗
    EWP (eval_shallow_match η o bs) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* Induction on the handler, which is a list of branches *)
    iInduction bs as [ | ] "IH".
    { (* Empty handler. *)
      iIntros "Hspec"; spec_unfold.
      cbn; destruct o.

      (* [O3Ret] case *)
      -

  Admitted.
  
End handler_proof.
