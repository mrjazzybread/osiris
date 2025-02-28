From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.
From iris.program_logic Require Import weakestpre adequacy.

From osiris.program_logic Require Import ewp basic_rules tactics.


(* -------------------------------------------------------------------------- *)
Section ewp_wp.

  Import ewp_rules_tactics.

  (*  We show an adequacy of a closed program using the fact that the adequacy of
    [EWP] is a consequence of the adequacy of [WP]. This is following the adequacy
    proof of [Hazel] (de Vilhena & Pottier) *)

  Lemma ewp_imp_wp {Σ} {A X}
    {irisGen: irisGS_gen HasNoLc (@osiris_lang A X) Σ}
    E (m : micro A X) (Φ : outcome2 A X -> _) :
    EWP m @ E <| ⊥ |> {{ Φ }} -∗ WP m @ NotStuck; E {{ Φ }} : iProp Σ.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "Hwp".
    destruct (to_val m) as [ v         |] eqn:?.
    (* [e] is an outcome2 (either [ret _] or [throw _]). *)
    { rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.
      destruct m; inversion Heqo; subst; eauto. }
    rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.
    ewp_case_is_handleable m ;inversion Heqo.
    { iMod "Hwp". done. }
    iMod "Hwp".
    { rewrite /prot; rewrite upcl_bottom; done. }
    intro_state. iMod ("Hwp" with "Hsi") as "[% H]".
    iSplitL "".
    { iPureIntro; destruct H, x. eexists nil, _,_, nil; cbn; split; eauto. }
    iModIntro. iIntros (e2 σ2 efs step) "H£".
    destruct step as (Hstep&->).
    iSpecialize ("H" $! _ _ Hstep).
    iMod "H"; iModIntro. iNext.
    repeat iModIntro.
    iApply step_fupdN_intro; [set_solver | ..].
    iNext; cbn; iMod "H"; iModIntro.
    iDestruct "H" as "[$ Hwp]"; iSplitR ""; last done.
    iApply ("IH" with "Hwp").
  Qed.

End ewp_wp.


(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  Context {A X : Type} {Σ : gFunctors}.

  Context `{!osirisGpreS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations. *)

  Theorem ewp_adequacy m σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ},
    ⊢ EWP m @ ⊤ <| ⊥ |> {{ fun o =>  ⌜ φ o ⌝ }}) →
    adequate NotStuck m σ (λ o _, φ o).
  Proof.
    intros Hwp.
    eapply (wp_adequacy_gen HasNoLc Σ _).
    iIntros (??) "".
    iMod (gen_heap_init σ) as (?) "[Hh _]".
    iModIntro. iExists
      (λ σ κs, gen_heap_interp σ),
      (λ _, True%I). iFrame.
    iApply ewp_imp_wp. iApply Hwp.
  Qed.

  (* Consequence: programs proved with the empty protocol cannot perform
  unhandled effects *)
  Corollary no_unhandled_effect m σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ},
    ⊢ EWP m @ ⊤ <| ⊥ |> {{ fun o => ⌜ φ o ⌝ }}) →
    ∀ m' t σ',
      rtc erased_step ([m], σ) (t, σ') →
      m' ∈ t →
      ∀ e k, m' ≠ Stop CPerform e k.
  Proof.
    intros [_ H]%(ewp_adequacy _ σ).
    intros m' t σ' S I e k Heq. subst m'.
    specialize (H t σ' _ eq_refl S I).
    destruct H.
    - destruct H. discriminate.
    - destruct H as (? & ? & ? & ? & Hstep).
      inversion Hstep as [Hstep' ->].
      inversion Hstep'.
  Qed.

End adequacy.
