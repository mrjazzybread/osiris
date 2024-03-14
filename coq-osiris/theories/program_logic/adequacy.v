From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.
From iris.program_logic Require Import weakestpre adequacy.

From osiris.program_logic Require Import ewp rules tactics.


(* -------------------------------------------------------------------------- *)
Section ewp_wp.

  Import ewp_rules_tactics.

  (*  We show an adequacy of a closed program using the fact that the adequacy of
    [EWP] is a consequence of the adequacy of [WP]. This is following the adequacy
    proof of [Hazel] (de Vilhena & Pottier) *)

  Lemma ewp_imp_wp {Σ P} {A X}
    {irisGen: irisGS_gen HasNoLc (@osiris_lang A X) Σ}
    {Prot: @protocol_wf Σ P}
    E (e : micro A X) (Φ : outcome2 A X -> _) :
    EWP e @ E <| prot_bottom |> {{ Φ }} -∗ WP e @ NotStuck; E {{ Φ }} : iProp Σ.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "Hwp".
    destruct (to_val e) as [ v         |] eqn:?.
    (* [e] is an outcome2 (either [ret _] or [throw _]). *)
    { rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.
      destruct e; inversion Heqo; subst; eauto. }
    rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.
    ewp_case_is_handleable e ;inversion Heqo.
    iMod "Hwp".
    { by iPoseProof (prot_bottom_absurd with "Hwp") as "H". }
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
  Context `{protocol_wf Σ P}.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP], for closed programs. *)

  Theorem ewp_adequacy e σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ},
    ⊢ EWP e @ ⊤ <| prot_bottom |> {{ fun v =>  ⌜ φ v ⌝ }}) →
    adequate NotStuck e σ (λ v _, φ v).
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

End adequacy.

