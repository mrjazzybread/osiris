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
    (* If [⊢ ⟨ ⊥ ⟩ impure m (λ v. ⌜φ v⌝)] holds *)
    ⊢ EWP m @ ⊤ <| ⊥ |> {{ fun o =>  ⌜ φ o ⌝ }}) →
    (* Then executing [m] cannot terminate with an unhandled effect or a crash, *)
    adequate NotStuck m
      σ (* in any initial heap, *)
      (λ o _, φ o) (* and the returned outcome satisfies the postcondition [φ] *).
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
  (* In particular, instantiating
     - [σ] with the empty heap
     - [φ] with [match o with | O2Ret v => φ' v | O2Throw v => False]
     Yields theorem 8.1 from the paper.

     Furthermore, instantiating [m] with [eval η e] yields corollary 8.2 *)

  (* To further substantiate the claim that programs proved with the empty protocol
     cannot perform unhandled effects, consider the following corollary. *)
  Corollary no_unhandled_effect m σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ},
    (* If [⊢ ⟨ ⊥ ⟩ impure m (λ v. ⌜φ v⌝)] holds *)
    ⊢ EWP m @ ⊤ <| ⊥ |> {{ fun o => ⌜ φ o ⌝ }}) →
    (* For any configuration [(t, σ')] *)
    ∀ t σ',
      (* reached from the starting configuration [([m], σ)]. *)
      rtc erased_step ([m], σ) (t, σ') →
      (* None of the computations in the threadpool are unhandled effects. *)
      ∀ m',
        m' ∈ t →
        ∀ e k, m' ≠ Stop CPerf e k.
  Proof.
    intros [_ H]%(ewp_adequacy _ σ).
    intros t σ' S m' I e k Heq. subst m'.
    specialize (H t σ' _ eq_refl S I).
    destruct H.
    - destruct H. discriminate.
    - destruct H as (? & ? & ? & ? & Hstep).
      inversion Hstep as [Hstep' ->].
      inversion Hstep'.
  Qed.

End adequacy.
