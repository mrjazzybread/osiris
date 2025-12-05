From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.program_logic Require Import thread_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Definition WPTP `{!osirisGS Σ} (π : thpool) (πp : post_map Σ): iProp Σ :=
  ([∗ map] ι ↦ m; φ ∈ π; πp, EWP m @ ⊤ <| (ι, ⊥) |> {{ φ }}).

Definition is_final {A E} (m : micro A E) : Prop :=
  match m with
  | Ret _ | Throw _ => True
  | _ => False
  end.

Definition is_join {A E} (m : micro A E) : Prop :=
  match m with
  | Stop CJoin _ _ => True
  | _ => False
  end.

Definition not_stuck {Σ A E} (m : micro A E) σ (πp : post_map Σ) ι :=
  is_final m ∨ can_progress σ πp m ι ∨ is_join m.

Lemma wp_wptp `{!osirisGS Σ} ι m φ :
  EWP m @ ⊤ <| (ι, ⊥) |> {{ φ }} ⊢ WPTP {[ι := m ]} {[ι := φ]}.
Proof. by rewrite /WPTP big_sepM2_singleton. Qed.

Include ewp_rules_tactics.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma ewp_not_stuck {A X} m F E (e : micro A X) ι σ πp Φ n:
    SAT m F [view E; supply n] (state_interp (σ, πp) ∗
                                  EWP e @ E <| (ι, ⊥) |> {{ Φ }}) →
    not_stuck e σ πp ι.
  Proof.
    intros Hsat. rewrite /not_stuck.
    rewrite ewp_unfold /ewp_pre /= in Hsat.
    ewp_case e; simpl in Hsat.
    1,2: by left. all: right.
    - exfalso.
      apply SAT_frame_cons in Hsat.
      apply SAT_fupd in Hsat.
      by apply SAT_elim in Hsat.
    - exfalso.
      apply SAT_frame_cons in Hsat.
      apply SAT_fupd in Hsat.
      rewrite /prot upcl_bottom in Hsat.
      by apply SAT_elim in Hsat.
    - rewrite Hhm in Hsat.
      eapply SAT_mono with (Q := (|={E, ∅}=> ⌜can_progress σ πp e ι⌝)%I)
                           in Hsat.
      { eapply SAT_fupd, SAT_elim in Hsat.
        by left. }
      iIntros "[Hsi Hwp]".
      spec_state. iModIntro.
      iPureIntro; assumption.
  Qed.

  Lemma ewp_postcondition {A X} m F E Ψ (e : micro A X) (Φ : outcome2 A X -> iProp Σ) v n:
    SAT m F [view E; supply n] (EWP e @ E <|Ψ|> {{ Φ }}) →
    outcome2_opt e = Some v →
    SAT m F [view E; supply n] (Φ v).
  Proof.
    intros Hsat Hval. eapply SAT_mono in Hsat; last first.
    { iIntros "Hwp".
      destruct e; try discriminate Hval; inversion Hval.
      - iPoseProof (ewp_ret_inv with "Hwp") as "Hret".
        rewrite H0. iApply "Hret".
      - iPoseProof (ewp_throw_inv with "Hwp") as "Hthrow".
        iApply "Hthrow". }
    by eapply SAT_fupd in Hsat.
  Qed.

  Inductive nsteps {A X} : nat → config A X → config A X → Prop :=
    nsteps_refl : ∀ ρ : config A X, nsteps 0 ρ ρ
  | nsteps_l :
    ∀ (n : nat) (ρ1 ρ2 ρ3 : config A X),
      step ρ1 ρ2 →
      nsteps n ρ2 ρ3 →
      nsteps (S n) ρ1 ρ3.

  Lemma not_elem_of_lookup {K} `{FinMapDom K M D} {A} (ι ι' : K) (π : M A) (m : A) :
    ι' ≠ ι ->
    π !! ι' = None ->
    (<[ ι := m ]> π) !! ι' = None.
  Proof.
    intros Hneq Hlookup.
    apply not_elem_of_dom.
    rewrite dom_insert.
    apply not_elem_of_union; split.
    - apply not_elem_of_singleton.
      apply Hneq.
    - apply not_elem_of_dom. apply Hlookup.
  Qed.

  Lemma wptp_extract_wp π πp ι m :
    ⌜π !! ι = Some m⌝ -∗
    WPTP π πp -∗
    ∃ φ, ⌜πp !! ι = Some φ⌝ ∗ EWP m @ ⊤ <| (ι, ⊥) |> {{ φ }} ∗ WPTP (delete ι π) (delete ι πp).
  Proof.
    iIntros "%Hlookup Hwps".
    iPoseProof (big_sepM2_delete_l with "Hwps") as "(%φ & Hlookup_p & Hwp & Hwps)".
    apply Hlookup.
    iFrame.
  Qed.

  Lemma SAT_wptp_extract_wp π πp ι e m F Rs :
    π !! ι = Some e →
    SAT m F Rs (WPTP π πp) →
    SAT m F Rs (∃ φ, ⌜πp !! ι = Some φ⌝ ∗ WPTP (delete ι π) (delete ι πp) ∗ EWP e <| (ι, ⊥) |> {{ φ }})%I.
  Proof.
    intros Hlookup Hsat.
    eapply SAT_mono, Hsat.
    iIntros "HWPTP".
    iPoseProof (wptp_extract_wp $! Hlookup with "HWPTP") as "(%φ & $ & $ & $)".
  Qed.

  Lemma sat_wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 πp e2 σ2 μ Φ n :
    thread_step (σ1, e1, ι, πp) (σ2, e2, μ) →
    SAT m F [view E; supply n]
      (state_interp (σ1, πp) ∗ EWP e1 @ E <| (ι, Ψ) |> {{ Φ }}) →
    ∃ n', SAT m F [view E; supply n']
            (EWP e2 @ E <| (ι, Ψ) |> {{ Φ }} ∗
            (match μ with
             | None => state_interp (σ2, πp)
             | Some (ι', e') =>
                 ∃ φ, state_interp (σ2, <[ι':=φ]>πp) ∗ EWP e' @ E <| (ι', ⊥) |> {{ λ o, □ φ o }}
             end)).
  Proof.
    intros Hstep Hsat. eapply SAT_mono in Hsat; last first.
    { iIntros "[HSI Hwp]". rewrite ewp_unfold /ewp_pre.
      rewrite (thread_step_is_EStep _ _ _ _ _ _ _ Hstep).
      iSpecialize ("Hwp" with "HSI").
      iExact "Hwp". }
    eapply SAT_fupd in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[_ Hwp]". iSpecialize ("Hwp" $! _ _ _ Hstep). iExact "Hwp". }
    eapply (SAT_frame_resource _ (view ∅)) in Hsat; last apply _.
    eapply SAT_unframe_resource in Hsat.
    eapply SAT_fupd in Hsat.
    eapply SAT_later in Hsat.
    eapply SAT_fupd in Hsat.
    eexists n. apply Hsat.
  Qed.

  Lemma ewp_fork_inv {A X} σ π ι ι' v1 v2 (k : _ -> micro A X) E Ψ Φ :
    ⌜π !! ι' = None⌝ -∗
    state_interp (σ, π) -∗
    EWP Stop CFork (v1, v2) k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> ∃ φ, EWP call v1 v2 @ E <| (ι', ⊥) |> {{ λ o, □ φ o }} ∗
    EWP (continue k (VThread ι')) @ E <| (ι, Ψ) |> {{ Φ }} ∗ state_interp (σ, <[ ι' := φ ]> π).
  Proof.
    iIntros "%Hlookup Hsi Hfork".
    rewrite ewp_unfold /ewp_pre /=.
    spec_state.
    epose proof (ForkS _ ι π v1 v2 k ι' Hlookup) as Hfstep.
    iSpecialize ("Hfork" $! _ _ _ Hfstep).
    ewp_mask_elim.
    iMod "Hfork" as "(Hcontinue & %φ & Hsi & Hfork)".
    by iFrame.
  Qed.

  Lemma ewp_join_inv {A X} φ σ πp ι' (k : _ → micro A X) ι Ψ Φ E o :
    ⌜πp !! ι' = Some φ⌝ -∗
    ⌜(⊢ φ o)⌝ -∗
    state_interp (σ, πp) -∗
    EWP Stop CJoin ι' k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, πp) ∗ EWP k o @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hjoin %Hφ Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state. clear Hstep.
    epose proof (JoinS _ _ _ _ _ _ _ Hjoin Hφ) as Hstep.
    iSpecialize ("Hwp" $! _ _ _ Hstep).
    ewp_mask_elim. iMod "Hwp" as "($ & $)". done.
  Qed.

  Lemma ewp_self_inv {A X} σ π ι (k : _ -> micro A X) Ψ Φ E :
    state_interp (σ, π) -∗
    EWP Stop CSelf () k @ E <|(ι, Ψ)|> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, π) ∗ EWP (continue k (VThread ι)) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "Hsi Hwp".
    ewp_unfold (Stop CSelf () k). spec_state.
    epose proof (SelfS _ _ _ _ _) as Hwpstep.
    iSpecialize ("Hwp" $! _ _ _ Hwpstep).
    ewp_mask_elim. iMod "Hwp" as "($ & $)". done.
  Qed.

  Lemma attempt_thread_join_step {A X} ι' π1 k (m : micro A X) σ (πp : post_map Σ) ι :
    (∀ ι o, π1 !! ι ≫= is_outcome = Some o → ∃ φ, πp !! ι = Some φ ∧ (⊢ φ o)) →
    dom πp ≡ dom π1 →
    attempt_join ι' π1 k = Some m →
    thread_step (σ, Stop CJoin ι' k, ι, πp) (σ, m, None).
  Proof.
    intros Hinv Heqdom Hattempt.
    unfold attempt_join in Hattempt.
    case (π1 !! ι') eqn:Heq.
    - assert (is_Some (πp !! ι')) as (φ & Hlookup_p).
      { apply (elem_of_dom πp ι'). rewrite Heqdom. apply elem_of_dom.
        eexists; eassumption. }
      destruct m0; try discriminate Hattempt;
        inversion Hattempt; subst;
        unfold continue, discontinue.
      + specialize (Hinv ι' (O2Ret a)).
        destruct Hinv as (? & ? & Hφ). rewrite Heq. reflexivity.
        eapply JoinS; eassumption.
      + specialize (Hinv ι' (O2Throw e)).
        destruct Hinv as (? & ? & Hφ). rewrite Heq. reflexivity.
        eapply JoinS; eassumption.
    - inversion Hattempt; subst.
      apply JoinCrashS.
      apply (not_elem_of_dom πp ι'). rewrite Heqdom. apply not_elem_of_dom. assumption.
  Qed.

  Lemma threadpool_thread_step (σ1 σ2 : store) (π1 π2 : thpool) πp :
    (∀ ι o, π1 !! ι ≫= is_outcome = Some o → ∃ φ, πp !! ι = Some φ ∧ (⊢ φ o)) →
    dom πp ≡ dom π1 →
    threadpool_step (σ1, π1) (σ2, π2) →
    ∃ (ι : thread) (m m' : microvx) μ,
      π1 !! ι = Some m ∧
      π2 !! ι = Some m' ∧
        @thread_step Σ val exn (σ1, m, ι, πp) (σ2, m', μ).
  Proof.
    intros Hinv Hdomeq.
    inversion 1.
    - eapply BaseS in H5.
      exists ι, m, m', None.
      split; first assumption.
      split; first apply lookup_insert.
      eassumption.
    - exists ι, (Stop CFork (v1, v2) k), (continue k (VThread ι')), (Some (ι', call v1 v2)).
      split; first assumption.
      split; first (rewrite lookup_insert_ne; first apply lookup_insert).
      intros ->; rewrite H5 in H3; discriminate.
      apply ForkS.
      apply (not_elem_of_dom_1 πp ι'). rewrite Hdomeq. apply not_elem_of_dom_2. assumption.
    - exists ι, (Stop CJoin ι' k), m, None.
      split; first assumption.
      split; first apply lookup_insert.
      eapply attempt_thread_join_step; eassumption.
    - exists ι, (Stop CSelf () k), (continue k (VThread ι)), None.
      split; first assumption.
      split; first apply lookup_insert.
      apply SelfS.
  Qed.

  Lemma WPTP_insert_delete ι π1 πp m' φ :
    ⌜πp !! ι = Some φ⌝ -∗
    WPTP (delete ι π1) (delete ι πp) -∗
    EWP m' <|(ι, ⊥)|> {{ φ }} -∗
    WPTP (<[ι:=m']> π1) πp.
  Proof.
    iIntros "%Hlookup Hwps Hwp".
    replace πp with (<[ι:=φ]>πp) by apply (insert_id πp ι φ Hlookup).
    iApply big_sepM2_insert_delete.
    replace πp with (<[ι:=φ]>πp) at 2 by apply (insert_id πp ι φ Hlookup).
    iFrame.
  Qed.


    Lemma wptp_step' (π1 : thpool) (πp : post_map Σ) σ1 σ2 m m' ι μ :
    ⌜π1 !! ι = Some m⌝ -∗
    (state_interp (σ1, πp) ∗ WPTP π1 πp) -∗
    ⌜thread_step (σ1, m, ι, πp) (σ2, m', μ)⌝ -∗
    |={⊤}[∅]▷=> match μ with
                | None => state_interp (σ2, πp) ∗ WPTP (<[ι:=m']>π1) πp
                | Some (ι', mforked) => ∃ (φ : outcome2 val exn → iProp Σ),
                    state_interp (σ2, <[ι':=φ]>πp) ∗ WPTP (<[ι':=mforked]> (<[ι:=m']>π1)) (<[ι':=φ]>πp)
                end.
  Proof.
    iIntros "%Hlookup [Hsi Hwps] %Hstep".
    iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
    assert (dom πp ≡ dom π1) as Hdomequiv by (rewrite Hdomeq; reflexivity).
    iPoseProof (wptp_extract_wp $! Hlookup with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
    iPoseProof (ewp_step with "Hsi Hwp") as "Hwp". apply Hstep.
    iMod "Hwp"; ewp_mask_elim; iMod "Hwp". ewp_mask_elim; iMod "Hwp" as "[Hwp Hrest]".
    iModIntro.
    inversion Hstep; subst.
    - iFrame.
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps Hwp").
    - iFrame.
      iApply big_sepM2_insert_delete. iFrame.
    destruct Hcases; last first.

    iExists μ. destruct μ as [[ι' mforked] | ].
    - iDestruct "Hrest" as "(%φ' & $ & Hfork)".


  Lemma wptp_step' (π1 π2 : thpool) (πp : post_map Σ) σ1 σ2 :
    (state_interp (σ1, πp) ∗ WPTP π1 πp) -∗
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ -∗
    |={⊤}[∅]▷=> ∃ (μ : option (thread * microvx)),
    match μ with
    | None => state_interp (σ2, πp) ∗ WPTP π2 πp
    | Some (ι', m') => ∃ (φ : outcome2 val exn → iProp Σ), state_interp (σ2, <[ι':=φ]>πp) ∗ WPTP π2 (<[ι':=φ]>πp)
  end.
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
    assert (dom πp ≡ dom π1) as Hdomequiv by (rewrite Hdomeq; reflexivity).
    have Hsteps := threadpool_thread_step σ1 σ2 π1 π2 πp Hdomequiv Hstep.
    destruct Hsteps as (ι & m & m' & μ & Hlookup1 & Hlookup2 & Hcases).
    iPoseProof (wptp_extract_wp $! Hlookup1 with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
    destruct Hcases; last first.
    iPoseProof (ewp_step with "Hsi Hwp") as "Hwp". apply H.
    iMod "Hwp"; ewp_mask_elim; iMod "Hwp". ewp_mask_elim; iMod "Hwp" as "[Hwp Hrest]".
    iModIntro.
    iExists μ. destruct μ as [[ι' mforked] | ].
    - iDestruct "Hrest" as "(%φ' & $ & Hfork)".


    inversion Hstep; subst.
    - (* Simplify the threadpool in the goal. *)
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H2 with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
      (* Get [EWP m'] judgment from the facts that [EWP m] and [m -> m']. *)
      iPoseProof (ewp_step with "Hsi Hwp") as "Hwp".
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "[$ Hwp]".
      (* Recombine [EWP m'] with [WPTP]. *)
      iApply big_sepM_insert_delete.
      by iFrame.

    - apply invert_some_active_thread in H2 as Hm.
      (* Simplify the threadpool in the goal. *)
      rewrite (fmap_insert) (local_view_insert_id _ _ _ _ Hm).
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! Hm with "Hwps") as "(Hfork & Hwps)".
      (* Inversion on [EWP Stop CFork]. *)
      apply lookup_local_fresh in H4 as Hforgot.
      iPoseProof (ewp_fork_inv $! Hforgot with "Hsi Hfork") as "Hfork".
      iMod "Hfork"; ewp_mask_elim; iMod "Hfork" as "(Hforked & Hcontinue & $)"; iModIntro.
      (* Recombine [EWP]s into one big [WPTP]. *)
      iApply big_sepM_insert.
      { (* Assertion about the fresh thread index [ι']. *)
        assert (ι' ≠ ι) as Hfresh.
        { intro Heq; rewrite Heq in H4; rewrite H4 in Hm; discriminate. }
        rewrite unfold_micro_insert; by apply not_elem_of_lookup. }
      iFrame.
      iApply big_sepM_insert_delete.
      iFrame.

    - apply invert_some_active_thread in H2 as Hm.
      (* Simplify the threadpool in the goal. *)
      rewrite (local_view_insert_id _ _ _ _ Hm).
      (* Get the [EWP] jugment for the active thread. *)
      iPoseProof (wptp_extract_wp $! Hm with "Hwps") as "(Hjoin & Hwps)".
      (* Invert the [EWP Stop CJoin]. *)
      iPoseProof (ewp_join_inv $! H4 with "Hsi Hjoin") as "Hwp".
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp)".
      (* Recombine the [EWP] and [WPTP] judgments. *)
      iApply big_sepM_insert_delete.
      by iFrame.

    - apply invert_some_active_thread in H0 as Hm.
      (* Simplify the threadpool in the goal. *)
      rewrite (local_view_insert_id _ _ _ _ Hm).
      (* Geth the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! Hm with "Hwps") as "(Hself & Hwps)".
      (* Invert the [EWP Stop CSelf]. *)
      iPoseProof (ewp_self_inv with "Hsi Hself") as "Hwp".
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp)".
      (* Recombine the [EWP] and [WPTP] judgments. *)
      iApply big_sepM_insert_delete.
      by iFrame.

    - subst.
      apply invert_some_active_thread in H0 as Hm.
      (* Simplify the threadpool in the goal. *)
      rewrite fmap_insert.
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! Hm with "Hwps") as "(Hdie & Hwps)".
      (* Inversion on [EWP Stop CDie] to get the updated state interp. *)
      apply lookup_local_view in Hm.
      eassert (ι ∈ dom _) as Hdom. { eapply elem_of_dom; eexists; apply Hm. }
      iPoseProof (ewp_die_inv $! Hdom with "Hsi Hdie") as "Hwp".
      iMod "Hwp". ewp_mask_elim. iMod "Hwp" as "($ & Hwp)".
      (* No need to recombine the [EWP] and [WPTP] because the definition of
         [WPTP] does not require anything on terminated threads.  *)
      iApply big_sepM_insert_delete.
      iFrame.
      done.
  Qed.

  Lemma wptp_step m F n π1 π2 σ1 σ2 :
    SAT m F [view ⊤; supply n]
      (state_interp (σ1, to_local_view <$> π1) ∗ WPTP π1) →
    threadpool_step (σ1, π1) (σ2, π2) →
    ∃ n', SAT m F [view ⊤; supply n']
             (|={⊤}[∅]▷=> state_interp (σ2, to_local_view <$> π2) ∗ WPTP π2 ).
  Proof.
    intros Hsat Hstep.
    exists n.
    eapply SAT_mono; [ | apply Hsat ].
    iIntros "Hsiwp".
    iApply (wptp_step' with "Hsiwp").
    iPureIntro. apply Hstep.
  Qed.

  Lemma wptp_steps m F n k π1 π2 σ1 σ2 :
    SAT m F [view ⊤; supply n] (state_interp (σ1, to_local_view <$> π1) ∗ WPTP π1) →
    threadpool_steps k (σ1, π1) (σ2, π2) →
    ∃ n', SAT m F [view ⊤; supply n'] (state_interp (σ2, to_local_view <$> π2) ∗ WPTP π2).
  Proof.
    induction k as [|k IH] in  n, π1, σ1 |-*; intros Hsat Hsteps.
    - revert Hsat. inversion_clear Hsteps. exists n.
      apply Hsat.
    - revert Hsat. inversion_clear Hsteps as [|?? [σ1' π1']]. intros Hsat.
      eapply wptp_step in Hsat as (n' & Hsat); last done.
      apply SAT_fupd in Hsat. apply SAT_later in Hsat. apply SAT_fupd in Hsat.
      eapply IH in Hsat as (n'' & Hsat); last done.
      exists n''. apply Hsat.
  Qed.

  Lemma wptp_not_stuck m F n e es ι σ π:
    SAT m F [view ⊤; supply n] (state_interp (σ, to_local_view <$> π) ∗ WPTP es) →
    es !! ι = Some (Active e) →
    not_stuck e (σ, π) ι.
  Proof.
    intros Hsat Hlookup.
    rewrite -SAT_frame_cons in Hsat.
    eapply SAT_wptp_extract_wp in Hsat; last eassumption.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[_ Hwp]". iApply "Hwp". }
    rewrite SAT_frame_cons in Hsat.
    by eapply ewp_not_stuck in Hsat.
  Qed.

  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy m F n k σ1 π1 σ2 π2:
    SAT m F [view ⊤; supply n] (state_interp (σ1, to_local_view <$> π1) ∗ WPTP π1) →
    threadpool_steps k (σ1, π1) (σ2, π2) →
    ∀ ι m,
      π2 !! ι = Some (Active m) ->
      not_stuck m (σ2, π2) ι.
  Proof.
    intros Hsat Hsteps. eapply wptp_steps in Hsat as (n' & Hsat); last done.
    intros ι e Hlookup.
    eauto using wptp_not_stuck.
  Qed.


  Lemma ewp_adequacy m F n ι e σ1 σ2 π2 k :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (state_interp (σ1, {[ ι := Alive ]}) ∗
       EWP e @ ⊤ <| (ι, ⊥) |> {{ λ _, True%I }}) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    threadpool_steps k (σ1, {[ι := Active e]}) (σ2, π2) →
    (* then no thread is stuck *)
    (∀ ι m, π2 !! ι = Some (Active m) → not_stuck m (σ2, π2) ι).
  Proof.
    intros Hsat Hsteps. rewrite wp_wptp in Hsat.
    rewrite -insert_empty in Hsat.
    replace (<[ι:=Alive]> ∅) with (@fmap (gmap thread) _ _ _ to_local_view (<[ι:=Active e]> ∅)) in Hsat;
      last first.
    { rewrite fmap_insert. reflexivity. }
    eapply wptp_adequacy; eauto.
  Qed.

End satisfiability_weakest_pre.



(* Lemma for handling the allocation of invariants and later credits. *)
(* To use it, you should:
    - pick a type X that carries all of the global ghost names for your language (e.g., [heapGS] for HeapLang)
    - pick a function [I] that takes the ghost names and produces an Iris instance
    - prove that you can allocate the initial state interpretation for some [x: X]
    - prove a weakest precondition for all choices of [x: X]

  Then you obtain the result of [wp_adequacy] for your choice of [X] and [I]. *)
Local Existing Instance invGS_wsat.
Lemma SAT_ewp_adequacy `{!invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 σ2 π2 (e : micro val exn) ι n k P:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS_gen HasNoLc Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: osirisGS Σ := I x in
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp (σ1, {[ι:=Alive]}) ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e @ ⊤ <| (ι, ⊥) |> {{ λ _, True }}) →
  (* then any k-step execution is safe: *)
  threadpool_steps k (σ1, {[ι := (Active e) ]}) (σ2, π2) →
  (∀ ι m, π2 !! ι = Some (Active m) → not_stuck m (σ2, π2) ι).
Proof.
  intros Halloc Hwp Hsteps.
  pose proof (SAT_intro (Σ := Σ)) as Hsat.
  eapply SAT_alloc_fancy_updates in Hsat as [Hi Hsat].
  eapply (Halloc Hi True%I) in Hsat as (x & Hsat); eauto; simpl in *.
  eapply SAT_mono in Hsat; last first.
  { iIntros "SI". iPoseProof (Hwp x) as "Hwp". iCombine "SI Hwp" as "Hx". iExact "Hx". }
  eapply (@ewp_adequacy Σ (I x)), Hsteps.
  eapply SAT_mono, Hsat.
  { iIntros "([$ P] & Hwp)". by iApply "Hwp". }
Qed.

Program Definition initial_thread `{!osirisGpreS Σ} : ghost_map.ghost_mapG Σ thread () := _.
Next Obligation.
  intros.
  apply gen_heapGpreS_heap.
Defined.

Program Definition initial_dead `{!osirisGpreS Σ} : ghost_map.ghost_mapG Σ thread (outcome2 val exn) := _.
Next Obligation.
  intros.
  apply gen_heapGpreS_heap.
Defined.

Lemma osiris_initial_allocation `{!osirisGpreS Σ} (ι : thread) σ (_ : invGS_gen HasNoLc Σ) (F : iProp Σ) :
  SAT Alloc F [view ⊤; supply 0] True →
  ∃ (h: osirisGS Σ),
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in
    SAT Alloc F [view ⊤; supply 0] (state_interp (σ, {[ ι := Alive ]} )).
Proof.
  intros Hsat.
  eapply SAT_frame_resource with (R := view _) in Hsat; last apply _.
  eapply SAT_frame_resource with (R := supply _) in Hsat; last apply _.
  eapply (SAT_gen_heap_init σ) in Hsat as [Hgen Hsat].
  eapply (@SAT_gen_heap_init thread _ _ thread_state Σ _ {[ ι := Alive ]}) in Hsat as [Hgen' Hsat].
  eapply (SAT_ghost_map_alloc {[ ι := () ]}) in Hsat as [γ Hsat].
  eapply (SAT_ghost_map_alloc ∅) in Hsat as [γ' Hsat].
  do 2 apply SAT_unframe_resource in Hsat.
  pose (hg := (@OsirisGS Σ _ _ Hgen Hgen' initial_thread γ initial_dead γ')).
  exists hg.
  eapply SAT_mono; last apply Hsat.
  iIntros "(Hdead & Hdeadown & Halive & Haliveown & Hgen' & Hpts' & Hmeta' & Hgen & Hpts & Hmeta)".
  iFrame.
  rewrite !big_sepM_singleton.
  rewrite omap_singleton.
  unfold dead_threads_of; rewrite omap_singleton_None; [ | reflexivity ].
  rewrite big_sepM_empty.
  iSplitR "Hdead"; [ | iSplitL "Hdead"; done ].
  iApply "Halive".
Qed.



(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations under open gFunctors [Σ]. *)

  Definition osiris_adequacy Σ `{!osirisGpreS Σ} (e : micro val exn) ι σ1 π2 σ2 k :
    (* If we can show [EWP e1 {{ True }}] with the ghost state provided by [Σ]. *)
    (∀ `{!osirisGS Σ}, ⊢ EWP e @ ⊤ <|(ι, ⊥)|> {{ λ _, True }}) →
    (* then any k-step execution is safe: *)
    threadpool_steps k (σ1, {[ι := (Active e)]}) (σ2, π2) →
    (∀ ι m, π2 !! ι = Some (Active m) → not_stuck m (σ2, π2) ι).
  Proof.
    intros Hwp.
    eapply SAT_ewp_adequacy with (X := osirisGS Σ) (P := λ _, bi_pure True).
    - intros iv F Hsat_init.
      have [h Hsat] := (osiris_initial_allocation ι σ1 iv F Hsat_init).
      exists h.
      eapply SAT_mono, Hsat.
      apply bi.sep_True_2.
    - apply Hwp.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for a closed list of gFunctors. *)

  (* Provide a minimal gFunctors for invariants, the store, and threads *)
  Definition osirisΣ : gFunctors :=
    #[ invΣ;
       gen_heapΣ locations.loc step.block;
       gen_heapΣ thread thread_state;
       gen_heapΣ thread unit;
       gen_heapΣ thread (outcome2 val exn)
      ].
  (* Show that inclusion of [osirisΣ] in [Σ] is enough to instantiate [osirisGpreS Σ]. *)
  Global Instance subG_heapGpreS {Σ} : subG osirisΣ Σ → osirisGpreS Σ.
  Proof. solve_inG. Qed.

  (* Example of an adequacy statement instantiated with a specific set of [gFunctors]. *)

  Definition osiris_adequacy_closed (e : micro val exn) ι σ1 π2 σ2 k :
    (∀ `{!osirisGS osirisΣ}, ⊢ EWP e @ ⊤ <|(ι, ⊥)|> {{ λ _, True }}) →
    threadpool_steps k (σ1, {[ι := (Active e) ]}) (σ2, π2) →
    (∀ ι m, π2 !! ι = Some (Active m) → not_stuck m (σ2, π2) ι).
  Proof.
    intros Hwp. eapply osiris_adequacy, Hwp. apply _.
  Qed.

End adequacy.
