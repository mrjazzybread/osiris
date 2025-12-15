From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap saved_prop.

From osiris.program_logic Require Import thread_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Require Import Coq.Program.Equality.

Definition WPTP `{!osirisGS Σ} (π : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))): iProp Σ :=
  ([∗ map] ι ↦ m; '(γ, φ) ∈ π; πp, saved_pred_own γ DfracDiscarded φ ∗ EWP m @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }}).

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

Definition not_stuck {A E} (m : micro A E) σ (π : gset thread) :=
  is_final m ∨ can_progress σ π m ∨ is_join m.

Lemma wp_wptp `{!osirisGS Σ} ι m γ φ :
  (saved_pred_own γ DfracDiscarded φ ∗ EWP m @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }}) ⊣⊢ WPTP {[ι := m ]} {[ι := (γ, φ)]}.
Proof.
  unfold WPTP.
  by rewrite big_sepM2_singleton.
Qed.

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

Lemma wptp_dom `{!osirisGS Σ} m F Rs π πp :
  SAT m F Rs (WPTP π πp) → dom πp ≡ dom π.
Proof.
  intros Hsat.
  eapply SAT_elim, SAT_mono, Hsat.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  iPureIntro. by rewrite Hdomeq.
Qed.

Lemma WPTP_dom `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp = dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  by iPureIntro.
Qed.

Lemma WPTP_extract_wp `{!osirisGS Σ} π πp ι e :
  ⌜π !! ι = Some e⌝ -∗
  WPTP π πp -∗
  ∃ γ φ , ⌜πp !! ι = Some (γ, φ)⌝ ∗
         saved_pred_own γ DfracDiscarded φ ∗
         EWP e @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }} ∗ WPTP (delete ι π) (delete ι πp).
Proof.
  iIntros "%Hlookup Hwps".
  iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
  assert (∃ φ, πp !! ι = Some φ) as ((γ & φ) & Hlookup_p).
  { apply (elem_of_dom πp ι).
    rewrite Hdomeq. apply elem_of_dom. eexists; eassumption. }
  iPoseProof (big_sepM2_delete _ _ _ _ _ _ Hlookup Hlookup_p with "Hwps")
    as "((Hvalid & Hwp) & Hwps)".
  iFrame.
  by iPureIntro.
Qed.

Lemma WPTP_extract_posts `{!osirisGS Σ} π πp :
  WPTP π πp ⊢ ∀ ι o, ⌜π !! ι ≫= is_outcome = Some o⌝ -∗ ∃ γ φ, ⌜πp !! ι = Some (γ, φ)⌝ ∗ (|={⊤}=> □ φ o).
Proof.
  iIntros "Hwps" (ι o Hlookup).
  unfold mbind in Hlookup.
  apply bind_Some in Hlookup.
  destruct Hlookup as (m & Hlookup & Houtcome).
  iPoseProof (big_sepM2_delete_l with "Hwps")
    as "(%p & %Hlookup_p & H & Hwps)".
  apply Hlookup. destruct p as [γ φ]. iDestruct "H" as "[? Hwp]".
  iExists γ, φ.
  iFrame "%".
  destruct m; inversion Houtcome.
  - iApply (ewp_ret_inv with "Hwp").
  - iApply (ewp_throw_inv with "Hwp").
Qed.

Include ewp_rules_tactics.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma ewp_not_stuck {A X} m F E (e : micro A X) ι σ πp Φ n:
    SAT m F [view E; supply n] (state_interp (σ, πp) ∗ EWP e @ E <| (ι, ⊥) |> {{ Φ }}) →
    not_stuck e σ (dom πp).
  Proof.
    intros Hsat. rewrite /not_stuck.
    rewrite ewp_unfold /ewp_pre /= in Hsat.
    ewp_case e; simpl in Hsat.
    left; by destruct o.
    all: right.
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
      eapply SAT_mono with (Q := (|={E, ∅}=> ⌜can_progress σ (dom πp) e⌝)%I) in Hsat.
      { eapply SAT_fupd, SAT_elim in Hsat.
        by left. }
      iIntros "[Hsi Hwp]".
      spec_state. iModIntro.
     by iPureIntro.
    - right. done.
  Qed.

  Lemma EWP_not_stuck_post {A X} E (e : micro A X) ι σ πp Φ :
    state_interp (σ, πp) ∗ EWP e @ E <| (ι, ⊥) |> {{ Φ }} ={E}[∅]▷=∗
    ⌜not_stuck e σ (dom πp)⌝ ∗ (∀ o, ⌜e = inject2 o⌝ -∗ Φ o).
  Proof.
    iIntros "(Hsi & Hwp)". rewrite /not_stuck.
    ewp_unfold e.
    ewp_case e; simpl.
    - ewp_mask_intro "Hmod". iNext. iMod "Hmod". iMod "Hwp". iModIntro.
      iSplitR.
      + iPureIntro; left; by destruct o.
      + iIntros (o' Hlookup); unfold inject2 in Hlookup.
        destruct o; destruct o'; try discriminate Hlookup; inversion Hlookup; iApply "Hwp".
    - by iMod "Hwp".
    - rewrite /prot upcl_bottom.
      by iMod "Hwp".
    -
      spec_state. rename Hstep into Hprog.
      apply invert_can_progress in Hprog as Hstep.
      destruct Hstep as [Hstep|Hstep].
      { destruct Hstep as (ι' & k & -> & Hdom).
        discriminate Hhm. }
      destruct Hstep as [Hstep|Hstep].
      { destruct Hstep as (v1 & v2 & k & ->).
        epose proof (ForkS σ ι (dom πp) v1 v2 k (fresh (dom πp)) (is_fresh _)).
        Unshelve.
        spec_step.
        iModIntro. iNext. iMod "Hwp". iModIntro.
        iSplitR.
        + iPureIntro.
          right; left.
          apply can_progress_fork.
        + iIntros (o HFalse). destruct o; discriminate HFalse. }
      destruct Hstep as [Hstep|Hstep].
      { destruct Hstep as (u & k & ->).
        epose proof (SelfS σ (dom πp) ι u k).
        spec_step.
        iModIntro. iNext. iMod "Hwp". iModIntro.
        iSplitR.
        + iPureIntro.
          right; left.
          apply can_progress_self.
        + iIntros (o HFalse). destruct o; discriminate HFalse. }
      destruct Hstep as ([??] & ?).
      pose proof (BaseS e σ ι m s (dom πp) H).
      spec_step. iModIntro. iNext. iMod "Hwp". iModIntro.
      iSplitR.
      + iPureIntro.
        right; left.
        assumption.
      + iIntros (o HFalse).
        rewrite HFalse in H0.
        dependent destruction H0.
        destruct o; dependent destruction H0.
        destruct o; discriminate x.
    - spec_state.
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iModIntro.
      iSplitR.
      + iPureIntro.
        by right; right.
      + iIntros (o HFalse). destruct o; discriminate HFalse.
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

  Lemma EWP_postcondition {A X} E Ψ (e : micro A X) (Φ : outcome2 A X -> iProp Σ) v :
    ⌜outcome2_opt e = Some v⌝ -∗
    (EWP e @ E <|Ψ|> {{ Φ }}) ={E}=∗
    Φ v.
  Proof.
    iIntros "%Hval Hwp".
    destruct e; try discriminate Hval; inversion Hval.
    - iPoseProof (ewp_ret_inv with "Hwp") as "Hret".
      iApply "Hret".
    - iPoseProof (ewp_throw_inv with "Hwp") as "Hthrow".
      iApply "Hthrow".
  Qed.

  Inductive nsteps {A X} : nat → config A X → config A X → Prop :=
    nsteps_refl : ∀ ρ : config A X, nsteps 0 ρ ρ
  | nsteps_l :
    ∀ (n : nat) (ρ1 ρ2 ρ3 : config A X),
      step ρ1 ρ2 →
      nsteps n ρ2 ρ3 →
      nsteps (S n) ρ1 ρ3.

  Lemma sat_wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 πp e2 σ2 μ Φ n :
    thread_step (σ1, e1, ι, dom πp) (σ2, e2, μ) →
    SAT m F [view E; supply n]
      (state_interp (σ1, πp) ∗ EWP e1 @ E <| (ι, Ψ) |> {{ Φ }}) →
    ∃ n', SAT m F [view E; supply n']
            (EWP e2 @ E <| (ι, Ψ) |> {{ Φ }} ∗
            (match μ with
             | None => state_interp (σ2, πp)
             | Some (ι', e') =>
                 ∃ φ' γ, state_interp (σ2, <[ι':=γ]> πp) ∗
                         saved_prop.saved_pred_own γ DfracDiscarded φ' ∗
                         EWP e' @ E <| (ι', ⊥) |> {{ λ o : outcome2 val exn, □ φ' o }}
             end)).
  Proof.
    intros Hstep Hsat. eapply SAT_mono in Hsat; last first.
    { iIntros "[HSI Hwp]". rewrite ewp_unfold /ewp_pre.
      rewrite (thread_step_is_WPStep _ _ _ _ _ _ _ Hstep).
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

  Lemma ewp_join_inv {A X} γ φ σ πp ι' (k : _ → micro A X) ι Ψ Φ E o :
    ⌜πp !! ι' = Some γ⌝ -∗
    saved_prop.saved_pred_own γ DfracDiscarded φ -∗
    □ φ o -∗
    state_interp (σ, πp) -∗
    EWP Stop CJoin ι' k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, πp) ∗ EWP k o @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hlookup Hsaved Hφ Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state.
    iMod "Hwp". rewrite Hlookup.
    iSpecialize ("Hwp" with "Hsaved Hφ").
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

  Lemma threadpool_thread_step (σ1 σ2 : store) (π1 π2 : thpool) :
    threadpool_step (σ1, π1) (σ2, π2) →
    (∃ ι ι' k m,
        π1 !! ι = Some (Stop CJoin ι' k) ∧
        attempt_join ι' π1 k = Some m ∧
        σ1 = σ2 ∧
        π2 = <[ι:=m]>π1) ∨
    ∃ (ι : thread) (m m' : microvx) μ,
      π1 !! ι = Some m ∧
      π2 !! ι = Some m' ∧
      thread_step (σ1, m, ι, dom π1) (σ2, m', μ) ∧
      match μ with
      | None => π2 = <[ι:=m']>π1
      | Some (ι', mf) => <[ι:=m']> π1 !! ι' = None ∧ π2 = <[ι':=mf]>(<[ι:=m']>π1)
      end.
  Proof.
    inversion 1.
    - right.
      eapply BaseS in H5.
      exists ι, m, m', None.
      split; first assumption.
      split; first apply lookup_insert.
      split; first eassumption.
      reflexivity.
    - right.
      exists ι, (Stop CFork (v1, v2) k), (continue k (VThread ι')), (Some (ι', call v1 v2)).
      split; first assumption.
      split; first (rewrite lookup_insert_ne; first apply lookup_insert).
      intros ->; rewrite H5 in H3; discriminate.
      split.
      + apply ForkS. apply (not_elem_of_dom π1). assumption.
      + split; last reflexivity.
        rewrite lookup_insert_ne. assumption.
        intros ->. rewrite H5 in H3; discriminate.
    - left. repeat eexists; eassumption.
    - right.
      exists ι, (Stop CSelf () k), (continue k (VThread ι)), None.
      split; first assumption.
      split; first apply lookup_insert.
      split; last reflexivity.
      apply SelfS.
  Qed.

  Lemma WPTP_insert_delete ι π1 πp m' γ φ :
    ⌜πp !! ι = Some (γ, φ)⌝ -∗
    WPTP (delete ι π1) (delete ι πp) -∗
    (saved_pred_own γ DfracDiscarded φ ∗ EWP m' <|(ι, ⊥)|> {{ λ o, □ φ o }}) -∗
    WPTP (<[ι:=m']> π1) πp.
  Proof.
    iIntros "%Hlookup Hwps Hwp".
    replace πp with (<[ι:=(γ, φ)]>πp) by apply (insert_id πp ι (γ, φ) Hlookup).
    iApply big_sepM2_insert_delete.
    replace πp with (<[ι:=(γ, φ)]>πp) at 2 by apply (insert_id πp ι (γ, φ) Hlookup).
    iFrame.
  Qed.

  Lemma WPTP_insert_post_delete ι π1 πp γ φ o :
    ⌜πp !! ι = Some (γ, φ)⌝ -∗
    ⌜π1 !! ι = Some (inject2 o)⌝ -∗
    WPTP (delete ι π1) (delete ι πp) -∗
    saved_pred_own γ DfracDiscarded φ -∗
    (|={⊤}=> □ φ o) -∗
    WPTP π1 πp.
  Proof.
    iIntros "%Hlookup_p %Hlookup Hwps Hsaved Hwp".
    replace πp with (<[ι:=(γ, φ)]>πp) by apply (insert_id πp ι (γ, φ) Hlookup_p).
    replace π1 with (<[ι:=inject2 o]>π1) by apply (insert_id π1 ι (inject2 o) Hlookup).
    iApply big_sepM2_insert_delete.
    replace πp with (<[ι:=(γ, φ)]>πp) at 2 by apply (insert_id πp ι (γ, φ) Hlookup_p).
    replace π1 with (<[ι:=inject2 o]>π1) at 2 by apply (insert_id π1 ι (inject2 o) Hlookup).
    iFrame.
    iApply ewp_fupd. iMod "Hwp". iModIntro.
    iApply ewp_outcome2.
    iAssumption.
  Qed.

  Lemma wptp_tstep (π1 : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))) σ1 σ2 m m' ι μ :
    ⌜π1 !! ι = Some m⌝ -∗
    (state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp) -∗
    ⌜thread_step (σ1, m, ι, dom πp) (σ2, m', μ)⌝ ={⊤}[∅]▷=∗
     match μ with
     | None => state_interp (σ2, fst <$> πp) ∗ WPTP (<[ι:=m']>π1) πp
     | Some (ι', mforked) => ∃ (φ : outcome2 val exn → iProp Σ) γ,
       state_interp (σ2, <[ι':=γ]>(fst <$> πp)) ∗ WPTP (<[ι':=mforked]> (<[ι:=m']>π1)) (<[ι':=(γ, φ)]>πp)
     end.
  Proof.
    iIntros "%Hlookup [Hsi Hwps] %Hstep".
    iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
    assert (dom πp ≡ dom π1) as Hdomequiv by (rewrite Hdomeq; reflexivity).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps")
      as "(%γ & %φ & %Hlookup_p & #Hsaved & Hwp & Hwps)".
    iPoseProof (ewp_step with "Hsi Hwp") as "Hwp". { rewrite dom_fmap_L. apply Hstep. }
    iMod "Hwp"; ewp_mask_elim; iMod "Hwp". ewp_mask_elim; iMod "Hwp" as "[Hwp Hrest]".
    iModIntro.
    inversion Hstep; subst.
    - iFrame.
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps [$]").
    - iDestruct "Hrest" as "(%φ' & %γ' & Hsi & #Hsaved' & Hcall)".
      iFrame. iExists φ'.
      iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "Hwps".
      iApply big_sepM2_insert.
      rewrite lookup_insert_ne. apply not_elem_of_dom. rewrite Hdomeq. assumption.
      { intros ->.
        rewrite (not_elem_of_dom_1 _ _ H0) in Hlookup_p.
        discriminate Hlookup_p. }
      apply not_elem_of_dom. assumption.
      iFrame. iApply "Hsaved'".
    - iFrame.
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps [Hsaved Hwp]").
      iFrame. iApply "Hsaved".
  Qed.

  Fixpoint add_posts {A : Type} l (πp : gmap thread A) :=
    match l with
    | [] => πp
    | (ι, φ) :: t => <[ι:=φ]>(add_posts t πp)
    end.

  Lemma add_posts_app {A : Type} l l' (πp : gmap thread A) :
    add_posts (l' ++ l) πp = add_posts l' (add_posts l πp).
  Proof.
    induction l' as [ | [ι' φ'] l'].
    - reflexivity.
    - simpl. f_equal.
      apply IHl'.
  Qed.

  Lemma wptp_step (π1 π2 : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))) σ1 σ2 :
    (state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp) -∗
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ ={⊤}[∅]▷=∗
    (∃ (l : list (thread * (gname * (outcome2 val exn → iProp Σ)))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, fst <$> (add_posts l πp)) ∗ WPTP π2 (add_posts l πp)).
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iCombine "Hsi Hwps" as "Hwps".
    have Hsteps := threadpool_thread_step σ1 σ2 π1 π2 Hstep.
    destruct Hsteps; last first.
    - (* Case: [threadpool_step] is immitated by a [thread_step]. *)
      destruct H as (ι & e & e' & μ & Hlookup & Hlookup' & Htstep & Hμ).
      iPoseProof (wptp_tstep $! Hlookup with "Hwps") as "Hwps".
      rewrite <- Hdomeq in Htstep. iSpecialize ("Hwps" $! Htstep).
      iMod "Hwps". iModIntro. iNext. iMod "Hwps".
      destruct μ as [[ι' mforked] | ]; last first.
      + (* Subcase: the step did not fork any new threads. *)
        subst π2. iModIntro.
        iDestruct "Hwps" as "(Hsi & Hwps)".
        iExists []. iFrame.
        iPureIntro. intros ι' Hin. by apply not_elem_of_nil in Hin.
      + (* Subcase: the step results in a forked thread. *)
        destruct Hμ as [Hfresh ->].
        iDestruct "Hwps" as "(%φ' & %γ & Hsi & Hwps)".
        iExists [(ι', (γ, φ'))]. iModIntro.
        simpl add_posts; rewrite fmap_insert.
        iFrame.
        iPureIntro. intros ? Hin. apply elem_of_list_singleton in Hin as ->.
        simpl. rewrite Hdomeq. apply not_elem_of_dom.
        assert (ι ≠ ι').
        { intros ->. rewrite lookup_insert in Hfresh. discriminate Hfresh. }
        rewrite lookup_insert_ne in Hfresh; last assumption.
        assumption.
    - (* Case: [threadpool_step] is a join. *)
      destruct H as (ι & ι' & k & e & Hlookup & Hattempt & -> & ->).
      iDestruct "Hwps" as "(Hsi & Hwps)".
      iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%γ & %φ & %Hlookup_p & Hsaved & Hwp & Hwps)".
      case (πp !! ι') eqn:Hlookup_p'.
      + (* Case: the join was successful. *)
        assert (∃ o, π1 !! ι' = Some (inject2 o) ∧ e = k o) as (o & Hlookup' & ->).
        { unfold attempt_join in Hattempt.
          assert (is_Some (π1 !! ι')) as [e' Hlookup'].
          { apply elem_of_dom. setoid_rewrite <- Hdomeq.
            apply (elem_of_dom πp ι').
            eexists; eassumption. }
          rewrite Hlookup' in Hattempt.
          destruct e'; inversion Hattempt; try discriminate;
            rewrite Hlookup'.
          exists (O2Ret a). split; reflexivity.
          exists (O2Throw e0). split; reflexivity. }
        assert (ι ≠ ι') as Hneq.
        { intros ->. rewrite Hlookup' in Hlookup; inversion Hlookup. destruct o; discriminate. }
        assert (delete ι π1 !! ι' = Some (inject2 o)) by (rewrite lookup_delete_ne; assumption).
        iPoseProof (WPTP_extract_wp (delete ι π1) (delete ι πp) ι' $! H with "Hwps")
          as "(%γ' & %φ' & %Hlookup_p'' & #Hsaved' & Ho & Hwps)".
        assert (πp !! ι' = Some (γ', φ')) as Hπp.
        { by rewrite lookup_delete_ne in Hlookup_p''; last apply Hneq. }
        iPoseProof (ewp_outcome2_inv with "Ho") as ">#Ho".
        iPoseProof (ewp_join_inv $! _ with "Hsaved' [$] Hsi Hwp") as "Hwp".
        iMod "Hwp". iModIntro. iNext. iMod "Hwp". iModIntro.
        iExists []. simpl. iDestruct "Hwp" as "($ & Hwp)".
        iPoseProof (WPTP_insert_post_delete $! Hlookup_p'' H with "Hwps Hsaved' Ho") as "Hwps".
        iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "$".
        iPureIntro. intros ? Hin. by apply not_elem_of_nil in Hin.
      + ewp_unfold (Stop CJoin ι' k). spec_state.
        iMod "Hwp".
        assert ((fst <$> πp) !! ι' = None) as Hnin.
        { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom. assumption. }
        setoid_rewrite Hnin.
        by repeat iMod "Hwp".
        Unshelve. rewrite lookup_fmap. rewrite Hπp. reflexivity.
  Qed.

  Lemma not_elem_of_add_posts {A} ι l (πp : gmap thread A) :
    ι ∉ dom (add_posts l πp) →
    ι ∉ fst <$> l ∧ ι ∉ dom πp.
  Proof.
    induction l as [| [ι' a] l IH].
    - simpl.
      intros Hnin.
      split; [ apply not_elem_of_nil | assumption ].
    - simpl. rewrite dom_insert.
      rewrite not_elem_of_union not_elem_of_singleton.
      intros [Hnhead Hndom].
      destruct (IH Hndom) as [Hnlist Hndom'].
      rewrite not_elem_of_cons.
      auto.
  Qed.

  Lemma wptp_steps k π1 π2 σ1 σ2 πp :
    state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp -∗
    ⌜threadpool_steps k (σ1, π1) (σ2, π2)⌝ ={⊤}[∅]▷=∗^k
    (∃ (l : list (thread * (gname * (outcome2 val exn → iProp Σ)))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, fst <$> add_posts l πp) ∗ WPTP π2 (add_posts l πp)).
  Proof.
    induction k as [|k IH] in  πp, π1, σ1 |-*; iIntros "Hwps %Hsteps".
    - inversion_clear Hsteps. simpl.
      iExists []. iFrame.
      iPureIntro; simpl; intros ? HF.
      by apply not_elem_of_nil in HF.
    - inversion_clear Hsteps as [|?? [σ1' π1']].
      simpl.
      iPoseProof (wptp_step with "Hwps") as "Hwps".
      iSpecialize ("Hwps" $! H).
      iMod "Hwps". iModIntro. iNext. iMod "Hwps" as "(%l & %Hl & Hwps)". iModIntro.
      iPoseProof (IH with "Hwps") as "Hwps".
      iSpecialize ("Hwps" $! H0).
      iApply (step_fupdN_wand with "Hwps").
      iIntros "(%l' & %Hl' & Hwps)".
      iExists (l' ++ l).
      rewrite add_posts_app.
      iFrame.
      iPureIntro.
      intros ι' Hin.
      rewrite fmap_app in Hin; apply elem_of_app in Hin.
      destruct Hin.
      + specialize (Hl' ι' H1).
        apply not_elem_of_add_posts in Hl' as [_ Hndom].
        assumption.
      + apply Hl, H1.
  Qed.

  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy k σ1 σ2 π2 ι e Φ :
    (∃ γ, state_interp (σ1, {[ι:=γ]}) ∗
          saved_pred_own γ DfracDiscarded (λ o, ⌜Φ o⌝)%I ∗
          EWP e @ ⊤ <| (ι, ⊥) |> {{ (λ o, □ ⌜Φ o⌝)%I }}) -∗
    ⌜threadpool_steps k (σ1, {[ι:=e]}) (σ2, π2)⌝ ={⊤}[∅]▷=∗^k
    (∀ ι' e, ⌜π2 !! ι' = Some e⌝ ={⊤}[∅]▷=∗
      ⌜not_stuck e σ2 (dom π2)⌝ ∗
      (∀ o, ⌜π2 !! ι = Some (inject2 o)⌝ -∗ |={⊤}=> □ ⌜Φ o⌝)).
  Proof.
    iIntros "(%γ & Hsi & Hwps) %Hsteps".
    rewrite wp_wptp. iCombine "Hsi Hwps" as "Hwps".
    remember {[ι := (γ, λ o, ⌜Φ o⌝)%I]} as πp.
    replace {[ι:=γ]} with (fst <$> πp) by (rewrite Heqπp map_fmap_singleton; reflexivity).
    iPoseProof (wptp_steps with "Hwps") as "Hwps".
    iSpecialize ("Hwps" $! Hsteps).
    iApply (step_fupdN_wand with "Hwps").
    iIntros "(%l & %Hl & Hsi & Hwps)".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iIntros (ι' e' Hlookup).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%γ' & %φ' & %Hlookup_p & Hsaved & Hwp & Hwps)".
    iCombine "Hsi Hwp" as "Hwp".
    iPoseProof (EWP_not_stuck_post with "Hwp") as "Hwp".
    rewrite dom_fmap_L Hdomeq.
    iMod "Hwp". iModIntro. iNext. iMod "Hwp" as "($ & Hpost)".
    assert (add_posts l πp !! ι = Some (γ, (λ o, ⌜Φ o⌝)%I)).
      { specialize (Hl ι).
        clear Hdomeq.
        induction l in Hl |-*.
        - simpl. rewrite Heqπp lookup_singleton. reflexivity.
        - destruct a; simpl.
          assert (ι ≠ t). { intros ->. apply Hl. rewrite fmap_cons elem_of_cons. by left.
                            rewrite Heqπp dom_singleton. by apply elem_of_singleton.  }
          rewrite lookup_insert_ne; last (symmetry; assumption).
          apply IHl. intro Hin. apply Hl.
          rewrite fmap_cons elem_of_cons. by right. }
    case (decide (ι' = ι)) as [-> | Hneq].
    - iIntros "!>" (o Hlookup').
      rewrite H in Hlookup_p.
      rewrite Hlookup' in Hlookup.
      inversion Hlookup_p; inversion Hlookup; subst.
      iApply ("Hpost" $! o eq_refl).
    - iModIntro.
      iIntros (o Hlookup_og).
      assert (delete ι' π2 !! ι = Some (inject2 o)).
      { rewrite lookup_delete_ne; assumption. }
      iClear "Hsaved Hpost". clear γ' φ' Hlookup e' Hlookup_p.
      iPoseProof (WPTP_extract_wp $! H0 with "Hwps") as "(%γ' & %φ' & %Hlookup_p & Hsaved & Hwp & Hwps)".
      assert (delete ι' (add_posts l πp) !! ι = Some (γ, (λ o, ⌜Φ o⌝)%I)).
      { rewrite lookup_delete_ne; assumption. }
      rewrite H1 in Hlookup_p.
      inversion Hlookup_p; subst.
      iApply (ewp_outcome2_inv with "Hwp").
  Qed.

  Lemma ewp_adequacy m F n ι e σ1 σ2 π2 k Φ :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (∃ γ, state_interp (σ1, {[ι:=γ]}) ∗
       saved_pred_own γ DfracDiscarded (λ o, ⌜Φ o⌝)%I ∗
       EWP e @ ⊤ <| (ι, ⊥) |> {{ (λ o, ⌜Φ o⌝)%I }}) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    threadpool_steps k (σ1, {[ι := e]}) (σ2, π2) →
    (* then no thread is stuck *)
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hsat Hsteps.
    eapply SAT_mono with
      (Q:=(∃ γ : gname, state_interp (σ1, {[ι := γ]}) ∗
                          saved_pred_own γ DfracDiscarded (λ o : outcome2 val exn, ⌜Φ o⌝) ∗
                          EWP e <|(ι, ⊥)|> {{ λ o : outcome2 val exn, □ ⌜Φ o⌝ }})%I) in Hsat; last first.
    { iIntros "(%γ & Hsi & Hsaved & Hwp)".
      iExists γ. iFrame "Hsi Hsaved".
      iApply (ewp_mono with "Hwp").
      iIntros (o HΦ). iFrame "%". }
    eapply SAT_mono in Hsat; last first.
    iIntros "Hwps".
    iPoseProof (wptp_adequacy k σ1 σ2 π2 with "Hwps") as "Hx".
    iSpecialize ("Hx" $! Hsteps). iExact "Hx".
    apply SAT_elim_iterated in Hsat; last first.
    { intros P HsatP.
      by apply SAT_fupd, SAT_later, SAT_fupd in HsatP. }
    split.
    - intros ι' e' Hlookup.
      eapply SAT_mono in Hsat; last first.
      { iIntros "Hx". iSpecialize ("Hx" $! ι' e' Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      eapply SAT_mono in Hsat; last first.
      { iIntros "[Hns Ho]". iCombine "Ho Hns" as "Hx". iExact "Hx". }
      rewrite -SAT_frame_cons in Hsat.
      apply SAT_elim in Hsat.
      by apply Hsat.
    - intros o Hlookup.
      eapply SAT_mono in Hsat; last first.
      { iIntros "Hx". iSpecialize ("Hx" $! ι (inject2 o) Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      rewrite -SAT_frame_cons in Hsat.
      eapply SAT_mono in Hsat; last first.
      { iIntros "HΦ".
        iSpecialize ("HΦ" $! o Hlookup). iExact "HΦ". }
      apply SAT_fupd, SAT_pers in Hsat.
      apply SAT_elim in Hsat.
      by apply Hsat.
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
Lemma SAT_ewp_adequacy `{invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 σ2 π2 (e : micro val exn) ι n k P Φ :
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS_gen HasNoLc Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: osirisGS Σ := I x in
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp (σ1, ∅) ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e @ ⊤ <| (ι, ⊥) |> {{ λ o, ⌜Φ o⌝  }}) →
  (* then any k-step execution is safe: *)
  threadpool_steps k (σ1, {[ι := e]}) (σ2, π2) →
  (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
  (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
Proof.
  intros Halloc Hwp Hsteps.
  pose proof (SAT_intro (Σ := Σ)) as Hsat.
  eapply SAT_alloc_fancy_updates in Hsat as [Hi Hsat].
  eapply (Halloc Hi True%I) in Hsat as (x & Hsat); eauto; simpl in *.
  eapply SAT_mono in Hsat; last first.
  { iIntros "((Hsi & Hti) & HP)". iPoseProof (Hwp x with "HP") as "Hwp".
    iCombine "Hsi Hti Hwp" as "Hx". iExact "Hx". }
  eapply (@ewp_adequacy Σ (I x)), Hsteps.
  apply SAT_bupd.
  eapply SAT_mono, Hsat.
  { iIntros "(Hsi & Hti & Hwp)".
    iMod (saved_pred_alloc (λ o, ⌜Φ o⌝)%I DfracDiscarded) as "(%γ & Hsaved)"; first done.
    iMod (gen_heap_alloc ∅ ι γ with "Hti") as "(Hti & Hpointsto)"; first apply lookup_empty.
    iModIntro. iFrame. }
Qed.

Lemma osiris_initial_allocation `{!osirisGpreS Σ} (ι : thread) σ (_ : invGS_gen HasNoLc Σ) (F : iProp Σ) (P: outcome2 val exn → Prop) :
  SAT Alloc F [view ⊤; supply 0] True →
  ∃ (h: osirisGS Σ),
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in
    SAT Alloc F [view ⊤; supply 0] (state_interp (σ, ∅)).
Proof.
  intros Hsat.
  eapply SAT_frame_resource with (R := view _) in Hsat; last apply _.
  eapply SAT_frame_resource with (R := supply _) in Hsat; last apply _.
  eapply (SAT_gen_heap_init σ) in Hsat as [Hgen Hsat].
  eapply (SAT_gen_heap_init ∅) in Hsat as [Hgen' Hsat].
  do 2 apply SAT_unframe_resource in Hsat.
  pose (hg := (@OsirisGS Σ _ _ Hgen Hgen')).
  exists hg.
  eapply SAT_mono; last apply Hsat.
  iIntros "(Hgen' & Hpts' & Hmeta' & Hgen & Hpts & Hmeta)".
  by iFrame.
Qed.

(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations under open gFunctors [Σ]. *)

  Definition osiris_adequacy Σ `{!osirisGpreS Σ} (e : micro val exn) ι σ1 π2 σ2 k Φ :
    (* If we can show [EWP e1 {{ True }}] with the ghost state provided by [Σ]. *)
    (∀ `{!osirisGS Σ}, ⊢ EWP e @ ⊤ <|(ι, ⊥)|> {{ λ o, ⌜Φ o⌝ }}) →
    (* then any k-step execution is safe: *)
    threadpool_steps k (σ1, {[ι := e]}) (σ2, π2) →
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hwp.
    eapply SAT_ewp_adequacy with (X := osirisGS Σ) (P := λ _, bi_pure True).
    - intros iv F Hsat_init.
      have [h Hsat] := (@osiris_initial_allocation Σ osirisGpreS0 ι σ1 iv F Φ Hsat_init).
      exists h.
      eapply SAT_mono, Hsat.
      apply bi.sep_True_2.
    - apply Hwp.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for a closed list of gFunctors. *)

  (* Example of an adequacy statement instantiated with a specific set of [gFunctors]. *)

  Definition osiris_adequacy_closed (e : micro val exn) ι σ1 π2 σ2 k Φ :
    (∀ `{!osirisGS osirisΣ}, ⊢ EWP e @ ⊤ <|(ι, ⊥)|> {{ λ o, ⌜Φ o⌝ }}) →
    threadpool_steps k (σ1, {[ι :=e]}) (σ2, π2) →
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hwp. eapply osiris_adequacy, Hwp. apply _.
  Qed.

End adequacy.
