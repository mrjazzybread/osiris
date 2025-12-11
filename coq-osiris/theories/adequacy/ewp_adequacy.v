From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.program_logic Require Import thread_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Definition WPTP `{!osirisGS Σ} (π : thpool) (πp : post_map Σ): iProp Σ :=
  ([∗ map] ι ↦ m; φ ∈ π; πp, EWP m @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }}).

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

Definition not_stuck {Σ A E} (m : micro A E) σ (π : post_map Σ) :=
  is_final m ∨ can_progress σ π m ∨ is_join m.

Lemma wp_wptp `{!osirisGS Σ} ι m φ :
  EWP m @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }} ={⊤}=∗ WPTP {[ι := m ]} {[ι := φ]}.
Proof.
  unfold WPTP.
  rewrite big_sepM2_singleton.
  by iIntros "? !>".
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

Lemma wptp_extract_wp `{!osirisGS Σ} m F Rs π πp ι e :
  π !! ι = Some e →
  SAT m F Rs (WPTP π πp) →
  ∃ φ, πp !! ι = Some φ ∧ SAT m F Rs (EWP e @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }} ∗ WPTP (delete ι π) (delete ι πp))%I.
Proof.
  intros Hlookup Hsat.
  eapply wptp_dom in Hsat as Hdomeq.
  assert (∃ φ, πp !! ι = Some φ) as [φ Hlookup_p].
  { eapply (elem_of_dom πp ι). rewrite Hdomeq. apply elem_of_dom. eexists; eassumption. }
  exists φ; split; first assumption.
  eapply SAT_mono, Hsat.
  iIntros "Hwps".
  iPoseProof (big_sepM2_delete _ _ _ _ _ _ Hlookup Hlookup_p with "Hwps") as "[Hwp Hwps]".
  iFrame.
Qed.

Lemma WPTP_dom `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp ≡ dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  iPureIntro. by rewrite Hdomeq.
Qed.

Lemma WPTP_extract_wp `{!osirisGS Σ} π πp ι e :
  ⌜π !! ι = Some e⌝ -∗
  WPTP π πp -∗
  ∃ φ, ⌜πp !! ι = Some φ⌝ ∗ EWP e @ ⊤ <| (ι, ⊥) |> {{ λ o, □ φ o }} ∗ WPTP (delete ι π) (delete ι πp).
Proof.
  iIntros "%Hlookup Hwps".
  iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
  assert (∃ φ, πp !! ι = Some φ) as [φ Hlookup_p].
  { eapply (elem_of_dom πp ι).
    rewrite Hdomeq. apply elem_of_dom. eexists; eassumption. }
  iExists φ; iSplit; first (iPureIntro; assumption).
  iPoseProof (big_sepM2_delete _ _ _ _ _ _ Hlookup Hlookup_p with "Hwps") as "[Hwp Hwps]".
  iFrame.
Qed.

Lemma WPTP_extract_posts `{!osirisGS Σ} π πp :
  WPTP π πp ⊢ ∀ ι o, ⌜π !! ι ≫= is_outcome = Some o⌝ -∗ ∃ φ, ⌜πp !! ι = Some φ⌝ ∗ (|={⊤}=> □ φ o).
Proof.
  iIntros "Hwps" (ι o Hlookup).
  unfold mbind in Hlookup.
  apply bind_Some in Hlookup.
  destruct Hlookup as (m & Hlookup & Houtcome).
  iPoseProof (big_sepM2_delete_l with "Hwps") as "(%φ & Hlookup_p & Hwp & Hwps)".
  apply Hlookup.
  iFrame.
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
    @not_stuck Σ A X e σ πp.
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
      eapply SAT_mono with (Q := (|={E, ∅}=> ⌜can_progress σ πp e⌝)%I)
                           in Hsat.
      { eapply SAT_fupd, SAT_elim in Hsat.
        by left. }
      iIntros "[Hsi Hwp]".
      spec_state. iModIntro.
     by iPureIntro.
    - right. done.
  Qed.

  Lemma EWP_not_stuck {A X} E (e : micro A X) ι σ πp Φ :
    state_interp (σ, πp) ∗ EWP e @ E <| (ι, ⊥) |> {{ Φ }} ={E}[∅]▷=∗
    ⌜@not_stuck Σ A X e σ πp⌝.
  Proof.
    iIntros "(Hsi & Hwp)". rewrite /not_stuck.
    ewp_unfold e.
    ewp_case e; simpl.
    - ewp_mask_intro "Hmod". iNext. iMod "Hmod". iModIntro.
      iPureIntro; left; by destruct o.
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
        epose proof (ForkS σ ι πp v1 v2 k (fresh (dom πp)) _).
        Unshelve.
        spec_step.
        iModIntro. iNext. iMod "Hwp". iModIntro.
        iPureIntro.
        right; left.
        apply can_progress_fork.
        apply (not_elem_of_dom πp). apply is_fresh. }
      destruct Hstep as [Hstep|Hstep].
      { destruct Hstep as (u & k & ->).
        epose proof (SelfS σ πp ι u k).
        spec_step.
        iModIntro. iNext. iMod "Hwp". iModIntro.
        iPureIntro.
        right; left.
        apply can_progress_self. }
      destruct Hstep as ([??] & ?).
      pose proof (BaseS e σ ι m s πp H).
      spec_step. iModIntro. iNext. iMod "Hwp". iModIntro.
      iPureIntro.
      right; left.
      assumption.
    - spec_state.
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iModIntro.
      iPureIntro.
      by right; right.
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

  Lemma sat_wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 πp e2 σ2 μ Φ n :
    thread_step (σ1, e1, ι, πp) (σ2, e2, μ) →
    SAT m F [view E; supply n]
      (state_interp (σ1, πp) ∗ EWP e1 @ E <| (ι, Ψ) |> {{ Φ }}) →
    ∃ n', SAT m F [view E; supply n']
            (EWP e2 @ E <| (ι, Ψ) |> {{ Φ }} ∗
            (match μ with
             | None => state_interp (σ2, πp)
             | Some (ι', e') =>
                 ∃ φ', state_interp (σ2, <[ι':=φ']> πp) ∗
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

  Lemma ewp_join_inv {A X} φ σ πp ι' (k : _ → micro A X) ι Ψ Φ E o :
    ⌜πp !! ι' = Some φ⌝ -∗
    □ φ o -∗
    state_interp (σ, πp) -∗
    EWP Stop CJoin ι' k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, πp) ∗ EWP k o @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hlookup Hφ Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state.
    iMod "Hwp". rewrite Hlookup.
    iSpecialize ("Hwp" with "Hφ").
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

  Lemma threadpool_thread_step (σ1 σ2 : store) (π1 π2 : thpool) (πp : post_map Σ) :
    dom πp ≡ dom π1 →
    threadpool_step (σ1, π1) (σ2, π2) →
    (∃ ι ι' k m,
        π1 !! ι = Some (Stop CJoin ι' k) ∧
        attempt_join ι' π1 k = Some m ∧
        σ1 = σ2 ∧
        π2 = <[ι:=m]>π1) ∨
    ∃ (ι : thread) (m m' : microvx) μ,
      π1 !! ι = Some m ∧
      π2 !! ι = Some m' ∧
      thread_step (σ1, m, ι, πp) (σ2, m', μ) ∧
      match μ with
      | None => π2 = <[ι:=m']>π1
      | Some (ι', mf) => <[ι:=m']> π1 !! ι' = None ∧ π2 = <[ι':=mf]>(<[ι:=m']>π1)
      end.
  Proof.
    intros Hdomeq.
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
      assert (πp !! ι' = None).
      { apply (not_elem_of_dom_1 πp ι'). rewrite Hdomeq. apply not_elem_of_dom_2. assumption. }
      split.
      + apply ForkS. assumption.
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

  Lemma WPTP_insert_delete ι π1 πp m' φ :
    ⌜πp !! ι = Some φ⌝ -∗
    WPTP (delete ι π1) (delete ι πp) -∗
    EWP m' <|(ι, ⊥)|> {{ λ o, □ φ o }} -∗
    WPTP (<[ι:=m']> π1) πp.
  Proof.
    iIntros "%Hlookup Hwps Hwp".
    replace πp with (<[ι:=φ]>πp) by apply (insert_id πp ι φ Hlookup).
    iApply big_sepM2_insert_delete.
    replace πp with (<[ι:=φ]>πp) at 2 by apply (insert_id πp ι φ Hlookup).
    iFrame.
  Qed.

  Lemma WPTP_insert_post_delete ι π1 πp φ o :
    ⌜πp !! ι = Some φ⌝ -∗
    ⌜π1 !! ι = Some (inject2 o)⌝ -∗
    WPTP (delete ι π1) (delete ι πp) -∗
    (|={⊤}=> □ φ o) -∗
    WPTP π1 πp.
  Proof.
    iIntros "%Hlookup_p %Hlookup Hwps Hwp".
    replace πp with (<[ι:=φ]>πp) by apply (insert_id πp ι φ Hlookup_p).
    replace π1 with (<[ι:=inject2 o]>π1) by apply (insert_id π1 ι (inject2 o) Hlookup).
    iApply big_sepM2_insert_delete.
    replace πp with (<[ι:=φ]>πp) at 2 by apply (insert_id πp ι φ Hlookup_p).
    replace π1 with (<[ι:=inject2 o]>π1) at 2 by apply (insert_id π1 ι (inject2 o) Hlookup).
    iFrame.
    iApply ewp_fupd. iMod "Hwp". iModIntro.
    iApply ewp_outcome2.
    destruct o; iAssumption.
  Qed.

  Lemma wptp_tstep (π1 : thpool) (πp : post_map Σ) σ1 σ2 m m' ι μ :
    ⌜π1 !! ι = Some m⌝ -∗
    (state_interp (σ1, πp) ∗ WPTP π1 πp) -∗
    ⌜thread_step (σ1, m, ι, πp) (σ2, m', μ)⌝ ={⊤}[∅]▷=∗
     match μ with
     | None => state_interp (σ2, πp) ∗ WPTP (<[ι:=m']>π1) πp
     | Some (ι', mforked) => ∃ (φ : outcome2 val exn → iProp Σ),
       state_interp (σ2, <[ι':=φ]>πp) ∗ WPTP (<[ι':=mforked]> (<[ι:=m']>π1)) (<[ι':=φ]>πp)
     end.
  Proof.
    iIntros "%Hlookup [Hsi Hwps] %Hstep".
    iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
    assert (dom πp ≡ dom π1) as Hdomequiv by (rewrite Hdomeq; reflexivity).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
    iPoseProof (ewp_step with "Hsi Hwp") as "Hwp". apply Hstep.
    iMod "Hwp"; ewp_mask_elim; iMod "Hwp". ewp_mask_elim; iMod "Hwp" as "[Hwp Hrest]".
    iModIntro.
    inversion Hstep; subst.
    - iFrame.
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps Hwp").
    - iDestruct "Hrest" as "(%φ' & Hsi & Hcall)".
      iFrame.
      iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps Hwp") as "Hwps".
      iApply big_sepM2_insert.
      rewrite lookup_insert_ne. apply not_elem_of_dom. rewrite Hdomeq. apply not_elem_of_dom. assumption.
      intros ->. rewrite H0 in Hlookup_p; discriminate Hlookup_p.
      assumption.
      iFrame.
    - iFrame.
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps Hwp").
  Qed.

  Fixpoint add_posts l (πp : post_map Σ) :=
    match l with
    | [] => πp
    | (ι, φ) :: t => <[ι:=φ]>(add_posts t πp)
    end.

  Lemma add_posts_app l l' πp :
    add_posts (l' ++ l) πp = add_posts l' (add_posts l πp).
  Proof.
    induction l' as [ | [ι' φ'] l'].
    - reflexivity.
    - simpl. f_equal.
      apply IHl'.
  Qed.

  Require Import Coq.Program.Equality.


  Lemma wptp_join πp π1 ι ι' k e σ :
    ⌜dom πp ≡ dom π1⌝ -∗
    ⌜π1 !! ι = Some (Stop CJoin ι' k)⌝ -∗
    ⌜attempt_join ι' π1 k = Some e⌝ -∗
    state_interp (σ, πp) ∗ WPTP π1 πp ={⊤}[∅]▷=∗
        (state_interp (σ, πp) ∗ WPTP (<[ι:=e]> π1) πp).
  Proof.
    iIntros (Hdomequiv Hlookup Hattempt) "[Hsi Hwp]".
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwp") as "(%φ & %Hlookup_p & Hwp & Hwps)".
    case (πp !! ι') eqn:Hlookup_p'.
    + (* Case: the join was successful. *)
      assert (∃ o, π1 !! ι' = Some (inject2 o) ∧ e = k o) as (o & Hlookup' & ->).
      { unfold attempt_join in Hattempt.
        assert (is_Some (π1 !! ι')) as [e' Hlookup'].
        { apply elem_of_dom. rewrite <- Hdomequiv. apply (elem_of_dom πp ι'). eexists; eassumption. }
        rewrite Hlookup' in Hattempt.
        destruct e'; inversion Hattempt; try discriminate;
          rewrite Hlookup'.
        exists (O2Ret a). split; reflexivity.
        exists (O2Throw e0). split; reflexivity. }
      assert (ι ≠ ι') as Hneq.
      { intros ->. rewrite Hlookup' in Hlookup; inversion Hlookup. destruct o; discriminate. }
      assert (delete ι π1 !! ι' = Some (inject2 o)) by (rewrite lookup_delete_ne; assumption).
      iPoseProof (WPTP_extract_wp (delete ι π1) (delete ι πp) ι' $! H with "Hwps")
          as "(%φ' & %Hlookup_p'' & Ho & Hwps)".
      assert (πp !! ι' = Some φ') as Hπp.
      { by rewrite lookup_delete_ne in Hlookup_p''; last apply Hneq. }
      rewrite Hπp in Hlookup_p'; inversion Hlookup_p'; subst u.
      iPoseProof (ewp_outcome2_inv with "Ho") as ">#Ho".
      ewp_unfold (Stop CJoin ι' k). spec_state.
      iMod "Hwp". rewrite Hπp.
      iSpecialize ("Hwp" $! o with "Ho").
      ewp_mask_elim. iMod "Hwp" as "[Hwp Hsi]".
      iModIntro. iFrame.
      iPoseProof (WPTP_insert_post_delete $! Hlookup_p'' H with "Hwps Ho") as "Hwps".
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps Hwp").
    + ewp_unfold (Stop CJoin ι' k). spec_state.
      iMod "Hwp".
      rewrite Hlookup_p'.
      by repeat iMod "Hwp".
  Qed.

  Lemma wptp_step (π1 π2 : thpool) (πp : post_map Σ) σ1 σ2 :
    (state_interp (σ1, πp) ∗ WPTP π1 πp) -∗
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ ={⊤}[∅]▷=∗
    (∃ l, state_interp (σ2, add_posts l πp) ∗ WPTP π2 (add_posts l πp)).
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomequiv".
    iCombine "Hsi Hwps" as "Hwps".
    have Hsteps := threadpool_thread_step σ1 σ2 π1 π2 πp Hdomequiv Hstep.
    destruct Hsteps; last first.
    - (* Case: [threadpool_step] is immitated by a [thread_step]. *)
      destruct H as (ι & e & e' & μ & Hlookup & Hlookup' & Htstep & Hμ).
      iPoseProof (wptp_tstep $! Hlookup with "Hwps") as "Hwps".
      iSpecialize ("Hwps" $! Htstep).
      iMod "Hwps". iModIntro. iNext. iMod "Hwps".
      destruct μ as [[ι' mforked] | ]; last first.
      + (* Subcase: the step did not fork any new threads. *)
        subst π2. iModIntro.
        iDestruct "Hwps" as "(Hsi & Hwps)".
        iExists []; iFrame.
      + (* Subcase: the step results in a forked thread. *)
        destruct Hμ as [Hfresh ->].
        iDestruct "Hwps" as "(%φ' & Hsi & Hwps)".
        iExists [(ι', φ')]. iModIntro. iFrame.
    - (* Case: [threadpool_step] is a join. *)
      destruct H as (ι & ι' & k & e & Hlookup & Hattempt & -> & ->).
      iPoseProof (wptp_join $! Hdomequiv Hlookup Hattempt with "Hwps") as "Hwps".
      iMod "Hwps". iModIntro. iNext. iMod "Hwps". iModIntro.
      by iExists [].
  Qed.

  Lemma wptp_steps k π1 π2 σ1 σ2 πp :
    state_interp (σ1, πp) ∗ WPTP π1 πp -∗
    ⌜threadpool_steps k (σ1, π1) (σ2, π2)⌝ ={⊤}[∅]▷=∗^k
    (∃ (l : list (thread * (outcome2 val exn → iProp Σ))),
        state_interp (σ2, add_posts l πp) ∗ WPTP π2 (add_posts l πp)).
  Proof.
    induction k as [|k IH] in  πp, π1, σ1 |-*; iIntros "Hwps %Hsteps".
    - inversion_clear Hsteps. simpl.
      by iExists [].
    - inversion_clear Hsteps as [|?? [σ1' π1']].
      simpl.
      iPoseProof (wptp_step with "Hwps") as "Hwps".
      iSpecialize ("Hwps" $! H).
      iMod "Hwps". iModIntro. iNext. iMod "Hwps" as "(%l & Hwps)". iModIntro.
      iPoseProof (IH with "Hwps") as "Hwps".
      iSpecialize ("Hwps" $! H0).
      iApply (step_fupdN_wand with "Hwps").
      iIntros "(%l' & Hwps)".
      iExists (l' ++ l).
      rewrite add_posts_app.
      iFrame.
  Qed.

  Lemma wptp_not_stuck m F n e ι σ π1 πp:
    SAT m F [view ⊤; supply n] (state_interp (σ, πp) ∗ WPTP π1 πp) →
    π1 !! ι = Some e →
    not_stuck e σ πp.
  Proof.
    intros Hsat Hlookup.
    rewrite -SAT_frame_cons in Hsat.
    eapply wptp_extract_wp in Hsat as (φ & Hlookup_p & Hsat); last eassumption.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[Hwp _]". iApply "Hwp". }
    rewrite SAT_frame_cons in Hsat.
    by eapply ewp_not_stuck in Hsat.
  Qed.

  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy k σ1 π1 σ2 π2 πp :
    state_interp (σ1, πp) ∗ WPTP π1 πp -∗
    ⌜threadpool_steps k (σ1, π1) (σ2, π2)⌝ ={⊤}[∅]▷=∗^k
    ∀ ι e,
      |={⊤}[∅]▷=>
      ⌜π2 !! ι = Some e →
       not_stuck e σ2 πp⌝.
  Proof.
    iIntros "Hwps %Hsteps".
    iPoseProof (wptp_steps with "Hwps") as "Hwps".
    iSpecialize ("Hwps" $! Hsteps).
    iApply (step_fupdN_wand with "Hwps").
    iIntros "(%l & Hsi & Hwps)" (ι e Hlookup).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
    iCombine "Hsi Hwp" as "Hwp".
    iPoseProof (EWP_not_stuck with "Hwp") as "Hwp".

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
