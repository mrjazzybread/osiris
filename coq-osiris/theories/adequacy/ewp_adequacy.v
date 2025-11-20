From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.program_logic Require Import wp_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Definition WPTP `{!osirisGS Σ} (π : thpool) : iProp Σ :=
  ([∗ map] ι ↦ s ∈ π,
     match s with
     | Active m => EWP m @ ⊤ <| (ι, ⊥) |> {{ λ _, True }}
     | Terminated o => True
     end).

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

Definition not_stuck {A E} (m : micro A E) s ι :=
  is_final m ∨ can_progress (s.1, s.2, m, ι) ∨ is_join m.

Lemma wp_wptp `{!osirisGS Σ} ι m φ :
  EWP m @ ⊤ <| (ι, ⊥) |> {{ φ }} ⊢ WPTP {[ι := (Active m) ]}.
Proof. rewrite /WPTP big_sepM_singleton.
       iIntros "Hewp". iApply (ewp_mono with "Hewp").
       iIntros (o) "Hφ". done.
Qed.

Include ewp_rules_tactics.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma ewp_not_stuck {A X} m F E (e : micro A X) ι σ π Φ n:
    SAT m F [view E; supply n] (state_interp (σ, π) ∗
                                  EWP e @ E <| (ι, ⊥) |> {{ Φ }}) →
    not_stuck e (σ, π) ι.
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
      eapply SAT_mono with (Q := (|={E, ∅}=> ⌜can_progress (σ, π, e, ι)⌝)%I)
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

  Lemma wp_postcondition {A X} m F E ι Ψ (e : micro A X) (Φ : outcome2 A X -> iProp Σ) v n:
    SAT m F [view E; supply n] (EWP e @ E <| (ι, Ψ) |> {{ Φ }}) →
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

  Lemma ewp_step {A X} σ π (m : micro A X) σ' m' E Ψ Φ :
    step (σ, m) (σ', m') ->
    state_interp (σ, π) -∗
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ', π) ∗ EWP m' @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hstep) "Hsi Hwp".
    destruct Ψ.
    eapply BaseS in Hstep.
    iMod (ewp_step _ _ _ _ _ Hstep with "Hsi Hwp") as "Hwp".
    iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp & _)".
    iApply "Hwp".
  Qed.

  (* Lemma invert_active_thread_in_wp es1 ι m : *)
  (*   WPTP es1 -∗ *)
  (*   ⌜active_thread ι es1 = Some m⌝ -∗ *)
  (*   ⌜es1 !! ι = Some (Active m)⌝ ∗ WPTP es1. *)
  (* Proof. *)
  (*   iIntros "Hwps %Hactive". *)
  (*   iPoseProof (big_sepM2_dom with "Hwps") as "%Hdom". iFrame. *)
  (*   iPureIntro. *)
  (*   rewrite /active_thread in Hactive. *)
  (*   case_eq (es1 !! ι); last (intros Heq; rewrite Heq in Hactive; discriminate). *)
  (*   intros [? | ?] Heq; rewrite Heq in Hactive; subst; last discriminate. *)
  (*   split. *)
  (*   - apply elem_of_dom. *)
  (*     rewrite -Hdom. *)
  (*     apply elem_of_dom. exists (Active m0). apply Heq. *)
  (*   - inversion Hactive; subst. reflexivity. *)
  (* Qed. *)

  Definition to_local_view : (thread_status) → thread_state :=
    λ s, match s with
         | Active _ => Alive
         | Terminated o => Dead o
         end.

  (* Definition to_local_view (π : gmap thread thread_status) : gmap thread thread_state := *)
  (*   fmap erase_active_thread π. *)

  Lemma invert_some_active_thread ι π m :
    active_thread ι π = Some m ->
    π !! ι = Some (Active m).
  Proof.
    intros Hactive.
    rewrite /active_thread in Hactive.
    case_eq (π !! ι).
    - intros [?|?] Hlookup; rewrite Hlookup in Hactive; try discriminate.
      by inversion Hactive.
    - intros Hlookup.
      rewrite Hlookup in Hactive; discriminate.
  Qed.

  Lemma lookup_local_view (π : thpool) (ι : thread) s :
    π !! ι = Some s ->
    (to_local_view <$> π) !! ι = Some (to_local_view s).
  Proof.
    intros Hlookup.
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.

  Lemma lookup_local_fresh (π : thpool) ι :
    π !! ι = None <-> (to_local_view <$> π) !! ι = None.
  Proof.
    etransitivity.
    - symmetry. exact (not_elem_of_dom π ι).
    - erewrite <- dom_fmap. apply not_elem_of_dom.
  Qed.

  Lemma local_view_insert_id (π : thpool) ι m m' :
    π !! ι = Some (Active m') ->
    to_local_view <$> (<[ ι := (Active m) ]> π) = to_local_view <$> π.
  Proof.
    intros Hlookup.
    rewrite !fmap_insert; simpl.
    apply insert_id.
    rewrite lookup_fmap Hlookup.
    reflexivity.
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

  Lemma unfold_micro_insert (π : thpool) ι (m : microvx) :
    @insert _ _ _ insert_thread ι m π = <[ ι := Active m ]> π.
  Proof.
    reflexivity.
  Qed.

  Lemma wptp_extract_wp π ι m :
    ⌜π !! ι = Some (Active m) ⌝ -∗
    WPTP π -∗
    EWP m @ ⊤ <| (ι, ⊥) |> {{ λ _, True }} ∗ WPTP (delete ι π).
  Proof.
    iIntros "%Hactive Hwps".
    iPoseProof (big_sepM_delete with "Hwps") as "[Hwp Hwps]".
    { apply Hactive. }
    iFrame.
  Qed.

  Lemma SAT_wptp_extract_wp π ι e m F Rs :
    π !! ι = Some (Active e) ->
    SAT m F Rs (WPTP π) ->
    SAT m F Rs (WPTP (delete ι π) ∗ EWP e <| (ι, ⊥) |> {{ λ _, True }})%I.
  Proof.
    intros Hlookup Hsat.
    eapply SAT_mono, Hsat.
    iIntros "HWPTP".
    iApply bi.sep_comm'.
    iPoseProof (wptp_extract_wp $! Hlookup with "HWPTP") as "($ & $)".
  Qed.

  Lemma attempt_join_some_inv {A X} ι π k s (m : micro A X) :
    π !! ι = Some s ->
    attempt_join ι π k = Some m ->
    ∃ o, (to_local_view <$> π) !! ι = Some (Dead o) ∧ m = k o.
  Proof.
    intros Hlookup Hattempt.
    rewrite /attempt_join in Hattempt.
    destruct s; rewrite Hlookup in Hattempt; [ discriminate | ].
    exists o.
    rewrite lookup_fmap. rewrite Hlookup.
    destruct o; by inversion Hattempt.
  Qed.

  Lemma lookup_local_view_Some (π : thpool) ι s :
    (to_local_view <$> π) !! ι = Some s ->
    ∃ m, π !! ι = Some m.
  Proof.
    intros Hlookup.
    epose proof (lookup_fmap_Some to_local_view π ι s) as [P _].
    specialize (P Hlookup) as (m & Hf & Hm).
    by exists m.
  Qed.

  Lemma sat_wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 π1 e2 σ2 π2 efs Φ n :
    wp_step (σ1, π1, e1, ι) (σ2, π2, e2, efs) →
    SAT m F [view E; supply n]
      (state_interp (σ1, π1) ∗ EWP e1 @ E <| (ι, Ψ) |> {{ Φ }}) →
    ∃ n', SAT m F [view E; supply n']
      (state_interp (σ2, π2) ∗ EWP e2 @ E <| (ι, Ψ) |> {{ Φ }} ∗ ([∗ list] '(ι', e) ∈ efs, EWP e @ E <| (ι', ⊥) |> {{ λ _, True }})).
  Proof.
    intros Hstep Hsat. eapply SAT_mono in Hsat; last first.
    { iIntros "[HSI Hwp]". rewrite ewp_unfold /ewp_pre.
      rewrite (wp_step_is_EStep _ _ _ _ _ _ _ _ Hstep).
      iSpecialize ("Hwp" with "HSI").
      iExact "Hwp". }
    eapply SAT_fupd in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[_ Hwp]". iSpecialize ("Hwp" $! _ _ _ _ Hstep). iExact "Hwp". }
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
    |={E}[∅]▷=> EWP try2 (call v1 v2) die @ E <| (ι', ⊥) |> {{ λ _, True }} ∗
    EWP (continue k (VThread ι')) @ E <| (ι, Ψ) |> {{ Φ }} ∗ state_interp (σ, <[ ι' := Alive ]> π).
  Proof.
    iIntros "%Hlookup Hsi Hfork".
    rewrite ewp_unfold /ewp_pre /=.
    spec_state.
    epose proof (ForkS _ π ι v1 v2 k ι' Hlookup) as Hfstep.
    iSpecialize ("Hfork" $! _ _ _ _ Hfstep).
    ewp_mask_elim.
    iMod "Hfork" as "(Hsi & Hcontinue & Hfork)".
    simpl; iDestruct "Hfork" as "[Hfork _]".
    by iFrame.
  Qed.

  Lemma ewp_join_inv {A X} σ π ι' k (m : micro A X) ι Ψ Φ E :
    ⌜attempt_join ι' π k = Some m⌝ -∗
    state_interp (σ, to_local_view <$> π) -∗
    EWP Stop CJoin ι' k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, to_local_view <$> π) ∗ EWP m @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hjoin Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state.
    rewrite /can_progress in Hstep. apply elem_of_dom in Hstep as [s Hstep].
    apply lookup_local_view_Some in Hstep as (ss & Hlookup).
    apply (attempt_join_some_inv _ _ _ _ _ Hlookup) in Hjoin
        as (o & Hdead & ->).
    epose proof (JoinS _ _ _ _ _ _ Hdead) as Hstep.
    iSpecialize ("Hwp" $! _ _ _ _ Hstep).
    ewp_mask_elim. iMod "Hwp" as "($ & $ & _)". done.
  Qed.

  Lemma ewp_self_inv {A X} σ π ι (k : _ -> micro A X) Ψ Φ E :
    state_interp (σ, π) -∗
    EWP Stop CSelf () k @ E <|(ι, Ψ)|> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, π) ∗ EWP (continue k (VThread ι)) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "Hsi Hwp".
    ewp_unfold (Stop CSelf () k). spec_state.
    epose proof (SelfS _ _ _ _ _) as Hwpstep.
    iSpecialize ("Hwp" $! _ _ _ _ Hwpstep).
    ewp_mask_elim. iMod "Hwp" as "($ & $ & _)". done.
  Qed.

  Lemma ewp_die_inv {A X} σ π ι o (k : _ -> micro A X) Ψ Φ E :
    ⌜ι ∈ dom π⌝ -∗
    state_interp (σ, π) -∗
    EWP Stop CDie o k @ E <|(ι, Ψ)|> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, <[ ι := Dead o ]> π) ∗ EWP k o @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hlookup Hsi Hwp".
    rewrite {1}ewp_unfold /ewp_pre /=. spec_state.
    epose proof (DieS _ _ _ _ _ Hlookup) as Hwpstep.
    iSpecialize ("Hwp" $! _ _ _ _ Hwpstep).
    ewp_mask_elim. iMod "Hwp" as "($ & $ & _)". done.
  Qed.

  (* One could be tempted to related [threadpool_step] and [wp_step] with a
     lemma of the following shape.

     Lemma threadpool_wp_step σ1 σ2 π1 π2 :
       threadpool_step (σ1, π1) (σ2, π2) ->
       ∃ ι m m' l π2',
         active_thread ι π1 = Some m ∧
         wp_step.wp_step (σ1, forget_active_threads π1, m, ι) (σ2, π2', m', l) ∧
         (match l with
          | [] => forget_active_threads π2 = π2'
          | [(  ι', _)] => <[ ι' := Alive ]> (forget_active_threads π2) = π2'
          end).

     However, threadpool_step allows [CJoin]s to crash, whereas [wp_step] only allows
     joining a valid, dead thread. *)

  Lemma wptp_step' (π1 π2 : thpool) σ1 σ2 :
    (state_interp (σ1, to_local_view <$> π1) ∗ WPTP π1) -∗
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ →
    |={⊤}[∅]▷=> state_interp (σ2, to_local_view <$> π2) ∗
                        WPTP π2.
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    inversion Hstep.
      (* iPoseProof (invert_active_thread_in_wp with "Hwps") as "Hwps"; *)
      (* try iDestruct ("Hwps" $! H2) as "(([%Φ %HΦ] & %Hm0) & Hwps)". *)
    - (* Simplify the threadpool in the goal. *)
      apply invert_some_active_thread in H2 as Hm.
      rewrite (local_view_insert_id π1 ι _ _ Hm).
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! Hm with "Hwps") as "(Hwp & Hwps)".
      (* Get [EWP m'] judgment from the facts that [EWP m] and [m -> m']. *)
      iPoseProof (ewp_step with "Hsi Hwp") as "Hwp"; first eassumption.
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
    SAT m F [view ⊤; supply n] (state_interp (σ, π) ∗ WPTP es) →
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
      not_stuck m (σ2, to_local_view <$> π2) ι.
  Proof.
    intros Hsat Hsteps. eapply wptp_steps in Hsat as (n' & Hsat); last done.
    intros ι e Hlookup.
    eauto using wptp_not_stuck.
  Qed.


  Lemma wp_adequacy m F n ι e σ1 σ2 π2 k :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (state_interp (σ1, {[ ι := Alive ]}) ∗
       EWP e @ ⊤ <| (ι, ⊥) |> {{ λ _, True%I }}) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    threadpool_steps k (σ1, {[ι := Active e]}) (σ2, π2) →
    (* then no thread is stuck *)
    (∀ ι m, π2 !! ι = Some (Active m) → not_stuck m (σ2, to_local_view <$> π2) ι).
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
Lemma SAT_wp_adequacy `{!invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 π1 σ2 π2 ι e n k P:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: osirisGS Σ := I x in
    let inv: invGS Σ := iris_invGS in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp (σ1, to_local_view <$> π1) ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e @ ⊤ <| (ι, ⊥) |> {{ λ _, True }}) →
  (* then any k-step execution is safe: *)
  threadpool_steps k (σ1, π1) (σ2, π2) →
  (∀ ι m, π2 !! ι = Some (Active m) → not_stuck e (σ2, to_local_view <$> π2) ι).
Proof.
  intros Halloc Hwp Hsteps.
  pose proof (SAT_intro (Σ := Σ)) as Hsat.
  eapply SAT_alloc_fancy_updates in Hsat as [Hi Hsat].
  eapply (Halloc Hi True%I) in Hsat as (x & Hsat); eauto; simpl in *.
  eapply SAT_mono in Hsat; last first.
  { iIntros "SI". iPoseProof (Hwp x) as "Hwp". iCombine "SI Hwp" as "Hx". iExact "Hx". }
  eapply (@wp_adequacy _ Σ (I x)), Hsteps.
  eapply SAT_mono, Hsat.
  { iIntros "([$ P] & Hwp)". by iApply "Hwp". }
Qed.


(* Definition of adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Lemma SAT_wp_adequate {Λ} `{!invGpreS Σ} (X: Type) (I: X → irisGS Λ Σ) σ1 ns nt n s e φ P:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS Σ) (F: iProp Σ) κs, SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: irisGS Λ Σ := I x in
    let inv: invGS Σ := iris_invGS in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp σ1 nt κs ns ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: irisGS Λ Σ := I x in P x ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝%I }}) →
  adequate s e σ1 (λ v _, φ v).
Proof.
  intros Halloc Hwp.
  apply adequate_alt; intros t2 σ2' [k [κs Hsteps]]%erased_steps_nsteps.
  eapply SAT_wp_adequacy; eauto.
Qed.



(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  Context {A X : Type} {Σ : gFunctors}.

  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations. *)

  Theorem ewp_adequacy (m : micro A X) ι σ φ :
  (∀ `{!irisGS_gen HasNoLc (@osiris_lang val exn) Σ},
    (* If [⊢ ⟨ ⊥ ⟩ impure m (λ v. ⌜φ v⌝)] holds *)
    ⊢ EWP m @ ⊤ <| (ι, ⊥) |> {{ fun o =>  ⌜ φ o ⌝ }}) →
    (* Then executing [m] cannot terminate with an unhandled effect or a crash, *)
    adequate NotStuck m
      σ (* in any initial heap, *)
      (λ o _, φ o) (* and the returned outcome satisfies the postcondition [φ] *).
  Proof.
  Abort.

End adequacy.
