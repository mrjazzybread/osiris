From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.program_logic Require Import wp_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Definition WPTP `{!osirisGS Σ} (t : thpool) Φs : iProp Σ :=
  ([∗ map] ι ↦ e;Φ ∈ t;Φs,
     match e with
     | Active m => EWP m @ ⊤ <| (ι, ⊥) |> {{ Φ }}
     | Terminated o => True
     end).

Definition is_ret_or_throw {A E} (m : micro A E) : Prop :=
  match m with
  | Ret _ | Throw _ => True
  | _ => False
  end.

Definition not_stuck {A E} (m : micro A E) s ι :=
  is_ret_or_throw m ∨ can_progress (s.1, s.2, m, ι).

Lemma wp_wptp `{!osirisGS Σ} ι e Φ:
  match e with
  | Active m => EWP m @ ⊤ <| (ι, ⊥) |> {{ Φ }}
  | Terminated o => True
  end ⊢ WPTP {[ι := e]} {[ι := Φ]}.
Proof. by rewrite /WPTP big_sepM2_singleton. Qed.

Include ewp_rules_tactics.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 π1 e2 σ2 π2 efs Φ n :
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

  Lemma wp_not_stuck {A X} m F E (e : micro A X) ι σ π Φ n:
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
      { eapply SAT_fupd in Hsat. by apply SAT_elim in Hsat. }
      iIntros "[Hsi Hwp]".
      spec_state. iModIntro.
      iPureIntro; assumption.
  Qed.

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

  Lemma wptp_length m F Rs es Φs :
    SAT m F Rs (WPTP es Φs) → dom es = dom Φs.
  Proof.
    intros Hsat. eapply SAT_elim, SAT_mono, Hsat. rewrite /WPTP. by iApply big_sepM2_dom.
  Qed.

  Lemma step_EStep {A X} σ (m : micro A X) σ' m' :
    step (σ, m) (σ', m') -> is_ewp_case m = EStep.
  Proof.
    intros Hstep.
    inversion Hstep; subst; reflexivity.
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

  Lemma invert_active_thread_in_wp es1 Φs ι m :
    WPTP es1 Φs -∗
    ⌜active_thread ι es1 = Some m⌝ -∗
    ⌜(∃ Φ, (Φs !! ι) = Some Φ) ∧ es1 !! ι = Some (Active m)⌝ ∗ WPTP es1 Φs.
  Proof.
    iIntros "Hwps %Hactive".
    iPoseProof (big_sepM2_dom with "Hwps") as "%Hdom". iFrame.
    iPureIntro.
    rewrite /active_thread in Hactive.
    case_eq (es1 !! ι); last (intros Heq; rewrite Heq in Hactive; discriminate).
    intros [? | ?] Heq; rewrite Heq in Hactive; subst; last discriminate.
    split.
    - apply elem_of_dom.
      rewrite -Hdom.
      apply elem_of_dom. exists (Active m0). apply Heq.
    - inversion Hactive; subst. reflexivity.
  Qed.

  Definition erase_computation := λ s, match s with
                                       | Active m => Alive
                                       | Terminated o => Dead o
                                       end.

  Definition forget_active_threads (m : gmap thread thread_status) : gmap thread thread_state :=
    fmap erase_computation m.

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

  Lemma forget_insert_alive (π : thpool) ι (m : microvx) :
    forget_active_threads (@insert _ _ _ insert_thread ι m π) = <[ ι := Alive ]> (forget_active_threads π).
  Proof.
    rewrite /forget_active_threads.
    rewrite fmap_insert. reflexivity.
  Qed.

  Lemma forget_insert_dead (π : thpool) ι o :
    forget_active_threads (<[ι:=Terminated o]> π) = <[ ι := Dead o ]> (forget_active_threads π).
  Proof.
    rewrite /forget_active_threads.
    rewrite fmap_insert. reflexivity.
  Qed.

  Lemma lookup_forget_active π ι m :
    π !! ι = Some (Active m) ->
    forget_active_threads π !! ι = Some Alive.
  Proof.
    intros Hlookup.
    rewrite /forget_active_threads lookup_fmap.
    by rewrite Hlookup.
  Qed.

  Lemma lookup_forget_terminated π ι o :
    π !! ι = Some (Terminated o) ->
    forget_active_threads π !! ι = Some (Dead o).
  Proof.
    intros Hlookup.
    rewrite /forget_active_threads lookup_fmap.
    by rewrite Hlookup.
  Qed.

  Lemma lookup_forget_fresh π ι :
    π !! ι = None <-> forget_active_threads π !! ι = None.
  Proof.
    rewrite /forget_active_threads.
    etransitivity.
    - symmetry. apply not_elem_of_dom.
    - erewrite <- dom_fmap. apply not_elem_of_dom.
  Qed.

  Lemma forget_active_insert_id π ι m m' :
    π !! ι = Some (Active m') ->
    forget_active_threads (@insert _ _ _ insert_thread ι m π) = forget_active_threads π.
  Proof.
    intros Hlookup.
    rewrite forget_insert_alive.
    apply insert_id.
    eapply lookup_forget_active. apply Hlookup.
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

  Lemma wptp_extract_wp es1 Φs ι m Φ :
    ⌜active_thread ι es1 = Some m⌝ -∗
    ⌜Φs !! ι = Some Φ⌝ -∗
    WPTP es1 Φs -∗
    EWP m @ ⊤ <| (ι, ⊥) |> {{ Φ }} ∗ WPTP (delete ι es1) (delete ι Φs).
  Proof.
    iIntros "%Hactive %Hpost Hwps".
    iPoseProof (big_sepM2_delete with "Hwps") as "[Hwp Hwps]".
    { apply invert_some_active_thread in Hactive.
      apply Hactive. }
    { apply Hpost. }
    iFrame.
  Qed.

  Lemma attempt_join_some_inv {A X} ι π k s (m : micro A X) :
    π !! ι = Some s ->
    attempt_join ι π k = Some m ->
    ∃ o, forget_active_threads π !! ι = Some (Dead o) ∧ m = k o.
  Proof.
    intros Hlookup Hattempt.
    rewrite /attempt_join in Hattempt.
    destruct s; rewrite Hlookup in Hattempt; [ discriminate | ].
    exists o.
    rewrite (lookup_forget_terminated _ _ _ Hlookup).
    destruct o; by inversion Hattempt.
  Qed.

  Lemma lookup_forget_some π ι s :
    forget_active_threads π !! ι = Some s ->
    ∃ m, π !! ι = Some m.
  Proof.
    intros Hlookup.
    rewrite /forget_active_threads in Hlookup.
    epose proof (lookup_fmap_Some erase_computation π ι s) as [P _].
    specialize (P Hlookup) as (m & Hf & Hm).
    by exists m.
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
    state_interp (σ, forget_active_threads π) -∗
    EWP Stop CJoin ι' k @ E <| (ι, Ψ) |> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, forget_active_threads π) ∗ EWP m @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "%Hjoin Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state.
    rewrite /can_progress in Hstep. apply elem_of_dom in Hstep as [s Hstep].
    apply lookup_forget_some in Hstep as (ss & Hlookup).
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
    ⌜π !! ι = Some Alive⌝ -∗
    state_interp (σ, π) -∗
    EWP Stop CDie o k @ E <|(ι, Ψ)|> {{ Φ }} -∗
    |={E}[∅]▷=> state_interp (σ, <[ ι := Dead o ]> π) ∗ EWP Stop CDie o k @ E <| (ι, Ψ) |> {{ Φ }}.
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

  Lemma wptp_step π1 π2 σ1 σ2 Φs :
    (state_interp (σ1, forget_active_threads π1) ∗ WPTP π1 Φs) -∗
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ →
    ∃ ιo, |={⊤}[∅]▷=> state_interp (σ2, forget_active_threads π2) ∗
                        match ιo with
                        | None => WPTP π2 Φs
                        | Some ι => WPTP π2 (<[ ι := (λ _, True) ]> Φs)
                        end.
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    inversion Hstep;
      iPoseProof (invert_active_thread_in_wp with "Hwps") as "Hwps";
      try iDestruct ("Hwps" $! H2) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
    - (* Taking a step does not create a new thread. *)
      iExists None.
      (* Simplify the threadpool in the goal. *)
      rewrite (forget_active_insert_id _ _ _ _ Hm0).
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H2 HΦ with "Hwps") as "[Hwp Hwps]".
      (* Get [EWP m'] judgment from the facts that [EWP m] and [m -> m']. *)
      iPoseProof (ewp_step with "Hsi Hwp") as "Hwp"; first eassumption.
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "[$ Hwp]".
      (* Recombine [EWP m'] with [WPTP]. *)
      rewrite -{2}(insert_id Φs ι Φ HΦ).
      iApply big_sepM2_insert_delete.
      by iFrame.

    - (* Forking a thread creates a new thread indexed by [ι']. *)
      iExists (Some ι').
      (* Simplify the threadpool in the goal. *)
      rewrite (forget_insert_alive) (forget_active_insert_id _ _ _ _ Hm0).
      (* Assertions about the fresh thread index [ι']. *)
      assert (ι' ≠ ι) as Hfresh. { intro Heq; rewrite Heq in H4; rewrite H4 in Hm0; discriminate. }
      iAssert (⌜Φs !! ι' = None⌝)%I as "%Hι'".
      { iPoseProof (big_sepM2_dom with "Hwps") as "%Hdom"; iPureIntro.
        apply not_elem_of_dom. rewrite -Hdom. by apply not_elem_of_dom. }

      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H2 HΦ with "Hwps") as "[Hfork Hwps]".
      (* Inversion on [EWP Stop CFork]. *)
      apply lookup_forget_fresh in H4 as Hforgot.
      iPoseProof (ewp_fork_inv $! Hforgot with "Hsi Hfork") as "Hfork".
      (* Framing. *)
      iMod "Hfork"; ewp_mask_elim; iMod "Hfork" as "(Hforked & Hcontinue & $)"; iModIntro.
      (* Recombine [EWP]s into one big [WPTP]. *)
      rewrite -{2}(insert_id Φs ι Φ HΦ).
      iApply big_sepM2_insert.
      { rewrite unfold_micro_insert; apply not_elem_of_lookup; assumption. }
      { apply not_elem_of_lookup; [ assumption | apply Hι' ]. }
      iFrame.
      iApply big_sepM2_insert_delete.
      iFrame.

    - (* Joining a thread does not create a new thread. *)
      iExists None.
      (* Simplify the threadpool in the goal. *)
      rewrite (forget_active_insert_id _ _ _ _ Hm0).
      (* Get the [EWP] jugment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H2 HΦ with "Hwps") as "[Hjoin Hwps]".
      (* Invert the [EWP Stop CJoin]. *)
      iPoseProof (ewp_join_inv $! H4 with "Hsi Hjoin") as "Hwp".
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp)".
      (* Recombine the [EWP] and [WPTP] judgments. *)
      rewrite -{2}(insert_id _ _ _ HΦ).
      iApply big_sepM2_insert_delete.
      by iFrame.

    - (* Getting one's own thread id does not create a new thread. *)
      iExists None.
      iDestruct ("Hwps" $! H0) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
      (* Simplify the threadpool in the goal. *)
      rewrite (forget_active_insert_id _ _ _ _ Hm0).
      (* Geth the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H0 HΦ with "Hwps") as "[Hself Hwps]".
      (* Invert the [EWP Stop CSelf]. *)
      iPoseProof (ewp_self_inv with "Hsi Hself") as "Hwp".
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp)".
      (* Recombine the [EWP] and [WPTP] judgments. *)
      rewrite -{2}(insert_id _ _ _ HΦ).
      iApply big_sepM2_insert_delete.
      by iFrame.

    - (* Dying does not create a new thread. *)
      iExists None.
      iDestruct ("Hwps" $! H0) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
      (* Simplify the threadpool in the goal. *)
      rewrite forget_insert_dead.
      (* Get the [EWP] judgment for the active thread. *)
      iPoseProof (wptp_extract_wp $! H0 HΦ with "Hwps") as "[Hdie Hwps]".
      (* Inversion on [EWP Stop CDie] to get the updated state interp. *)
      apply lookup_forget_active in Hm0.
      iPoseProof (ewp_die_inv $! Hm0 with "Hsi Hdie") as "Hwp".
      iMod "Hwp". ewp_mask_elim. iMod "Hwp" as "($ & _)".
      (* No need to recombine the [EWP] and [WPTP] because the definition of
         [WPTP] does not require anything on terminated threads.  *)
      rewrite -{2}(insert_id _ _ _ HΦ).
      iApply big_sepM2_insert_delete.
      iFrame.
      done.
  Qed.

  Lemma wptp_step m F n es1 es2 σ1 σ2 π Φs :
    SAT m F [view ⊤; supply n] (state_interp (σ1, π) ∗ WPTP es1 Φs) →
    threadpool_step (σ1, es1) (σ2, es2) →
    ∃ n' π', SAT m F [view ⊤; supply n'] (|={⊤}[∅]▷=> state_interp (σ2, π') ∗ WPTP es2 Φs).
  Proof.
    intros Hsat Hstep.
    (* rewrite -SAT_frame_cons in Hsat. *)
    (* eapply wptp_extract_wp in Hsat as (Φ1s & Φ2s & Φ & -> & Hlen1 & Hlen2 & Hsat). *)
    (* rewrite SAT_frame_cons in Hsat. *)
    eapply SAT_mono in Hsat.
    { exists n. exact Hsat. }

    iIntros "[Hsi Hwps]".
    apply SAT_frame_cons in Hsat.

  Qed.

  Lemma wptp_steps m F n k s es1 es2 σ1 σ2 κs κs' Φs ns nt :
    SAT m F [view ⊤; supply n] (state_interp σ1 ns (κs ++ κs') nt ∗ WPTP s es1 Φs) →
    language.nsteps k (es1, σ1) κs (es2, σ2) →
    ∃ n' nt', SAT m F [view ⊤; supply n'] (state_interp σ2 (ns + k) κs' (nt + nt') ∗ WPTP s es2 (Φs ++ replicate nt' fork_post)).
  Proof.
    induction k as [|k IH] in  n, es1, σ1, ns, κs, nt, Φs |-*; intros Hsat Hsteps.
    - revert Hsat. inversion_clear Hsteps. exists n, 0. rewrite !right_id !Nat.add_0_r //.
    - revert Hsat. inversion_clear Hsteps as [|?? [t1' σ1']]. rewrite -app_assoc. intros Hsat.
      eapply wptp_step in Hsat as (n' & nt' & Hsat); last done.
      eapply IH in Hsat as (n'' & nt'' & Hsat); last done.
      exists n'', (nt' + nt''). rewrite !Nat.add_assoc.
      revert Hsat. rewrite -app_assoc replicate_add //= Nat.add_succ_r //.
  Qed.

  Lemma wptp_not_stuck m F n e es σ ns κs nt Φs:
    SAT m F [view ⊤; supply n] (state_interp σ ns κs nt ∗ WPTP NotStuck es Φs) →
    e ∈ es →
    not_stuck e σ.
  Proof.
    intros Hsat [i Hlook]%elem_of_list_lookup_1.
    eapply take_drop_middle in Hlook as Hsplit.
    rewrite -Hsplit in Hsat. rewrite -SAT_frame_cons in Hsat.
    eapply wptp_extract_wp in Hsat as (Φ1s & Φ2s & Φ & -> & Hlen1 & Hlen2 & Hsat).
    rewrite SAT_frame_cons in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "(SI & Hwp & Hwps)". iCombine "Hwps SI Hwp" as "Hx". iExact "Hx". }
    rewrite -SAT_frame_cons in Hsat.
    by eapply wp_not_stuck in Hsat.
  Qed.


  Lemma wptp_postconditions m F n s es Φs:
    SAT m F [view ⊤; supply n] (WPTP s es Φs) →
    SAT m F [view ⊤; supply n] ([∗ list] e;Φ ∈ es; Φs, from_option Φ (WP e @ s; ⊤ {{ Φ }}) (to_val e)).
  Proof.
    induction es as [|e es IH] in Φs, F |-*; intros Hsat.
    - eapply wptp_length in Hsat as Hlen. destruct Φs; last done. eapply Hsat.
    - eapply wptp_length in Hsat as Hlen. destruct Φs as [|Φ Φs]; first done.
      revert Hsat. rewrite /WPTP /=. intros Hsat.
      rewrite -SAT_frame_cons. eapply IH. rewrite SAT_frame_cons.
      rewrite bi.sep_comm. revert Hsat. rewrite bi.sep_comm.
      rewrite -!SAT_frame_cons. destruct (to_val e) eqn:Heq.
      + intros Hsat. eapply SAT_mono, wp_postcondition; eauto.
      + eapply SAT_mono. by iIntros "$".
  Qed.


  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy m F n k s es1 es2 nt ns κs κs' σ1 σ2 Φs:
    SAT m F [view ⊤; supply n] (state_interp σ1 ns (κs ++ κs') nt ∗ WPTP s es1 Φs) →
    language.nsteps k (es1, σ1) κs (es2, σ2) →
    ∃ n' nt', SAT m F [view ⊤; supply n']
      (state_interp σ2 (ns + k) κs' (nt + nt') ∗ ([∗ list] e;Φ ∈ es2; (Φs ++ replicate nt' fork_post), from_option Φ (WP e @ s; ⊤ {{ Φ }}) (to_val e)))
    ∧ (∀ e, s = NotStuck → e ∈ es2 → not_stuck e σ2).
  Proof.
    intros Hsat Hsteps. eapply wptp_steps in Hsat as (n' & nt' & Hsat); last done.
    eexists _, _. split.
    - rewrite -SAT_frame_cons in Hsat. eapply wptp_postconditions in Hsat.
      rewrite SAT_frame_cons in Hsat. eauto using wptp_not_stuck.
    - intros e -> Hel. eapply wptp_not_stuck; eauto.
  Qed.


  Lemma wp_adequacy m F n κs s e es σ1 σ2 φ nt ns k :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n] (state_interp σ1 nt κs ns ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝%I }}) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    language.nsteps k ([e], σ1) κs (es, σ2) →
    (* then no thread is stuck and if the main thread terminates in a value, it satisfies the postcondition *)
    (∀ v es', es = language.of_val v :: es' → φ v) ∧
    (∀ e, s = NotStuck → e ∈ es → not_stuck e σ2).
  Proof.
    intros Hsat Hsteps. rewrite wp_wptp in Hsat.
    replace κs with (κs ++ []) in Hsat by rewrite app_nil_r //.
    eapply wptp_adequacy in Hsat as (n' & nt' & Hsat); eauto.
    destruct Hsat as (Hsat & Hnstuck). split; last eapply Hnstuck.
    intros v es' ->; simpl in *. rewrite to_of_val /= in Hsat.
    eapply SAT_elim, SAT_mono, Hsat. iIntros "(_ & $ & _)".
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
Lemma SAT_wp_adequacy {Λ} `{!invGpreS Σ} (X: Type) (I: X → irisGS Λ Σ) κs σ1 σ2 ns nt n s e es φ k P:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: irisGS Λ Σ := I x in
    let inv: invGS Σ := iris_invGS in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp σ1 nt κs ns ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: irisGS Λ Σ := I x in P x ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝%I }}) →
  (* then any k-step execution is safe: *)
  language.nsteps k ([e], σ1) κs (es, σ2) →
  (∀ v es', es = language.of_val v :: es' → φ v) ∧
  (∀ e, s = NotStuck → e ∈ es → not_stuck e σ2).
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
