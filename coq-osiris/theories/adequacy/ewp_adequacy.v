From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.program_logic Require Import wp_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import base_logic_extension satisfiable.

Definition WPTP `{!osirisGS Σ} (t : thpool) Φs : iProp Σ :=
  ([∗ map] ι ↦ e;Φ ∈ t;Φs,
     match e with
     | Active m => EWP m @ ⊤ <| (ι, ⊥) |> {{ Φ }}
     | Terminated o => EWP Stop CDie o inject2 @ ⊤ <| (ι, ⊥) |> {{ Φ }}
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
  | Terminated o => EWP Stop CDie o inject2 @ ⊤ <| (ι, ⊥) |> {{ Φ }}
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

  (* Lemma wptp_extract_wp m (F : iProp Σ) Rs es1 e es2 Φs : *)
  (*   SAT m F Rs (WPTP (es1 ++ e :: es2) Φs) → *)
  (*   ∃ Φ1s Φ2s Φ, Φs = Φ1s ++ Φ :: Φ2s ∧ length Φ1s = length es1 ∧ length Φ2s = length es2 ∧ *)
  (*     SAT m F Rs (EWP e.2 @ ⊤ <| (e.1, ⊥) |> {{ Φ }} ∗ WPTP (es1 ++ es2) (Φ1s ++ Φ2s)). *)
  (* Proof. *)
  (*   intros Hsat. eapply wptp_length in Hsat as Hlen. symmetry in Hlen. *)
  (*   specialize (lookup_lt_is_Some_2 Φs (length es1)) as [Φ Hrest]. *)
  (*   { rewrite Hlen app_length /=. lia. } *)
  (*   eapply take_drop_middle in Hrest as Hsplit. *)
  (*   eexists _, _, _. split_and!; first done. *)
  (*   - rewrite length_take Hlen app_length /=. lia. *)
  (*   - rewrite length_drop Hlen app_length /=. lia. *)
  (*   - eapply SAT_mono, Hsat. rewrite -{1}Hsplit. *)
  (*     rewrite /WPTP. iIntros "Hx". *)
  (*     iDestruct (big_sepL2_app_inv with "Hx") as "[Hx1 Hx2]". *)
  (*     { rewrite length_take Hlen app_length /=. lia. } *)
  (*     destruct e; simpl. *)
  (*     iDestruct "Hx2" as "[$ Hx2]". *)
  (*     iApply (big_sepL2_app with "Hx1 Hx2"). *)
  (* Qed. *)

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

  Definition forget_active_threads (m : gmap thread thread_status) : gmap thread thread_state :=
    fmap (λ s, match s with
               | Active m => Alive
               | Terminated o => Dead o
               end) m.

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

  Lemma name es1 Φs ι m Φ :
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

  Lemma wptp_step es1 es2 σ1 σ2 Φs :
    (state_interp (σ1, forget_active_threads es1) ∗ WPTP es1 Φs) -∗
    ⌜threadpool_step (σ1, es1) (σ2, es2)⌝ →
    ∃ ιo, |={⊤}[∅]▷=> state_interp (σ2, forget_active_threads es2) ∗
                        match ιo with
                        | None => WPTP es2 Φs
                        | Some ι => WPTP es2 (<[ ι := (λ _, True) ]> Φs)
                        end.
  Proof.
    iIntros "[Hsi Hwps] %Hstep".
    inversion Hstep;
      iPoseProof (invert_active_thread_in_wp with "Hwps") as "Hwps";
      try iDestruct ("Hwps" $! H2) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
    - iExists None.
      replace Φs with (<[ ι:=Φ ]> Φs) at 2 by (apply insert_id; assumption).

      iPoseProof (big_sepM2_insert_acc _ _ _ _ _ _ Hm0 HΦ with "Hwps")
        as "[Hwp Hwps]".

      iPoseProof (ewp_step with "Hsi Hwp") as "Hwp"; first eassumption.

      replace (forget_active_threads (<[ι:=m']>es1)) with (forget_active_threads es1); last first.
      { rewrite /forget_active_threads /=.
        rewrite unfold_micro_insert.
        rewrite fmap_insert. symmetry. apply insert_id.
        rewrite lookup_fmap. apply invert_some_active_thread in H2.
        rewrite H2. reflexivity. }
      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "[$ Hwp]".


      iApply "Hwps". iApply "Hwp".

    - iExists (Some ι').
      replace Φs with (<[ ι:=Φ ]> Φs) at 2 by (apply insert_id; assumption).
      iPoseProof (big_sepM2_dom with "Hwps") as "%Hdom".
      assert (Φs !! ι' = None) as Hι'.
      { apply not_elem_of_dom. apply not_elem_of_dom in H4.
        by rewrite <- Hdom. }

      pose proof (invert_some_active_thread _ _ _ H2) as Hι.

      iPoseProof (name $! H2 HΦ with "Hwps") as "[Hfork Hwps]".
      rewrite ewp_unfold /ewp_pre /=. spec_state.
      assert (forget_active_threads es1 !! ι' = None) as Hforgot.
      { by rewrite /forget_active_threads lookup_fmap H4. }
      epose proof (ForkS _ (forget_active_threads es1) ι v1 v2 k ι' Hforgot) as Hfstep.
      iSpecialize ("Hfork" $! _ _ _ _ Hfstep).
      ewp_mask_elim. iMod "Hfork" as "(Hsi & Hcontinue & Hforked)". iModIntro.
      rewrite /big_opL. iDestruct "Hforked" as "[Hforked _]".

      iSplitL "Hsi".
      { rewrite /forget_active_threads.
        do 2 (rewrite unfold_micro_insert;
              rewrite fmap_insert).
        replace (<[ι:=Alive]> (forget_active_threads es1)) with (forget_active_threads es1); [ iFrame | ].
        symmetry. apply insert_id.
        rewrite /forget_active_threads. rewrite lookup_fmap.
        rewrite Hι. reflexivity. }

      iApply big_sepM2_insert.
      { rewrite unfold_micro_insert. apply not_elem_of_lookup.
        + intro Heq; rewrite Heq in H4; rewrite H4 in Hι; discriminate.
        + assumption. }
      { apply not_elem_of_lookup.
        + intros Heq. rewrite Heq in Hι'; rewrite Hι' in HΦ; discriminate.
        + assumption. }

      iPoseProof (big_sepM2_insert_delete _ es1 Φs ι) as "[_ Hwpwp]". iFrame.
      iApply "Hwpwp". by iFrame.

    - iExists None.
      replace Φs with (<[ ι:=Φ ]> Φs) at 2 by (apply insert_id; assumption).

      iPoseProof (big_sepM2_insert_acc _ _ _ _ _ _ Hm0 HΦ with "Hwps")
        as "[Hwp Hwps]".


      rewrite ewp_unfold /ewp_pre /=. spec_state.
      rewrite /can_progress in Hstep0.
      assert (∃ o, forget_active_threads es1 !! ι' = Some (Dead o) ∧ m = k o) as (o & Hdead & ->).
      { rewrite /attempt_join in H4.
        case_eq (es1 !! ι'); last first.
        - intros Hlookup. apply elem_of_dom in Hstep0 as (s&Hlookup1).
          rewrite /forget_active_threads in Hlookup1.
          rewrite lookup_fmap in Hlookup1. rewrite Hlookup in Hlookup1. discriminate.
        - intros [F|o] Hlookup.
          + rewrite Hlookup in H4; discriminate.
          + exists o.
            rewrite /forget_active_threads. rewrite lookup_fmap.
            rewrite Hlookup. split; first reflexivity.
            rewrite Hlookup in H4.
            destruct o; by inversion H4. }

      pose proof (JoinS σ2 (forget_active_threads es1) ι k o ι' Hdead) as Hjoin.
      iSpecialize ("Hwp" $! _ _ _ _ Hjoin).

      replace (forget_active_threads (<[ι:=k o]>es1)) with (forget_active_threads es1); last first.
      { rewrite /forget_active_threads /=.
        rewrite unfold_micro_insert.
        rewrite fmap_insert. symmetry. apply insert_id.
        rewrite lookup_fmap. apply invert_some_active_thread in H2.
        rewrite H2. reflexivity. }

      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp & _)".


      iApply "Hwps". iApply "Hwp".

    - iExists None.
      iDestruct ("Hwps" $! H0) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
      replace Φs with (<[ ι:=Φ ]> Φs) at 2 by (apply insert_id; assumption).

      iPoseProof (big_sepM2_insert_acc _ _ _ _ _ _ Hm0 HΦ with "Hwps")
        as "[Hwp Hwps]".


      rewrite ewp_unfold /ewp_pre /=. spec_state.
      rewrite /can_progress in Hstep0.

      pose proof (SelfS σ2 (forget_active_threads es1) ι () k) as Hself.
      iSpecialize ("Hwp" $! _ _ _ _ Hself).

      replace (forget_active_threads (<[ι:=continue k (VThread ι)]>es1)) with (forget_active_threads es1); last first.
      { rewrite /forget_active_threads /=.
        rewrite unfold_micro_insert.
        rewrite fmap_insert. symmetry. apply insert_id.
        rewrite lookup_fmap. apply invert_some_active_thread in H0.
        rewrite H0. reflexivity. }

      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "($ & Hwp & _)".


      iApply "Hwps". iApply "Hwp".

    - iExists None.
      iDestruct ("Hwps" $! H0) as "(([%Φ %HΦ] & %Hm0) & Hwps)".
      replace Φs with (<[ ι:=Φ ]> Φs) at 2 by (apply insert_id; assumption).

      iPoseProof (big_sepM2_insert_acc _ _ _ _ _ _ Hm0 HΦ with "Hwps")
        as "[Hwp Hwps]".


      rewrite ewp_unfold /ewp_pre /=. spec_state.
      rewrite /can_progress in Hstep0.

      assert ((forget_active_threads es1) !! ι = Some Alive) as Halive.
      { rewrite /forget_active_threads lookup_fmap.
        rewrite Hm0. reflexivity. }
      pose proof (DieS σ2 (forget_active_threads es1) ι o k Halive) as Hdie.
      iSpecialize ("Hwp" $! _ _ _ _ Hdie).

      replace (forget_active_threads (<[ι:=Terminated o]>es1)) with (<[ι := Dead o]> (forget_active_threads es1));
        last first.
      { rewrite /forget_active_threads fmap_insert. reflexivity. }

      iMod "Hwp"; ewp_mask_elim; iMod "Hwp" as "(Hsi & Hwp & _)".

      destruct_wp_step; subst.
      iFrame.
      iApply "Hwps".
      iApply (ewp_die_mono with "Hwp").
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
