From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.
From iris.program_logic Require Import weakestpre adequacy.

From osiris.program_logic Require Import wp_step ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import satisfiable.

Definition WPTP `{!osirisGS Σ} (t : list (thread * micro val exn)) Φs : iProp Σ :=
  ([∗ list] '(ι, e);Φ ∈ t;Φs, EWP e @ ⊤ <| (ι, ⊥) |> {{ Φ }}).

Lemma wp_wptp `{!osirisGS Σ} ι e Φ:
  EWP e @ ⊤ <| (ι, ⊥) |> {{ Φ }} ⊢ WPTP [(ι, e)] [Φ].
Proof. by rewrite /WPTP big_sepL2_singleton. Qed.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma wp_step {A X} m F E ι Ψ (e1 : micro A X) σ1 π1 e2 σ2 π2 efs Φ :
    wp_step.wp_step (σ1, π1, e1, ι) (σ2, π2, e2, efs) →
    SAT m F []
      (state_interp (σ1, π1) ∗ EWP e1 @ E <| (ι, Ψ) |> {{ Φ }}) →
    SAT m F []
      (state_interp (σ2, π2) ∗ EWP e2 @ E <| (ι, Ψ) |> {{ Φ }} ∗ ([∗ list] '(ι', e) ∈ efs, EWP e @ ⊤ <| (ι', ⊥) |> {{ λ _, True }})).
  Proof.
    intros Hstep Hsat. eapply SAT_mono in Hsat. eapply SAT_mono in Hsat; last first.
    { iIntros "[HSI Hwp]". rewrite ewp_unfold /ewp_pre.
      rewrite (wp_step_is_EStep _ _ _ _ _ _ _ _ Hstep).
      iSpecialize ("Hwp" with "HSI").

      ewp_case e1.
      rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
      iSpecialize ("Hwp" $! σ1 ns κ κs nt with "HSI").
      iExact "Hwp". }
    eapply SAT_fupd in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[_ Hwp]". iSpecialize ("Hwp" $! e2 σ2 efs Hstep). iExact "Hwp". }
    eapply (SAT_frame_resource _ (view ∅)) in Hsat; last apply _.
    eapply SAT_later_credits_credit_wand in Hsat.
    eapply SAT_unframe_resource in Hsat.
    eapply SAT_elim_iterated in Hsat; last first.
    { intros Q Hsat'. eapply SAT_fupd, SAT_later, SAT_fupd, Hsat'. }
    eapply SAT_fupd in Hsat. eexists _. eapply Hsat.
  Qed.

  Lemma wp_not_stuck m F E e σ Φ ns nt κs n:
    SAT m F [view E; supply n] (state_interp σ ns κs nt ∗ WP e @ NotStuck; E {{ Φ }}) →
    not_stuck e σ.
  Proof.
    intros Hsat. rewrite /not_stuck. destruct (to_val e) eqn: He; first by eauto.
    right. eapply SAT_mono with (Q := (|={E, ∅}=> ⌜reducible e σ⌝)%I) in Hsat.
    { eapply SAT_fupd in Hsat. by eapply SAT_elim in Hsat. }
    iIntros "[SI Hwp]". rewrite wp_unfold /wp_pre.
    rewrite He. iMod ("Hwp" $! σ ns [] κs nt with "SI") as "[$ _]".
    by iModIntro.
  Qed.

  Lemma wp_postcondition m F E s e Φ v n:
    SAT m F [view E; supply n] (WP e @ s; E {{ Φ }}) →
    to_val e = Some v →
    SAT m F [view E; supply n] (Φ v).
  Proof.
    intros Hsat Hval. eapply SAT_mono in Hsat; last first.
    { iIntros "Hwp". rewrite wp_unfold /wp_pre Hval. iExact "Hwp". }
    by eapply SAT_fupd in Hsat.
  Qed.



  Lemma wptp_length m F s Rs es Φs :
    SAT m F Rs (WPTP s es Φs) → length es = length Φs.
  Proof.
    intros Hsat. eapply SAT_elim, SAT_mono, Hsat. rewrite /WPTP. by iApply big_sepL2_length.
  Qed.

  Lemma wptp_extract_wp m F Rs s es1 e es2 Φs :
    SAT m F Rs (WPTP s (es1 ++ e :: es2) Φs) →
    ∃ Φ1s Φ2s Φ, Φs = Φ1s ++ Φ :: Φ2s ∧ length Φ1s = length es1 ∧ length Φ2s = length es2 ∧
      SAT m F Rs (WP e @ s; ⊤ {{ Φ }} ∗ WPTP s (es1 ++ es2) (Φ1s ++ Φ2s)).
  Proof.
    intros Hsat. eapply wptp_length in Hsat as Hlen. symmetry in Hlen.
    specialize (lookup_lt_is_Some_2 Φs (length es1)) as [Φ Hrest].
    { rewrite Hlen app_length /=. lia. }
    eapply take_drop_middle in Hrest as Hsplit.
    eexists _, _, _. split_and!; first done.
    - rewrite take_length Hlen app_length /=. lia.
    - rewrite drop_length Hlen app_length /=. lia.
    - eapply SAT_mono, Hsat. rewrite -{1}Hsplit.
      rewrite /WPTP. iIntros "Hx". iDestruct (big_sepL2_app_inv with "Hx") as "[$ Hx2]".
      { rewrite take_length Hlen app_length /=. lia. }
      iDestruct "Hx2" as "[$ $]".
  Qed.

  Lemma wptp_step m F n s es1 es2 σ1 σ2 κ κs Φs ns nt :
    SAT m F [view ⊤; supply n] (state_interp σ1 ns (κ ++ κs) nt ∗ WPTP s es1 Φs) →
    step (es1,σ1) κ (es2, σ2) →
    ∃ n' nt', SAT m F [view ⊤; supply n'] (state_interp σ2 (S ns) κs (nt + nt') ∗ WPTP s es2 (Φs ++ replicate nt' fork_post)).
  Proof.
    intros Hsat Hstep. destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
    rewrite -SAT_frame_cons in Hsat.
    eapply wptp_extract_wp in Hsat as (Φ1s & Φ2s & Φ & -> & Hlen1 & Hlen2 & Hsat).
    rewrite SAT_frame_cons in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "(SI & Hwp & Hwps)". iCombine "Hwps SI Hwp" as "Hx". iExact "Hx". }
    rewrite -SAT_frame_cons in Hsat.
    eapply wp_step in Hsat as (n' & Hsat); last done.
    rewrite SAT_frame_cons in Hsat.
    eexists _, _. eapply SAT_mono, Hsat.
    iIntros "(Hwps & SI & Hwp & Hforks)". rewrite Nat.add_comm. iFrame "SI".
    iDestruct (big_sepL2_app_inv with "Hwps") as "[Hwps1 Hwps2]"; first auto.
    rewrite -app_assoc /=. rewrite /WPTP. iFrame.
    rewrite big_sepL2_replicate_r //.
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
