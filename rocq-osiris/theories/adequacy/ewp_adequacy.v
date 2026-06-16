From iris.proofmode Require Import base ltac_tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap saved_prop token.

From osiris.lang Require Import thread_ids.
From osiris.semantics Require Import eval.
From osiris.program_logic Require Import
  thread_step ewp basic_rules micro_rules tactics.
Require Import satisfiable.base_logic_extension satisfiable.

From Stdlib Require Import Program.Equality.

Definition WPTP `{!osirisGS Σ} (π : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))): iProp Σ :=
  ([∗ map] ι ↦ m; '(γ, φ) ∈ π; πp, saved_pred_own γ DfracDiscarded φ ∗ ewp_def ⊤ m ⊥ (λ o, □ φ o)).

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


(* -------------------------------------------------------------------------- *)
(* General gmap helper lemmas *)

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

Lemma fmap_fst_lookup {A B} (m : gmap thread (A * B)) ι a b :
  m !! ι = Some (a, b) →
  (fst <$> m) !! ι = Some a.
Proof. intros. by rewrite lookup_fmap H. Qed.

Lemma lookup_delete_ne_inv {K} `{Countable K} {A} (m : gmap K A) (i j : K) (x : A) :
  i ≠ j →
  m !! j = Some x →
  delete i m !! j = Some x.
Proof. intros. by rewrite lookup_delete_ne. Qed.

(* [insert_list] takes a list of bindings, a gmap,
   and inserts every binding into the gmap in order. *)
Fixpoint insert_list {A : Type} l (πp : gmap thread A) :=
    match l with
    | [] => πp
    | (ι, φ) :: t => <[ι:=φ]>(insert_list t πp)
    end.

Lemma insert_list_app {A : Type} l l' (πp : gmap thread A) :
  insert_list (l' ++ l) πp = insert_list l' (insert_list l πp).
Proof.
  induction l' as [ | [ι' φ'] l'].
  - reflexivity.
  - simpl. f_equal.
    apply IHl'.
Qed.

Lemma insert_list_lookup_not_in {A} ι l (πp : gmap thread A) :
  ι ∉ fst <$> l →
  insert_list l πp !! ι = πp !! ι.
Proof.
  induction l as [| [ι' a] l IH]; first done.
  rewrite fmap_cons not_elem_of_cons. simpl.
  intros [Hneq Hnin].
  rewrite lookup_insert_ne; first by apply IH.
  by symmetry.
Qed.

Lemma not_elem_of_insert_list {A} ι l (πp : gmap thread A) :
  ι ∉ dom (insert_list l πp) →
  ι ∉ fst <$> l ∧ ι ∉ dom πp.
Proof.
  induction l as [| [ι' a] l IH].
  - simpl.
    intros Hnin.
    split; [ apply not_elem_of_nil | exact Hnin ].
  - simpl. rewrite dom_insert.
    rewrite not_elem_of_union not_elem_of_singleton.
    intros [Hnhead Hndom].
    destruct (IH Hndom) as [Hnlist Hndom'].
    rewrite not_elem_of_cons.
    auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helper lemmas for manipulating [WPTP]s. *)

(* [wp_wptp] established the correspondence between [EWP] and [WPTP] over a singleton. *)
Lemma wp_wptp `{!osirisGS Σ} ι m γ φ :
  (saved_pred_own γ DfracDiscarded φ ∗ ewp_def ⊤ m ⊥ (λ o, □ φ o)) ⊣⊢ WPTP {[ι := m ]} {[ι := (γ, φ)]}.
Proof.
  unfold WPTP.
  by rewrite big_sepM2_singleton.
Qed.

Lemma WPTP_dom `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp = dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  by iPureIntro.
Qed.

Lemma WPTP_dom_equiv `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp ≡ dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  iPureIntro; by rewrite Hdomeq.
Qed.

(* Isolate a specific thread in a [WPTP]. *)
Lemma WPTP_extract_wp `{!osirisGS Σ} π πp ι e :
  ⌜π !! ι = Some e⌝ -∗
  WPTP π πp -∗
  ∃ γ φ , ⌜πp !! ι = Some (γ, φ)⌝ ∗
         saved_pred_own γ DfracDiscarded φ ∗
         ewp_def ⊤ e ⊥ (λ o, □ φ o) ∗ WPTP (delete ι π) (delete ι πp).
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

(* Reinsert a thread that was extracted back into a [WPTP]. *)
Lemma WPTP_insert_delete `{!osirisGS Σ} ι π1 πp m' γ φ :
  ⌜πp !! ι = Some (γ, φ)⌝ -∗
  WPTP (delete ι π1) (delete ι πp) -∗
  (saved_pred_own γ DfracDiscarded φ ∗ ewp_def ⊤ m' ⊥ (λ o, □ φ o)) -∗
  WPTP (<[ι:=m']> π1) πp.
Proof.
  iIntros "%Hlookup Hwps Hwp".
  replace πp with (<[ι:=(γ, φ)]>πp) by apply (insert_id πp ι (γ, φ) Hlookup).
  iApply big_sepM2_insert_delete.
  replace πp with (<[ι:=(γ, φ)]>πp) at 2 by apply (insert_id πp ι (γ, φ) Hlookup).
  iFrame.
Qed.

(* Reinsert a terminated thread's postcondition that was extracted
   back into a [WPTP]. *)
Lemma WPTP_insert_post_delete `{!osirisGS Σ} ι π1 πp γ φ o :
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
  iApply fupd_ewp. iMod "Hwp". iModIntro.
  by iApply ewp_outcome2.
Qed.

(* Isolate a specific postcondition (i.e. terminated thread) in a [WPTP]. *)
Lemma WPTP_extract_outcome `{!osirisGS Σ} π πp ι o :
  ⌜π !! ι = Some (inject2 o)⌝ -∗
  WPTP π πp -∗
  ∃ γ φ, ⌜πp !! ι = Some (γ, φ)⌝ ∗ saved_pred_own γ DfracDiscarded φ ∗ WPTP (delete ι π) (delete ι πp) ∗ (|={⊤}=> □ φ o).
Proof.
  iIntros "%Hlookup Hwps".
  iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%γ & %φ & %Hlookup_p & #Hsaved & Hwp & Hwps)".
  iExists γ, φ. iFrame "∗%#".
  by iApply (ewp_outcome2_inv with "Hwp").
Qed.


Include ewp_rules_tactics.

Ltac invert_can_progress :=
    lazymatch goal with
    | h: can_progress _ _ ?e |- _ =>
        let hstep := fresh "Htstep" in
        let ι' := fresh "ι'" in
        let k := fresh "k" in
        let Heq_e := fresh "Heq_e" in
        let Hdom := fresh "Hdom" in
        let v1 := fresh "v" in
        let v2 := fresh "v" in
        let u := fresh "u" in
        let σ'_inner := fresh "σ_inner" in
        let e'_inner := fresh "e_inner" in
        let Hstep := fresh "Hstep" in
        apply invert_can_progress in h as hstep;
        destruct hstep as
          [(ι' & k & Heq_e & Hdom)
          | [ (v1 & v2 & k & Heq_e) |
              ([σ'_inner e'_inner] & Hstep)
          ] ];
        try subst e
    end.

Local Ltac iModFL_tac s := iMod s; iModIntro; iNext; iMod s; iModIntro.

Local Tactic Notation "iModFL" constr(s) "as" constr(s') :=
  iModFL_tac s; iDestruct s as s'.
Local Tactic Notation "iModFL" constr(s) := iModFL_tac s.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma EWP_not_stuck_post {A X} E (e : micro A X) σ πp Φ :
    state_interp (σ, πp) ∗ ewp_def E e ⊥ Φ ={E}[∅]▷=∗
    ⌜not_stuck e σ (dom πp)⌝ ∗ (∀ o, ⌜e = inject2 o⌝ -∗ Φ o).
  Proof.
    iIntros "(Hsi & Hwp)". rewrite /not_stuck.
    ewp_unfold e.
    ewp_case e; simpl.
    - (* Case: [e] is an [outcome2]. *)
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iMod "Hwp". iModIntro.
      iSplitR.
      + (* Prove we are not stuck. *)
        iPureIntro; left; by destruct o.
      + (* Prove we satisfy the postcondition. *)
        iIntros (o' Heq).
        destruct o; destruct o'; unfold inject2 in Heq;
          inversion Heq; iApply "Hwp".
    - (* Case: [e] is a [crash]. *) by iMod "Hwp".
    - (* Case: [e] is a [perform]. *)
      iMod "Hwp" as "(% & [] & Hwp)".
    - (* Case: [e] takes a thread_step. *)
      spec_state. rename Hstep into Hprog.
      invert_can_progress.
      + (* Subcase: [e] is a join. *)
        discriminate Hhm.
      + (* Subcase: [e] is a fork. *)
        epose proof (ForkS σ (fresh (dom πp)) (dom πp) _ _ k (is_fresh _)) as Htstep_fork.
        spec_step.
        iModIntro. iNext. iMod "Hwp". iModIntro.
        iSplitR.
        * (* Prove that we are not stuck. *)
          iPureIntro. right; left. apply can_progress_fork.
        * (* Prove that if we are final, we satisfy the post (we are not final). *)
          iIntros (o HFalse). destruct o; discriminate HFalse.
      + (* Subcase: [e] takes a regular step. *)
        pose proof (BaseS e σ _ _ (dom πp) Hstep) as Htstep_base.
        spec_step. iModIntro. iNext. iMod "Hwp". iModIntro.
        iSplitR.
        * (* Prove that we are not stuck. *)
          iPureIntro. right; left. exact Hprog.
        * (* Prove that if we are final, we satisfy the post (we are not final). *)
          iIntros (o HFalse); rewrite HFalse in Hstep.
          destruct o; inversion Hstep.
    - (* Case: [e] is a join. *)
      spec_state.
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iModIntro.
      iSplitR.
      + (* Prove that we are not stuck. *)
        iPureIntro. by right; right.
      + (* Prove that if we are final, we satisfy the post (we are not final). *)
        iIntros (o HFalse). destruct o; discriminate HFalse.
  Qed.

  Inductive nsteps {A X} : nat → config A X → config A X → Prop :=
    nsteps_refl : ∀ ρ : config A X, nsteps 0 ρ ρ
  | nsteps_l :
    ∀ (n : nat) (ρ1 ρ2 ρ3 : config A X),
      step ρ1 ρ2 →
      nsteps n ρ2 ρ3 →
      nsteps (S n) ρ1 ρ3.

  Lemma ewp_join_inv {A X} γ φ σ πp ι' (k : _ → micro A X) Ψ Φ E o :
    ⌜πp !! ι' = Some γ⌝ -∗
    saved_pred_own γ DfracDiscarded φ -∗
    □ φ o -∗
    state_interp (σ, πp) -∗
    ewp_def E (Stop CJoin ι' k) Ψ Φ -∗
    |={E}[∅]▷=> state_interp (σ, πp) ∗ ewp_def E (k o) Ψ Φ.
  Proof.
    iIntros "%Hlookup Hsaved Hφ Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state.
    rewrite Hlookup.
    iMod "Hwp" as "(%φ' & Hsaved' & Hwp)".
    iPoseProof (saved_pred_agree _ _ _ _ _ o with "Hsaved Hsaved'") as "Hagree".
    iModIntro. iNext. iRewrite "Hagree" in "Hφ".
    iSpecialize ("Hwp" with "Hφ").
    ewp_mask_elim. iMod "Hwp" as "($ & $)". done.
  Qed.

  (* Relating a "real" threadpool step (from the definition of the semantics),
     to a "local" thread step (from the definition of our weakest pre). *)
  Lemma threadpool_thread_step (σ1 σ2 : store) (π1 π2 : thpool) :
    (* If the threadpool can take a step *)
    threadpool_step (σ1, π1) (σ2, π2) →
    (* Then either that step was a join *)
    (∃ ι ι' k m,
        π1 !! ι = Some (Stop CJoin ι' k) ∧
        attempt_join ι' π1 k = Some m ∧
        σ1 = σ2 ∧
          π2 = <[ι:=m]>π1)
    ∨
    (* Or that step can be emulated by a [thread_step]. *)
    ∃ (ι : thread) (m m' : microvx) μ,
      π1 !! ι = Some m ∧
      π2 !! ι = Some m' ∧
      thread_step (σ1, m, dom π1) (σ2, m', μ) ∧
      (* With different descriptions of [π2] depending on
         whether a new thread was forked or not. *)
      match μ with
      | None => π2 = <[ι:=m']>π1
      | Some (ι', mf) => <[ι:=m']> π1 !! ι' = None ∧ π2 = <[ι':=mf]>(<[ι:=m']>π1)
      end.
  Proof.
    intros Htpstep.
    inversion_clear Htpstep.
    - (* BaseTP case: π !! ι = Some m, step (σ, m) (σ', m') *)
      right; rename H into Hlookup, H0 into Hstep; subst.
      eapply BaseS in Hstep as Htstep.
      exists ι, m, m', None.
      split; [exact Hlookup | split; [ apply lookup_insert_eq | split; [exact Htstep | reflexivity]]].
    - (* ForkTP case: π !! ι = Some (Stop CFork ...), π !! ι' = None *)
      right; rename H into Hlookup, H0 into Hfresh; subst.
      exists ι, (Stop CFork (v1, v2) k), (continue k (VThread ι')), (Some (ι', call v1 v2)).
      split; [exact Hlookup | ].
      split; [rewrite lookup_insert_ne; [apply lookup_insert_eq | ] | ].
      { intros Heq_ι. subst ι'. rewrite Hfresh in Hlookup. discriminate Hlookup. }
      split.
      + apply ForkS. apply (not_elem_of_dom π1). exact Hfresh.
      + split; [| reflexivity].
        rewrite lookup_insert_ne; [exact Hfresh | ].
        intros Heq_ι'. subst ι'. rewrite Hfresh in Hlookup. discriminate Hlookup.
    - (* JoinTP case: π !! ι = Some (Stop CJoin ...), attempt_join ... *)
      left; rename H into Hlookup, H0 into Hattempt; subst.
      exists ι, ι', k, m.
      split; [exact Hlookup | split; [exact Hattempt | split; reflexivity]].
  Qed.

  Lemma wptp_tstep (π1 : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))) σ1 σ2 m m' ι μ :
    ⌜π1 !! ι = Some m⌝ -∗
    ⌜thread_step (σ1, m, dom πp) (σ2, m', μ)⌝ -∗
    (state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp) ={⊤}[∅]▷=∗
     match μ with
     | None => state_interp (σ2, fst <$> πp) ∗ WPTP (<[ι:=m']>π1) πp
     | Some (ι', mforked) => ∃ (φ : outcome2 val exn → iProp Σ) γ,
       state_interp (σ2, <[ι':=γ]>(fst <$> πp)) ∗ WPTP (<[ι':=mforked]> (<[ι:=m']>π1)) (<[ι':=(γ, φ)]>πp)
     end.
  Proof.
    iIntros "%Hlookup %Hstep [Hsi Hwps]".
    iPoseProof (WPTP_dom_equiv with "Hwps") as "%Hdomeq".
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps")
      as "(%γ & %φ & %Hlookup_p & #Hsaved & Hwp & Hwps)".
    iPoseProof (ewp_step with "Hsi Hwp") as ">Hwp". { rewrite dom_fmap_L. apply Hstep. }
    iModFL "Hwp" as "[Hwp Hμ]".
    inversion Hstep; subst; iFrame.
    - (* Case: thread_step is a [BaseS]. *)
      iApply (WPTP_insert_delete $! Hlookup_p with "Hwps [$]").
    - (* Case: thread_step is a [ForkS]. *)
      iDestruct "Hμ" as "(%φ' & %γ' & Hsi & #Hsaved' & Hcall)".
      iFrame. iExists φ'.
      iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "Hwps".
      iApply big_sepM2_insert.
      { setoid_rewrite Hdomeq in H0. apply not_elem_of_dom in H0.
        rewrite lookup_insert_ne; try assumption.
        apply (lookup_ne π1). by rewrite H0 Hlookup. }
      { apply not_elem_of_dom; assumption. }
      iFrame. iApply "Hsaved'".
  Qed.

  Ltac invert_threadpool_step :=
    lazymatch goal with
    | h: threadpool_step (?σ1, ?π1) (?σ2, ?π2) |- _ =>
        let Hsteps := fresh "Hsteps" in
        (have Hsteps := threadpool_thread_step σ1 σ2 π1 π2 h);
        destruct Hsteps as
          [ (ι & ι' & k & e & Hlookup & Hattempt & Heq_σ & Heq_π2)
          | (ι & e & e' & μ & Hlookup & Hlookup' & Htstep & Hμ)
          ];
        subst;
        last first
    end.

  Lemma wptp_step (π1 π2 : thpool) (πp : gmap thread (gname * (outcome2 val exn → iProp Σ))) σ1 σ2 :
    ⌜threadpool_step (σ1, π1) (σ2, π2)⌝ -∗
    (state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp) ={⊤}[∅]▷=∗
    (∃ (l : list (thread * (gname * (outcome2 val exn → iProp Σ)))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, fst <$> (insert_list l πp)) ∗ WPTP π2 (insert_list l πp)).
  Proof.
    iIntros "%Hstep [Hsi Hwps]".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iCombine "Hsi Hwps" as "Hwps".
    invert_threadpool_step.
    - (* Case: [threadpool_step] is immitated by a [thread_step]. *)
      rewrite <- Hdomeq in Htstep.
      iPoseProof (wptp_tstep $! Hlookup Htstep with "Hwps") as "Hwps". (* Use [wptp_tstep]. *)
      iModFL "Hwps".
      destruct μ as [[ι' mforked] | ]; last first.
      + (* Subcase: the step did not fork any new threads. *)
        subst π2.
        iDestruct "Hwps" as "(Hsi & Hwps)".
        iExists []. iFrame.
        iPureIntro. intros ι' Hin. by apply not_elem_of_nil in Hin.
      + (* Subcase: the step results in a forked thread. *)
        destruct Hμ as [Hfresh Heq_π2]. subst π2.
        iDestruct "Hwps" as "(%φ' & %γ & Hsi & Hwps)".
        iExists [(ι', (γ, φ'))].
        rewrite fmap_insert.
        iFrame.
        iPureIntro. intros ι'' Hin. apply list_elem_of_singleton in Hin as ->.
        rewrite Hdomeq. apply not_elem_of_dom.
        assert (ι ≠ ι') as Hneq_ι.
        { intros Heq_ι. subst ι'. rewrite lookup_insert_eq in Hfresh. discriminate Hfresh. }
        rewrite lookup_insert_ne in Hfresh; last exact Hneq_ι.
        exact Hfresh.
    - (* Case: [threadpool_step] is a join. *)
      iDestruct "Hwps" as "(Hsi & Hwps)".
      iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%γ & %φ & %Hlookup_p & Hsaved & Hwp & Hwps)".
      case (πp !! ι') eqn:Hlookup_p'.
      + (* Case: the join was successful. *)
        destruct p as [γ' φ'].
        assert (∃ o, π1 !! ι' = Some (inject2 o) ∧ e = k o) as (o & Hlookup' & Heq_e).
        { unfold attempt_join in Hattempt.
          assert (is_Some (π1 !! ι')) as [e' Hlookup'].
          { apply elem_of_dom. setoid_rewrite <- Hdomeq.
            apply (elem_of_dom πp ι'). exists (γ', φ'). exact Hlookup_p'. }
          rewrite Hlookup' in Hattempt.
          destruct e'; inversion Hattempt; try discriminate; subst; rewrite Hlookup'.
          - exists (O2Ret a). split; reflexivity.
          - exists (O2Throw e0). split; reflexivity. }
        subst e.
        assert (ι ≠ ι') as Hneq.
        { intros Heq_ι. subst ι'. rewrite Hlookup' in Hlookup.
          inversion Hlookup as [Heq_stop]. destruct o; discriminate Heq_stop. }
        pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup') as Hlookup_del.
        iPoseProof (WPTP_extract_outcome (delete ι π1) (delete ι πp) ι' with "[//] Hwps")
          as "(%γ'' & %φ'' & %Hlookup_p'' & #Hsaved' & Hwps & Ho)".
        pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup_p') as Hlookup_del_p.
        rewrite Hlookup_del_p in Hlookup_p''. inversion Hlookup_p''; subst γ'' φ''.
        iMod "Ho" as "#Ho".
        pose proof (fmap_fst_lookup _ _ _ _ Hlookup_p') as Hlookup_fmap.
        iPoseProof (ewp_join_inv $! Hlookup_fmap with "Hsaved' Ho Hsi Hwp") as "Hwp".
        iModFL "Hwp" as "(Hsi & Hwp)".
        iExists []. iFrame "Hsi".
        iPoseProof (WPTP_insert_post_delete $! Hlookup_del_p Hlookup_del with "Hwps Hsaved' Ho") as "Hwps".
        iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "$".
        iPureIntro. intros ι'' Hin. by apply not_elem_of_nil in Hin.
      + ewp_unfold (Stop CJoin ι' k). spec_state.
        iMod "Hwp".
        assert ((fst <$> πp) !! ι' = None) as Hnin.
        { apply not_elem_of_dom. rewrite dom_fmap. apply not_elem_of_dom. exact Hlookup_p'. }
        setoid_rewrite Hnin.
        by repeat iMod "Hwp".
  Qed.

  Lemma wptp_steps k π1 π2 σ1 σ2 πp :
    ⌜threadpool_steps k (σ1, π1) (σ2, π2)⌝ -∗
    state_interp (σ1, fst <$> πp) ∗ WPTP π1 πp ={⊤}[∅]▷=∗^k
    (∃ (l : list (thread * (gname * (outcome2 val exn → iProp Σ)))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, fst <$> insert_list l πp) ∗ WPTP π2 (insert_list l πp)).
  Proof.
    induction k as [|k IH] in  πp, π1, σ1 |-*; iIntros "%Hsteps Hwps".
    - inversion_clear Hsteps. simpl.
      iExists []. iFrame.
      iPureIntro; simpl; intros ? HF.
      by apply not_elem_of_nil in HF.
    - inversion_clear Hsteps as [|?? [σ1' π1']].
      simpl.
      iPoseProof (wptp_step $! H with "Hwps") as "Hwps".
      iModFL "Hwps" as "(%l & %Hl & Hwps)".
      iPoseProof (IH $! H0 with "Hwps") as "Hwps".
      iApply (step_fupdN_wand with "Hwps").
      iIntros "(%l' & %Hl' & Hwps)".
      iExists (l' ++ l).
      rewrite insert_list_app.
      iFrame.
      iPureIntro.
      intros ι' Hin.
      rewrite fmap_app in Hin; apply elem_of_app in Hin.
      destruct Hin.
      + specialize (Hl' ι' H1).
        by apply not_elem_of_insert_list in Hl' as [_ Hndom].
      + apply Hl, H1.
  Qed.

  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy k σ1 σ2 π2 ι e Φ :
    ⌜threadpool_steps k (σ1, {[ι:=e]}) (σ2, π2)⌝ -∗
    (∃ γ, state_interp (σ1, {[ι:=γ]}) ∗
          saved_pred_own γ DfracDiscarded (λ o, ⌜Φ o⌝)%I ∗
          ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) ={⊤}[∅]▷=∗^k
    (∀ ι' e, ⌜π2 !! ι' = Some e⌝ ={⊤}[∅]▷=∗
      ⌜not_stuck e σ2 (dom π2)⌝ ∗
      (∀ o, ⌜π2 !! ι = Some (inject2 o)⌝ -∗ |={⊤}=> □ ⌜Φ o⌝)).
  Proof.
    iIntros "%Hsteps (%γ & Hsi & Hsaved & Hwp)".
    iPoseProof (ewp_wand with "Hwp []") as "Hwp".
    { iIntros (o) "%Ho". instantiate (1:=λ o, (□ ⌜Φ o⌝)%I).
      by iModIntro. }
    iCombine "Hsi Hsaved Hwp" as "Hwps".
    rewrite wp_wptp.
    instantiate (1 := ι).
    remember {[ι := (γ, λ o, ⌜Φ o⌝)%I]} as πp.
    replace {[ι:=γ]} with (fst <$> πp) by (rewrite Heqπp map_fmap_singleton; reflexivity).
    iPoseProof (wptp_steps $! Hsteps with "Hwps") as "Hwps".
    iApply (step_fupdN_wand with "Hwps").
    iIntros "(%l & %Hl & Hsi & Hwps)".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iIntros (ι' e' Hlookup).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%γ' & %φ' & %Hlookup_p & Hsaved & Hwp & Hwps)".
    iCombine "Hsi Hwp" as "Hwp".
    iPoseProof (EWP_not_stuck_post with "Hwp") as "Hwp".
    rewrite dom_fmap_L Hdomeq.
    iModFL "Hwp" as "($ & Hpost)".
    assert (insert_list l πp !! ι = Some (γ, (λ o, ⌜Φ o⌝)%I)) as Hlookup_orig.
    { rewrite insert_list_lookup_not_in.
      - by rewrite Heqπp lookup_singleton_eq.
      - intros Hin%Hl. rewrite Heqπp dom_singleton in Hin.
        apply Hin. by apply elem_of_singleton. }
    case (decide (ι' = ι)) as [Heq_ι | Hneq].
    - subst ι'. iIntros (o Hlookup').
      rewrite Hlookup_orig in Hlookup_p.
      rewrite Hlookup' in Hlookup.
      inversion Hlookup_p; subst γ' φ'.
      inversion Hlookup; subst e'.
      by iApply ("Hpost" $! o eq_refl).
    - iIntros (o Hlookup_og).
      pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup_og) as Hlookup_del_π2.
      iPoseProof (WPTP_extract_outcome (delete ι' π2) (delete ι' (insert_list l πp)) ι with "[//] Hwps")
        as "(%γ'' & %φ'' & %Hlookup_p' & _ & _ & HΦ)".
      rewrite lookup_delete_ne in Hlookup_p'; last exact Hneq.
      rewrite Hlookup_orig in Hlookup_p'. inversion Hlookup_p'; subst γ'' φ''.
      done.
  Qed.

  Lemma ewp_adequacy m F n ι e σ1 σ2 π2 k Φ :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (∃ γ, state_interp (σ1, {[ι:=γ]}) ∗
       saved_pred_own γ DfracDiscarded (λ o, ⌜Φ o⌝)%I ∗
       ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    threadpool_steps k (σ1, {[ι := e]}) (σ2, π2) →
    (* then no thread is stuck *)
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hsat Hsteps.
    eapply SAT_mono in Hsat; last iApply (wptp_adequacy k σ1 σ2 π2 $! Hsteps).
    apply SAT_elim_iterated in Hsat; last first.
    { intros P HsatP; by eapply SAT_fupd, SAT_later, SAT_fupd. }
    split.
    - (* Prove that no thread is stuck. *)
      intros ι' e' Hlookup.
      eapply SAT_mono in Hsat; last first. (* Instantiate inside SAT. *)
      { iIntros "Hx". iSpecialize ("Hx" $! ι' e' Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      eapply SAT_mono in Hsat; last first. (* Symmetry inside SAT. *)
      { iIntros "[Hns Ho]". iCombine "Ho Hns" as "Hx". iExact "Hx". }
      rewrite -SAT_frame_cons in Hsat.
      by apply SAT_elim in Hsat.
    - (* Prove that if the initial thread has terminated,
         then the postcondition holds. *)
      intros o Hlookup.
      eapply SAT_mono in Hsat; last first. (* Instantiate inside SAT. *)
      { iIntros "Hx". iSpecialize ("Hx" $! ι (inject2 o) Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      rewrite -SAT_frame_cons in Hsat.
      eapply SAT_mono in Hsat; last first.
      { iIntros "HΦ". iSpecialize ("HΦ" $! o Hlookup). iExact "HΦ". }
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
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
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
    iMod (saved_pred_alloc
            (savedPredG0 := (@osiris_savedPredG Σ (@osiris_inG Σ (I x))))
            (λ o, ⌜Φ o⌝)%I DfracDiscarded)
           as "(%γ & Hsaved)"; first done.
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
  eapply (SAT_ghost_map_alloc (∅ : gmap locations.loc (list locations.loc))) in Hsat as [γ Hsat].
  do 2 apply SAT_unframe_resource in Hsat.
  pose (hg := (@OsirisGS Σ _ _ Hgen Hgen' _ γ)).
  exists hg.
  eapply SAT_mono; last apply Hsat.
  iIntros "(Harri & _ & Hgen & _ & _ & Hgen' & _ & _)".
  iFrame "Hgen Hgen'".
  iExists ∅. iFrame "Harri". iPureIntro.
  intros a ls Hlookup. rewrite lookup_empty in Hlookup. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations under open gFunctors [Σ]. *)

  Lemma osiris_adequacy Σ `{!osirisGpreS Σ} (e : micro val exn) ι σ1 π2 σ2 k Φ :
    (* If we can show [EWP e1 {{ True }}] with the ghost state provided by [Σ]. *)
    (∀ `{!osirisGS Σ}, ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
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
    (∀ `{!osirisGS osirisΣ}, ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
    threadpool_steps k (σ1, {[ι :=e]}) (σ2, π2) →
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hwp. eapply osiris_adequacy, Hwp. apply _.
  Qed.

End adequacy.
