From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

From osiris.lang Require Import locations.
From osiris.program_logic Require Import ewp basic_rules tactics.
From osiris.adequacy.satisfiable Require Import satisfiable.
From osiris.adequacy Require Import base_logic_extension.

Include ewp_rules_tactics.

(* If a computation [e1] can step, then we know that
   [is_ewp_case e1 = None]. *)

Lemma if_can_step_is_step {A X} σ1 (e1 : micro A X) σ2 e2 :
  step (σ1, e1) (σ2, e2) ->
  is_ewp_case e1 = EStep.
Proof.
  intros Hwp.
  destruct_step; reflexivity.
Qed.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  Lemma ewp_step {A X} m F E Ψ (e1 : micro A X) σ1 e2 σ2 Φ n :
    semantics.step.step (σ1, e1) (σ2, e2) →
    SAT m F [view E; supply n]
      (state_interp σ1 ∗ ewp_def E e1 Ψ Φ) →
    ∃ n', SAT m F [view E; supply n']
      (state_interp σ2 ∗ ewp_def E e2 Ψ Φ).
  Proof.
    intros Hstep Hsat. eapply SAT_mono in Hsat; last first.
    { iIntros "[HSI Hwp]". rewrite ewp_unfold /ewp_pre.
      rewrite (if_can_step_is_step σ1 e1 σ2 e2 Hstep).
      iSpecialize ("Hwp" $! σ1 0 [] [] 0 with "HSI").
      iExact "Hwp". }
    eapply SAT_fupd in Hsat.
    eapply SAT_mono in Hsat; last first.
    { iIntros "[_ Hwp]". iSpecialize ("Hwp" $! σ2 e2 Hstep). iExact "Hwp". }
    eapply (SAT_frame_resource _ (view ∅)) in Hsat; last apply _.
    eapply SAT_unframe_resource in Hsat.
    eapply SAT_fupd in Hsat.
    eapply SAT_later in Hsat.
    eapply SAT_fupd in Hsat.
    eexists _. eapply Hsat.
  Qed.

  Lemma ewp_not_stuck {A X} m F E (e : micro A X) σ Φ n:
    SAT m F [view E; supply n] (state_interp σ ∗
                                  EWP e @ E <|⊥|> {{ Φ }}) →
    not_stuck e σ.
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
      eapply SAT_mono with (Q := (|={E, ∅}=> ⌜can_step (σ, e)⌝)%I)
                           in Hsat.
      { (* Get [reducible e σ] from [SAT m F [view E; supply n] (|={E,∅}=> ⌜can_step (σ, e)⌝)]. *)
        eapply SAT_fupd in Hsat. apply SAT_elim in Hsat as [(σ2 & e2) Hstep].
        eexists [], e2, σ2, []; split; [ apply Hstep | reflexivity ].
      }
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

  Lemma singleton_app_cons {A} (x y : A) l1 l2 :
    [x] = l1 ++ y :: l2 ->
    l1 = [] ∧ y = x ∧ l2 = [].
  Proof.
    intros Heq.
    assert (l1 = []) as ->.
    { destruct l1; first done.
      destruct l1; discriminate Heq. }
    assert (l2 = []) as ->.
    { destruct l2; [ done | discriminate Heq ]. }
    by inversion_clear Heq.
  Qed.

  Lemma ewp_steps {A X} m F n k (e1 e2 : micro A X) σ1 σ2 Φ :
    SAT m F [view ⊤; supply n] (state_interp σ1 ∗ EWP e1 @ ⊤ <|⊥|> {{ Φ }}) →
    nsteps k (σ1, e1) (σ2, e2) →
    ∃ n', SAT m F [view ⊤; supply n'] (state_interp σ2 ∗ EWP e2 @ ⊤ <|⊥|> {{ Φ }}).
  Proof.
    induction k as [|k IH] in n, e1, e2, σ1, Φ |-*; intros Hsat Hsteps.
    - revert Hsat. inversion_clear Hsteps.
      exists n. apply Hsat.
    - revert Hsat. inversion_clear Hsteps as [|?? [t1' σ1']]. intros Hsat.
      eapply ewp_step in Hsat as (n' & Hsat); last apply H.
      eapply IH in Hsat as [n'' Hsat]; last apply H0.
      exists n''; apply Hsat.
  Qed.

  Lemma ewp_adequacy {A X} m F n (e1 e2 : micro A X) σ1 σ2 k Φ :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (state_interp σ1 ∗
       EWP e1 @ ⊤ <|⊥|> {{ λ v, ⌜Φ v⌝ }})%I →
    (* and we take a k-step execution to [e2] and some state [σ2] *)
    nsteps k (σ1, e1) (σ2, e2) →
    (* then if the computation terminates in a value, it satisfies the postcondition *)
    (not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> Φ o)).
  Proof.
    intros Hsat Hsteps.
    eapply ewp_steps in Hsat as (n' & Hsat); last apply Hsteps.
    split; [ eapply ewp_not_stuck; apply Hsat | ].
    intros o Ho.
    rewrite -SAT_frame_cons in Hsat.
    eapply ewp_postcondition in Hsat; last apply Ho.
    eapply SAT_elim; apply Hsat.
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
Lemma SAT_ewp_adequacy `{!invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 σ2 (e1 e2 : micro val exn) n k P Φ:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS_gen HasNoLc Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
     (* we ensure that all inferences point to the right instances *)
     let i: osirisGS Σ := I x in
     let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in
    SAT Alloc F [view ⊤; supply n] (state_interp σ1 ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e1 @ ⊤ <|⊥|> {{ λ v, ⌜Φ v⌝ }}) →
  (* then any k-step execution is safe: *)
  nsteps k (σ1, e1) (σ2, e2) →
  (not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> Φ o)).
Proof.
  intros Halloc Hwp Hsteps.
  pose proof (SAT_intro (Σ := Σ)) as Hsat.
  eapply SAT_alloc_fancy_updates in Hsat as [Hi Hsat].
  eapply (Halloc Hi True%I) in Hsat as (x & Hsat); eauto; simpl in *.
  eapply SAT_mono in Hsat; last first.
  { iIntros "SI". iPoseProof (Hwp x) as "Hwp". iCombine "SI Hwp" as "Hx". iExact "Hx". }
  eapply (@ewp_adequacy Σ (I x)), Hsteps.
  eapply SAT_mono; last apply Hsat.
  { iIntros "([$ P] & Hwp)". by iApply "Hwp". }
Qed.

Lemma osiris_initial_allocation `{!osirisGpreS Σ} σ (_ : invGS_gen HasNoLc Σ) (F : iProp Σ) :
  SAT Alloc F [view ⊤; supply 0] True →
  ∃ (h: osirisGS Σ),
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in
    SAT Alloc F [view ⊤; supply 0] (state_interp σ).
Proof.
  intros Hsat.
  eapply SAT_frame_resource with (R := view _) in Hsat; last apply _.
  eapply SAT_frame_resource with (R := supply _) in Hsat; last apply _.
  eapply (SAT_gen_heap_init σ) in Hsat as [Hgen Hsat].
  do 2 apply SAT_unframe_resource in Hsat.
  pose (hg := (@OsirisGS Σ _ _ Hgen)). exists hg.
  eapply SAT_mono; last apply Hsat.
  iIntros "(Hgen & Hpts & Hmeta & _)".
  rewrite /state_interp /=. by iFrame.
Qed.

(* We show a first adequacy statement, parameterised by some gFunctors [Σ]
   such that [osirisGpreS Σ] holds. *)

Definition osiris_adequacy Σ `{!osirisGpreS Σ} (e1 : micro val exn) σ1 e2 σ2 φ k :
  (* If we can show [EWP e1 {{ λ v, φ v }}] with the ghost state provided by [Σ]. *)
  (∀ `{!osirisGS Σ}, ⊢ EWP e1 @ ⊤ <|⊥|> {{ λ v, ⌜φ v⌝ }}) →
  (* Then any k-step execution of [e1] leads to a state such that: *)
  nsteps k (σ1, e1) (σ2, e2) →
  (* That state is not stuck ∧
     If that state is final, then it satisfies the postcondition [φ]. *)
  (not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> φ o)).
Proof.
  intros Hwp.
  eapply SAT_ewp_adequacy with (X := osirisGS Σ) (P := λ _, bi_pure True).
  - intros iv F Hsat_init.
    have [h Hsat] := (osiris_initial_allocation σ1 iv F Hsat_init).
    exists h.
    eapply SAT_mono, Hsat.
    apply bi.sep_True_2.
  - apply Hwp.
Qed.

(* We now show that the previous adequacy statement can be instantiated
   by providing a minimal [Σ] such that [osirisGpreS Σ] holds.*)

(* Provide the ghost state for invariants and the store. *)
Definition osirisΣ : gFunctors := #[invΣ; gen_heapΣ loc step.block].
(* Show that inclusion of [osirisΣ] in [Σ] is enough to instantiate [osirisGpreS Σ]. *)
Global Instance subG_heapGpreS {Σ} : subG osirisΣ Σ → osirisGpreS Σ.
Proof. solve_inG. Qed.

(* Example of an adequacy statement instantiated with a specific set of [gFunctors]. *)

Definition osiris_adequacy_closed (e1 : micro val exn) σ1 e2 σ2 φ k :
  (∀ `{!osirisGS osirisΣ}, ⊢ EWP e1 @ ⊤ <|⊥|> {{ λ v, ⌜φ v⌝ }}) →
  nsteps k (σ1, e1) (σ2, e2) →
  (not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> φ o)).
Proof.
  intros Hwp. eapply osiris_adequacy, Hwp. apply _.
Qed.
