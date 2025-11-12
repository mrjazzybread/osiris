From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap.

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

  Lemma no_forking {A X} (e1 : micro A X) σ1 κs es σ2 :
    language.step ([e1], σ1) κs (es, σ2) →
    ∃ e2, es = [e2].
  Admitted.

  Lemma no_forkings {A X} k (e1 : micro A X) σ1 κs es σ2 :
    language.nsteps k ([e1], σ1) κs (es, σ2) →
    ∃ e2, es = [e2].
  Admitted.

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

  Lemma ewp_steps {A X} m F n k (e1 : micro A X) es σ1 σ2 κs Φ :
    SAT m F [view ⊤; supply n] (state_interp σ1 ∗ EWP e1 @ ⊤ <|⊥|> {{ Φ }}) →
    language.nsteps k ([e1], σ1) κs (es, σ2) →
    ∃ e2, es = [e2] ∧
    ∃ n', SAT m F [view ⊤; supply n'] (state_interp σ2 ∗ EWP e2 @ ⊤ <|⊥|> {{ Φ }}).
  Proof.
    induction k as [|k IH] in n, e1, σ1, κs, Φ |-*; intros Hsat Hsteps.
    - revert Hsat. inversion_clear Hsteps. exists e1. split; [ reflexivity | ].
      exists n. apply Hsat.
    - revert Hsat. inversion_clear Hsteps as [|?? [t1' σ1']]. intros Hsat.
      inversion H. simpl. inversion H1. subst.
      apply singleton_app_cons in H5 as (-> & -> & ->).
      simpl in *.
      destruct (no_forking _ _ _ _ _ H) as (e0' & ->).
      destruct (no_forkings _ _ _ _ _ _ H0) as (e0'' & ->).
      exists e0''; split; [ reflexivity | ].
      inversion H2; subst.
      clear H1 H2.
      eapply ewp_step in Hsat as (n' & Hsat); last apply H3.
      apply (IH _ _ _ κs0 _) in Hsat as (? & Heq & [n'' Hsat]).
      inversion_clear Heq.
      exists n''; apply Hsat.
      assumption.
  Qed.

  Lemma ewp_adequacy {A X} m F n κs (e1 : micro A X) es σ1 σ2 k Φ :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (state_interp σ1 ∗
       EWP e1 @ ⊤ <|⊥|> {{ λ v, ⌜Φ v⌝ }})%I →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    @language.nsteps (osiris_lang) k ([e1], σ1) κs (es, σ2) →
    (* then if the computation terminates in a value, it satisfies the postcondition *)
    (∃ e2, es = [e2] ∧ not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> Φ o)).
  Proof.
    intros Hsat Hsteps.
    eapply ewp_steps in Hsat as (e2 & -> & n' & Hsat); last apply Hsteps.
    exists e2; split; [ reflexivity | ].
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
Lemma SAT_wp_adequacy `{!invGpreS Σ} (X: Type) (I: X → osirisGS Σ) κs σ1 σ2 (e : micro val exn) es n k P Φ:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
     let i: osirisGS Σ := I x in
    SAT Alloc F [@view Σ (@invGS_wsat HasNoLc Σ (@osiris_invGS Σ (I x))) ⊤; @supply Σ (@invGS_lc HasNoLc Σ (@osiris_invGS Σ (I x))) n] (state_interp σ1 ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e @ ⊤ <|⊥|> {{ λ v, ⌜Φ v⌝ }}) →
  (* then any k-step execution is safe: *)
  language.nsteps k ([e], σ1) κs (es, σ2) →
  (∃ e2, es = [e2] ∧ not_stuck e2 σ2 ∧ (∀ o, outcome2_opt e2 = Some o -> Φ o)).
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


(* Definition of adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : language.expr Λ) (σ1 : state Λ)
    (φ : language.val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : language.val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Lemma SAT_wp_adequate `{!invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 n s (e : micro val exn) φ P:
  (* allocate the initial state interpretation *)
  (∀ (iv: invGS Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: osirisGS Σ := I x in
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp σ1 ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ EWP e @ ⊤ <|⊥|> {{ λ v, ⌜φ v⌝%I }}) →
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
