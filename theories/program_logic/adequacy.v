From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe wp helpers.


Section Adequacy.
  Context `{!osirisGS Σ}.

  (* [wp_preservation] is an iterated version of [wp_step]. *)
  Lemma wp_preservation n :
    forall {A σ1 σn} {m1 mn : free A} {s E φ},
    nsteps step n (σ1, m1) (σn, mn) →
    state_interp σ1 -∗
    wp s E m1 φ ={E,∅}=∗
    |={∅}▷=>^n |={∅,E}=> state_interp σn ∗ wp s E mn φ.
  Proof.
    induction n as [ | n IHn] => A σ1 σn m1 mn s E φ /=.
    { iIntros ([->->]%invert_nsteps_0%pair_equal_spec) "$$".
      iApply fupd_mask_subseteq; by apply empty_subseteq. }
    { iIntros (([σm mm]&Hstep&Hsteps)%nsteps_S_inv) "??".
      iPoseProof ((wp_step Hstep) with "[$][$]") as ">Hstep".
      iModIntro.
      iApply ((step_fupdN_wand _ _ 1) with "Hstep").
      iIntros "H".
      destruct n.
      { apply invert_nsteps_0 in Hsteps.
        simplify_eq/=. done. }
      { simpl. iMod "H" as "[??]".
        iPoseProof (IHn _ _ _ _ _ _ _ _ Hsteps) as "IH".
        by iMod ("IH" with "[$][$]"). } }
  Qed.

End Adequacy.

Section Adequacy.
  Import uPred.

  Let inverse_modalities {Σ} `(!invGS_gen HasNoLc Σ) (P : iProp Σ) n :
    (|={∅}▷=>^n |={∅}=> P) ⊢
    |={∅}=> |={∅}▷=>^n P.
  Proof.
    destruct n.
    - simpl. by iMod 1.
    - iIntros"H".
      by iMod (step_fupdN_S_fupd with "H") as "H".
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [required_cmras] describes requirements on [Σ] (what should be in Σ?), in
     order to define an instance of [osirisGS _] later. *)

  Class required_cmras Σ :=
    {
      heap : inG Σ (reservation_map.reservation_mapR (agreeR positiveO)) ;
      heap' : inG Σ (gmap_view.gmap_viewR loc (leibnizO val)) ;
      heap'' : inG Σ (gmap_view.gmap_viewR loc (leibnizO gname)) ;
      wsat_inv : inG Σ (gmap_view.gmap_viewR positive (laterO (iPropO Σ)));
      wsat_enabled : inG Σ coPset.coPset_disjR;
      wsat_disabled : inG Σ (gset.gset_disjR positive) ;
      lc : inG Σ (authR natUR)
    }.

  (* These two local lemmas are required in order to recover the requirements of
     [gen_heap_init] and [step_fupdN_soundness_no_lc]. *)
  Let required_camras_heap {Σ} :
    required_cmras Σ → gen_heapGpreS loc val Σ.
  Proof. intros []; by repeat constructor. Qed.
  Let required_camras_inv {Σ} :
    required_cmras Σ → invGpreS Σ.
  Proof. intros []; by repeat constructor. Qed.

  (* ------------------------------------------------------------------------ *)

  (* [wp_pre_adequacy] is a lemma used to start the adequacy proof. *)

  Let wp_pre_adequacy :
    ∀ {Σ : gFunctors},
    ∀ {P : iProp Σ} {_: Plain P},
    required_cmras Σ →
    ∀ n : nat,
    (⊢ ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
         (Hinv : invGS_gen HasNoLc Σ),
       state_interp ∅
       ={⊤,∅}=∗ |={∅}▷=>^n P)%I →
    ⊢ P.
  Proof.
    iIntros (Σ HΣ P HP n H).

    (* First, we use an Iris soundness lemma to introduce the required
       modalities. The soundness lemma will also provide us with a valid [Hinv]
       to pass to [H]. *)
    eapply (step_fupdN_soundness_no_lc _ n O).
    iIntros (Hinv) "_". (* We do not care about later credits. *)

    (* Now, initialize the heap. *)
    iPoseProof (@gen_heap_init loc _ _ val Σ _ ∅) as ">(%Hstore&?&_)".
    iAssert (state_interp ∅) with "[$]" as "?".

    (* Use the hypothesis on the provability of [P]. *)
    iApply (H $! Hstore Hinv with "[$]").

    (* cmras needed to use the heap and invariants are present in Σ. *)
    Unshelve. all: by eauto.
  Qed.

  (* Main result: the adequacy lemma. *)

  Lemma wp_adequacy {A} `{!required_cmras Σ}
        {m1 n σ2 m2} (s: stuckness) (φ: Prop) :
    nsteps step n (∅, m1) (σ2, m2) →
    (⊢ ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
         (Hinv : invGS_gen HasNoLc Σ),
       let _ : osirisGS Σ := OsirisG Σ Hinv Hstore in
       |={⊤}=> ∃ (φ' : A → iProp Σ),
       wp s ⊤ m1 φ' ∗
       ( state_interp σ2 -∗
         wp s ⊤ m2 φ' -∗
         |={⊤,∅}=> ⌜φ⌝)) →
    φ.
  Proof.
    intros Hsteps H.

    (* First: setup the iterated later/fupd modalities using the previous local
              lemma and enter the Iris Proof Mode. *)
    eapply pure_soundness.
    eapply (wp_pre_adequacy _ n).
    iIntros (Hstore Hinv) "Hsi".

    (* Use our hypothesis on the provability of the [wp] and its consequence. *)
    iMod (H $! Hstore Hinv)  as "(%φ' & ? & Hφ)".

    (* Use preservation of the [wp] and [state_interp] by [n] steps. *)
    iMod ((wp_preservation _ Hsteps) with "[Hsi][$]") as "H".
    { done. } (* FIXME: replacing [Hsi] by [$] above should work. *)

    (* Inverse some modalities. *)
    iApply (inverse_modalities Hinv ⌜φ⌝ n).

    (* Use our preservation hypothesis to retrieve the state and [wp]. *)
    iApply (step_fupdN_wand with "H").
    iMod 1 as "[? Hwp]".

    (* We have [wp _ _ m2 _] and [state_interm σ2]. Hence, [Hφ] gives us [φ]. *)
    iApply ("Hφ" with "[$][$]").
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* The following lemma is a corollary of the adequacy lemma:
     Let [φ] be a predicate over some type [A].
     If [wp _ _ m1 (λ v, ⌜φ v⌝)] holds in the Iris logic, and if [(∅, m1)] steps
        to [(σn, mn)],
     then [mn] is not stuck, and if it represents a value [v], then [φ v] holds.
   *)
  Lemma wp_adequacy' {A} `{!required_cmras Σ}
        {m1 n σn mn} s(φ : A → Prop) :
    (* [(∅, m1)] reduces to ([σn, mn)] in n steps. *)
    nsteps step n (∅, m1) (σn, mn) →

    (* [wp _ _ m1 (λ v, ⌜φ v⌝)] holds *)
    (⊢ ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
         (Hinv : invGS_gen HasNoLc Σ),
       let _ : osirisGS Σ := OsirisG Σ Hinv Hstore in
       (wp s ⊤ m1 (λ a, ⌜ φ a ⌝))) →

    (* Then, the resulting configuration is not stuck and should [mn] represent
       a value [v], [φ v] holds. *)
    (¬ stuck (σn, mn)) ∧ ∀ a, mn = Ret a → φ a.
  Proof.
    intros Hsteps H.

    (* First, we define an new pure proposition [φ']. It is equivalent to the
       conclusion of the lemma. *)
    let φ' := constr:(match mn with
              | ret v => φ v
              | _ => can_step (σn, mn)
              end) in
    apply (@apply φ' (¬ stuck (σn, mn) ∧ (∀ a : A, mn = Ret a → φ a))).
    { intros Hφ.
      split.
      { intros ?.
        destruct mn; eauto using invert_stuck_ret, can_step_not_stuck. }
      by intros ?->. }

    (* Now that the goal is easier to understand, we use the adequacy lemma.
       It provides us with the store- and invariants-related hypotheses to use
       the provability of [wp _ _ m1 (λ v, ⌜φ v⌝)]. *)
    eapply (wp_adequacy s _ Hsteps).
    iIntros (Hstore Hinv).

    iExists (λ v, ⌜φ v⌝)%I.
    iPoseProof (H $! _ _) as "$". iModIntro.

    (* We now have access to the state interp and [wp] of the final
       configuration, which is enough to prove non-stuckness and the
       postcondition. *)
    iIntros "?Hwp".

    (* We proceed by case-analysis on [mn]. *)
    destruct mn; wp_unfold_all.
    { (* Case: [mn = Ret _]. *)
      iMod ("Hwp" with "[$]") as ">[_$]".
      iApply fupd_mask_intro; [ done | by iIntros "_" ]. }
    all: iMod ("Hwp" with "[$]") as "[%?]"; done.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [wp_safe] states that if [wp _ _ m (λ a, ⌜ φ a ⌝)] holds, [(∅, m)] is a
     safe configuration that satisfies [φ]. *)
  Lemma wp_safe {A} `{!required_cmras Σ}
        {m1} (φ : A → Prop) :
    (* [wp _ _ m1 (λ v, ⌜φ v⌝)] holds *)
    (⊢ ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
         (Hinv : invGS_gen HasNoLc Σ),
       let _ : osirisGS Σ := OsirisG Σ Hinv Hstore in
       (wp NotStuck ⊤ m1 (λ a, ⌜ φ a ⌝))) →
    safe (∅, m1) (λ _ a, φ a).
  Proof.
    intro H.
    apply prove_safe.
    intros n σn mn Hsteps.
    pose proof (steps_nsteps Hsteps) as [n' Hn'steps]; clear n Hsteps.

    (* Apply the corollary of the adequacy lemma stated and poven above. *)
    apply (wp_adequacy' NotStuck _ Hn'steps).
    iIntros (??).
    iApply H.
  Qed.

(* TODO where do we go from here? *)
End Adequacy.
