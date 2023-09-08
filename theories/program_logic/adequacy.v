From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe wp helpers.

(* This file contains the adequacy theorem (i.e. correction of the WP).
   The main result is provided by [adequacy_corollary]:
     For any type [A],
             computation [m1 : micro A],
             natural integer [n],
             physical heap [σn],
             computation[mn : micro A],
             postcondition [φ : A → iProp Σ],

         if [(∅, m1)] reduces to [(σn, mn)] in [n] steps,
         and if (wp s ⊤ m1 (λ a, ⌜ φ a ⌝)) holds in Iris (given the required
                cmras),
         then
          - the configuration [(σn, mn)] is not stuck,
          - should [mn] represent a value [v], [φ v] holds.

   This result is slightly different from the adequacy theorem of Iris. The main
   difference is the empty initial heap: in Iris an additional assertion
   [state_interp σ1] is requested. This allows their result to hold for any
   (potentially non-empty) initial heap.
   In Osiris, we assume that the heap is initially empty. This is justified by
   the form of closed proofs of programs and the bind rule.
   Indeed, upon proving a program [P] depending on a libraries [L1], ..., [Ln],
   the closed  proof of [P] is of the form:
         [WP (v1 ← eval EnvNil L1 ;
              ...
              vn ← eval (EnvCons "L(n-1)" v(n-1) ...) Ln ;
              eval (EnvCons "Ln" vn ...) P) {{ φ }}].
   In other words, we re-evaluate all dependencies of a program needs before
   starting  the proof of the program. Hence, having a non-empty initial state
   [σ1] is unnecessary.
   Rule WP-bind2 ensures that given a proof of [P] that assumes those of [L1],
   ..., [Ln] is enough to prove this statement. *)



Section Adequacy.
  Import uPred.

  (* This technical lemma is used in the adequacy proof. *)
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
      (* -------------------------------------------------------------------- *)
      (* Heap-related cmras. *)

      (* Detailed explanations on the heap are provided in the first two
         comments of the file [iris/base_logic/lib/gen_heap.v] of the Iris
         repository.  *)
      heap_map : inG Σ (reservation_map.reservation_mapR (agreeR positiveO)) ;
      heap_vals : inG Σ (gmap_view.gmap_viewR loc (leibnizO val)) ;
      heap_gnames : inG Σ (gmap_view.gmap_viewR loc (leibnizO gname)) ;

      (* -------------------------------------------------------------------- *)
      (* Invariant-related cmras.
         Iris From the Ground Up
         (https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
         provides more details on invariants and their definition in Iris. *)

      (* [wsat_inv] is used to define the mapping from names to assertions one
         can see in the definition of the world satisfaction [W] and the
         definitions of invariants. *)
      wsat_inv : inG Σ (gmap_view.gmap_viewR positive (laterO (iPropO Σ)));
      (* [wsat_enabled] is used to remember the name of invariants that hold. *)
      wsat_enabled : inG Σ coPset.coPset_disjR;
      (* [wsat_disabled] is used to remember the name of invariants which are
         not satisfied. *)
      wsat_disabled : inG Σ (gset.gset_disjR positive) ;

      (* Used for later credits. Despite our choice not to support them, this
         algebra is required to define an instance of [invGS_gen] used below.
         TODO : remove the following constraint on [Σ] and repair the proofs. *)
      lc : inG Σ (authR natUR)
    }.

  (* These two lemmas are required in order to recover the requirements of
     [gen_heap_init] and [step_fupdN_soundness_no_lc]. *)
  Let required_camras_heap {Σ} :
    required_cmras Σ → gen_heapGpreS loc val Σ.
  Proof. intros []; by repeat constructor. Qed.
  Let required_camras_inv {Σ} :
    required_cmras Σ → invGpreS Σ.
  Proof. intros []; by repeat constructor. Qed.

  (* ------------------------------------------------------------------------ *)

  (* [wp_pre_adequacy] is a lemma used to start the adequacy proof.
     The lemma:
     - provides:
       + the required resources to use the heap and invariants,
       + an empty heap
     - puts the goal behind the right iterated modality, i.e. the one that will
       appear in [wp_adequacy]. *)

  Local Lemma wp_pre_adequacy :
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
        {m1 n σn mn} (s: stuckness) (φ: Prop) :
    (* Assuming [(∅, m1)] steps to [(σn, mn)] in [n] steps. *)
    nsteps step n (∅, m1) (σn, mn) →

    (⊢ (* If the logical heap and invariants can be used, *)
     ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
       (Hinv : invGS_gen HasNoLc Σ),
       let _ : osirisGS Σ := OsirisG Σ Hinv Hstore in

       (* and the following holds, *)
       |={⊤}=> (* There exists a post-condition [φ'] s.t. *)
               ∃ (φ' : A → iProp Σ),
               (* [m1] is correct wrt. [φ'], *)
               wp s ⊤ m1 φ' ∗
               ( (* and if the proof of [mn] and state of [σn] are sufficient to
                    prove [φ]. *)
                 state_interp σn -∗
                 wp s ⊤ mn φ' -∗
                 |={⊤,∅}=> ⌜φ⌝)) →

    (* Then [φ] holds outside of Iris. *)
    φ.
  Proof.
    intros Hsteps H.

    (* First: setup the iterated later/fupd modalities using the previous local
              lemma and enter the Iris Proof Mode. *)
    eapply pure_soundness, (wp_pre_adequacy _ n).
    iIntros (Hstore Hinv) "Hsi".

    (* Use our hypothesis on the provability of the [wp] and its consequence. *)
    iMod (H $! Hstore Hinv)  as "(%φ' & ? & Hφ)".

    (* Use preservation of the [wp] and [state_interp] by [n] steps. *)
    iMod ((wp_preservation _ Hsteps) with "[Hsi][$]") as "H".
    (*{ Set Printing Implicit. simpl. iFrame. } *)
    { done. } (* FIXME: replacing [Hsi] by [$] above should work.  It does not
                        because it needs to reduce the body of [Hsi] first. Use
                        [Set Printing Implicit] for more details. *)

    (* Inverse some modalities: push [ |={∅}=> ] behind the iterated
       modality. *)
    iApply (inverse_modalities Hinv ⌜φ⌝ n).

    (* It is possible to strip the iterated modality from both [H] and the
       goal. This is done in two steps: (1) apply a lemma stating the
       possibility of stripping the iterated modality. This consumes [H]. *)
    iApply (step_fupdN_wand with "H").
    (* (2) Introduce the hypothesis [H] without its modalities, i.e. an
       assertion of the form [ |={∅,⊤}=> X ∗ Y ].
       After the introduction, the goal is of the form [ |={∅}=> G ], it is
       possible to tacitly use FupTrans to prove [ |={∅,⊤}=> |={⊤,∅}=> G ]
       instead. Therefore, by monotony of [ |={∅, ⊤}=> ], it suffices to prove
       [ |={⊤,∅}=> G ] after introducing [ X ∗ Y ]. *)
    iMod 1 as "[? Hwp]".

    (* We have [wp _ _ m2 _] and [state_interm σ2]. Hence, [Hφ] gives us the
       result. *)
    iApply ("Hφ" with "[$][$]").
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* The following lemma is a corollary of the adequacy lemma:
     Let [φ] be a predicate over some type [A].
     If [wp _ _ m1 (λ v, ⌜φ v⌝)] holds in the Iris logic, and if [(∅, m1)] steps
        to [(σn, mn)] in n steps,
     then [mn] is not stuck, and if it represents a value [v], then [φ v]
          holds. *)
  Lemma adequacy_corollary {A} `{!required_cmras Σ}
        {m1 n σn mn} s (φ : A → Prop) :
    (* [(∅, m1)] reduces to ([σn, mn)] in n steps. *)
    nsteps step n (∅, m1) (σn, mn) →

    (* If [wp _ _ m1 (λ v, ⌜φ v⌝)] holds *)
    (⊢ (* given the required cmras, *)
     ∀ (Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable)
       (Hinv : invGS_gen HasNoLc Σ),
       let _ : osirisGS Σ := OsirisG Σ Hinv Hstore in
       (wp s ⊤ m1 (λ a, ⌜ φ a ⌝))) →

    (* Then,
        - the resulting configuration is not stuck, and
        - should [mn] represent a value [v], [φ v] holds. *)
    (¬ stuck (σn, mn)) ∧ ∀ a, mn = Ret a → φ a.
  Proof.
    intros Hsteps H.

    (* First, we define an new pure proposition [φ']. It implies the conclusion
       of the lemma and is easier to work with.
       Note: [φ'] is equivalent to the goal, but the proof only requires one
             way. *)
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
    iIntros (Hstore Hinv); iExists _.
    iPoseProof (H $! _ _) as "$". (* Frame the [WP m1 _] hypothesis. *)
    iModIntro.

    (* We now have access to the state interp and [wp] of the final
       configuration, which is enough to prove non-stuckness and the
       postcondition. *)
    iIntros "?Hwp".

    (* We proceed by case-analysis on [mn]. *)
    destruct mn; wp_unfold_all.
    { (* Case: [mn = Ret _].
               One only needs to prove that the post-condition is satisfied,
               which follows from the definition of [WP].
               As [∅ ⊆ ⊤], the modality can be removed. *)
      iMod ("Hwp" with "[$]") as ">[_$]".
      iApply fupd_mask_intro; [ done | by iIntros "_" ]. }

    (* In all of the other cases, the goal cannot be stuck (due to [can_step] in
       the definition of [WP]). *)
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
    apply (adequacy_corollary NotStuck _ Hn'steps).
    iIntros (??).
    iApply H.
  Qed.

End Adequacy.
