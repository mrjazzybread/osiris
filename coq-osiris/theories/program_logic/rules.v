Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import wp tactics.
From osiris Require Import syntax semantics.

(** *Reasoning principles of [Osiris] wp-based Hoare triples *)

Section wp_rules.

  Context `{!osirisGS Σ}.

  Import wp_rules_tactics.

  (* ------------------------------------------------------------------------ *)
  (** *General properties about [WP] and [step] *)

  Lemma wp_can_step {R E} {σ} φ (m : micro R E) {M}:
    store_interp σ -∗
    wp NotStuck M m φ ={M, ∅}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros "SI Hwp".
    wp_unfold_all.
    destruct (wp.to_outcome m) eqn: Hm.
    { iMod "Hwp". iApply fupd_mask_intro; first set_solver.
      iIntros "_".
      to_outcome_is_Some Hm; [ iRight; iRight | iRight; iLeft ];
      iPureIntro; eauto. }
    { spec_state. iPureIntro.
      left. by apply can_step_reducible. }
  Qed.

  Lemma wp_can_step' {R E} {σ φ} (m : micro R E) {M}:
    store_interp σ -∗
    wp NotStuck M m φ ={M}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros.
    iPoseProof (wp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

  Lemma wp_step {R E} {σ σ'} {m n : micro R E} {φ}:
    step (σ, m) (σ', n) →
    store_interp σ -∗
    £ 1 -∗
    WP m {{ φ }} ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    (store_interp σ' ∗ WP n {{ φ }}).
  Proof.
    intro Hstep.
    iIntros "Hsi H£ Hwp".
    wp_unfold m.
    pose proof (step_not_outcome Hstep) as ->.
    spec_state. iModIntro.
    eassert (prim_step m σ _ _ _ _).
    { constructor; eauto. }
    iSpecialize ("Hwp" $! _ _ _ H with "H£").
    iMod "Hwp". iModIntro. iNext.
    do 2 iMod "Hwp".
    iMod (@fupd_mask_subseteq _ _ _ ∅) as "Hmod";
    [ set_solver | iModIntro ]. iMod "Hmod". iModIntro.
    iDestruct "Hwp" as "[$ [$ _]]".
  Qed.

  Lemma wp_covariant {A X} s E (m : micro A X) φ φ' :
    WP m @ s; E {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    WP m @ s; E {{ φ' }}.
  Proof.
    iIntros "Hwp Himpl";
      iApply (wp_strong_mono with "Hwp [Himpl]"); try done.
    iIntros (?) "Hφ"; iModIntro; iApply ("Himpl" with "Hφ").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Inversion Laws *)
  Lemma invert_wp_ret {R E} φ r :
    ∀ σ, store_interp σ -∗
        WP (Ret r : micro R E) {{ φ }} -∗
        |={⊤}=> store_interp σ ∗ φ (Res r).
  Proof.
    iIntros (?) "Hsi Hwp"; wp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_throw {R E} φ exn:
    ∀ σ, store_interp σ -∗
        WP (throw exn : micro R E) {{ φ }} -∗
        |={⊤}=> store_interp σ ∗ φ (Exn exn).
  Proof.
    iIntros (?) "Hsi Hwp"; wp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_crash {R E} φ:
    ∀ σ, store_interp σ -∗
        WP (crash : micro R E) {{ φ }} -∗
        |={⊤}=> False.
  Proof.
    iIntros (?) "Hsi Hwp".
    wp_unfold_all. spec_state.

    inversion Hred.
    destruct H as (?&?&?&?); inversion H.
    subst. inversion H0.
  Qed.

  Local Ltac strip_modalities Hmod :=
    iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as Hmod;
    [ set_solver | iModIntro ]; iNext; iModIntro;
    iMod Hmod; iModIntro; wp_frame.

  (* Invert cases where there are premises of the form [WP crash _] or [WP (throw _) _]*)
  Local Ltac wp_invert :=
    match goal with
    | |- context [environments.Esnoc _ ?SI (store_interp _)] =>
        match goal with
        (* WP crash Ψ is an absurd goal; can conclude immediately *)
        | |- context [environments.Esnoc _ ?Hwp (wp _ _ crash _)] =>
            iPoseProof (invert_wp_crash with SI) as "Hinv";
              by iMod ("Hinv" with "[$]") as "%"
        (* WP throw Ψ *)
        | |- context [environments.Esnoc _ ?Hwp (wp _ _ (throw _) _)] =>
            iPoseProof (invert_wp_throw with SI) as "Hinv";
            iMod ("Hinv" with "[$]") as "[$ Hinv]"; strip_modalities "Hmod"
        end
    end.

  (* ------------------------------------------------------------------------ *)
  (** *Hoare-style reasoning rules for primitive [micro] and monadic combinators *)

  (* Pure outcomes *)
  Definition wp_ret {R E} s a e φ:
    ipure φ a ⊢ WP (Ret a : micro R E) @ s; e {{ φ }}.
  Proof.
    iIntros "Hφ"; rewrite wp_unfold; by cbn.
  Qed.
  Definition wp_ret' {R E} s a e φ:
    φ a ⊢ WP (Ret a : micro R E) @ s; e {{ RET v, φ v }}.
  Proof.
    iIntros "Hφ"; rewrite wp_unfold; by cbn.
  Qed.

  (* Cut rule *)
  Lemma wp_bind {A1 A2 X} (m1 : micro A1 X) (m2 : A1 -> micro A2 X) ψ:
    WP m1 {{ lift_ipure (fun (v : _) => WP (m2 v) {{ ψ }}) }} ⊢
    WP (bind m1 m2) {{ ψ }}.
  Proof.
    iLöb as "IH" forall (m1 m2 ψ); iIntros "Hwp".

    wp_case_is_ret m1.
    (* Case: [m1] is [ret _]. *)
    { repeat wp_unfold_all; destruct (to_outcome (m2 a));
      by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { wp_unfold m1.
      (* Case analysis on [bind] :
            If [m1] is not [ret _]; [bind m1 m2] is not [ret _] *)
      wp_case_is_ret (bind m1 m2); subst.

      wp_case_is_throw m1.
      (* Case : [m1] is [throw _]; trivial *)
      { cbn; by try_iMod "Hwp". }

      (* Case : [m1] is not [throw _] *)
      wp_unfold (bind m1 m2); rewrite Houtcome.
      (* Since [m1] is not an outcome, [bind m1 m2] is not an outcome, either. *)
      not_outcome: bind m1 m2.

      intro_state; spec_state; iModIntro.

      construct_wp_nonret.

      step_bind Hstep; spec_step.

      iModIntro; wp_frame.

      by iApply ("IH" with "Hwp"). }
  Qed. (* LATER: See if we can clean up this proof using [wp_try] Proof. *)

  (* A binary version of the previous lemma. *)

  (* This version must be preferred when the proof of [m1] requires a case
    analysis. The scope of the case analysis is then limited to the first
    premise, so the proof of [m2] is not duplicated. *)

  Lemma wp_bind_binary {A1 A2 X} (m1: micro A1 X) (m2: A1 → micro A2 X) φ ψ :
    WP m1 {{ φ }} ⊢
    (∀ v, φ v -∗ ((fun v0 => WP m2 v0 {{ v, ψ v }}) ↑) v) -∗
    WP (bind m1 m2) {{ ψ }}.
  Proof.
    iIntros "Hm1 Hm2".
    iApply wp_bind.
    iApply (wp_strong_mono with "Hm1"); try set_solver.
    iIntros (?) "Hφ"; iSpecialize ("Hm2" with "Hφ"); by iModIntro.
  Qed.

  (* Try-catch *)
  Lemma wp_try {A B E E'} (m : micro A E')
    (f : A -> micro B E) (h : E' -> micro B E) φ :
    WP m {{ | RET x => WP (f x) {{ φ }} ;
            | EXN y => WP (h y) {{ φ }} }} -∗
    WP (try m f h) {{ φ }}.
  Proof.
    iLöb as "IH" forall (m f h φ).
    iIntros "Hwp".
    wp_case_is_ret m.
    (* Case: [m1] is [ret _]. *)
    (* The result is immediate. *)
    { repeat wp_unfold_all;
        destruct (to_outcome (f a)); by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { wp_unfold m.

      (* Case analysis on [try] :
            If [m1] is not [ret _]; [try m1 _ _] is not [ret _] *)
      wp_case_is_ret (try m f h) Hret'; subst.
      { rewrite /= Hk_ret /=.
        wp_unfold_all; by iMod "Hwp". }

      wp_case_is_throw m Hthrow; cbn.
      (* Case : [m1] is [throw _]. *)
      { wp_unfold_all.
        destruct (to_outcome (h e)); [ by iMod "Hwp" |].
        intro_state; iMod "Hwp";
          spec_state; by iFrame. }

      (* Case : [m1] is not [throw _]. *)
      rewrite Houtcome.

      eapply (to_outcome_None_try m f h) in Houtcome.
      wp_unfold (try m f h); rewrite Houtcome.

      intro_state; spec_state; iModIntro.

      construct_wp_nonret.

      step_try Hstep; spec_step.

      iModIntro; wp_frame.

      by iApply ("IH" with "Hwp"). }
  Qed.

  (* A binary version of the previous lemma. *)

  (* This version must be preferred when the proof of [m1] requires a case
    analysis. The scope of the case analysis is then limited to the first
    premise, so the proof of [m2] is not duplicated. *)

  Lemma wp_try_binary {A1 A2 X' X} (m1: micro A1 X') (m2: A1 → micro A2 X)
    (h : X' -> micro A2 X) (φ ψ : outcome -> _) :
    WP m1 {{ φ }} ⊢
    (∀ v, φ v -∗
          (| RET x => WP m2 x {{ v, ψ v }};
           | EXN y => WP h y {{ v, ψ v }}) v) -∗
    WP (try m1 m2 h) {{ ψ }}.
  Proof.
    iIntros "Hm1 Hm2".
    iApply wp_try.
    iApply (wp_strong_mono with "Hm1"); try set_solver.
    iIntros (?) "Hφ"; iSpecialize ("Hm2" with "Hφ"); by iModIntro.
  Qed.

  (* Par combinator *)
  Lemma wp_par {A E A1 A2 E'} (m1 : micro A1 E') (m2 : micro A2 E')
    {k: A1 * A2 → micro A E} {z : E' → micro A E} {φ} φ1 φ2:
    WP m1 {{ φ1 }} ⊢
    WP m2 {{ φ2 }} -∗
    (∀ e, φ1 (Exn e) -∗ WP (z e) {{ φ }}) -∗
    (∀ e, φ2 (Exn e) -∗ WP (z e) {{ φ }}) -∗
    (∀ a1 a2,
        φ1 (Res a1) -∗ φ2 (Res a2) -∗
        WP (k (a1, a2)) {{ φ }}) -∗
      WP (Par m1 m2 k z) {{ φ }}.
  Proof.
    (* We proceed by Löb-Induction after generalizing [m1] and [m2]. *)
    iLöb as "IH" forall (m1 m2); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

    (* As for the other rules, proof starts by stepping in the WP:
      (1) unfold the wp, (2) introduce a outcomeid state, (3) introduce the head
      modality and (4) enter in the second branch of the WP. *)
    wp_unfold_head; intro_state.

    wp_intro_mask "Hmod".

    (* Make a case study over the possible step. In each case, use FupTrans to
      add the modality [ |={E,∅}=> ] in front of the goal. *)
    { iMod "Hmod" as "_".

      (* We now examine each of the ways in which [Par m1 m2 k z] can step. *)
      destruct_step.

    { (* Case: [StepParRetRet].
        Both [m1] and [m2] represent outcomes [v1] and [v2]. One can consume [H1]
        and [H2] to learn that the outcomes respect their postconditions.
        The inversion does not consume the state-interpretation, which can be
        framed behind the modalities. *)
      iMod (invert_wp_ret with "[$][$]") as "[Hsi H2]".
      iMod (invert_wp_ret with "[$][$]") as "[$ H1]".

      (* Introduce the modality [ |={E,∅}=> ]. *)
      iMod (@fupd_mask_subseteq _ _ ⊤ ∅) as "Hmod";
        [ set_solver | iModIntro ].
      (* The later is not exposed in this rule. Hence, it can simply be
        introduced together with the remaining modalities. *)
      iNext; iModIntro; iMod "Hmod"; iModIntro.

      repeat red in Hstep.
      (* Finally, use the hypothesis on [k] to finish the proof. *)
      iSpecialize ("Hjoin" with "H1 H2"); by iFrame. }

    (* In the four following cases, one of the branches of the [Par] is either a
      [crash] or [throw _]. Hence, one can consume the corresponding [WP]
      hypothesis to get [ |={E}=> False ]. As the goal is of the form
      [ |={E,∅}=> G ], by FupTrans, it suffices to show [|={E}=> |={E,∅}=> G].
      Then, by monotony of [ |={E}=> ], one can eliminate [False] and finish
      the proof. *)

    (* Invert cases where there are premises of the form [WP crash _] or [WP (throw _) _]*)
    1-4: wp_invert;
      try iApply ("Hexn1" with "[$]");
      try iApply ("Hexn2" with "[$]").

    { (* Case: [StepParLeft] *)
      (* [m1] steps to [m'1]. Steps preserve the conjunction of the [WP] and the
        state interpretation. Some modalities need to be stripped from the
        result. *)
      iPoseProof (wp_step Hstep with "Hsi H£ H1") as ">H1".
      iMod "H1"; iModIntro. (* After stripping modalities, one can
                                        frame the state interpretation. *)
      iNext. iModIntro; do 2 iMod "H1". iModIntro.
      iDestruct "H1" as "[$ H1]"; cbn; iFrame; iSplitR ""; last done.

      (* The induction hypothesis ends the proof. *)
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* Case: [StepParRight]
        This case is similar to the previous one. *)
      iMod (wp_step Hstep with "Hsi H£ H2") as ">H2".
      iModIntro. iNext.
      iMod "H2"; iModIntro. (* After stripping modalities, one can
                                        frame the state interpretation. *)
      iMod "H2".
      iDestruct "H2" as "[$ H2]"; cbn; iFrame; iSplitR ""; last done.
      iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). } }
  Qed.


  (* The following lemmas offer reasoning rules for each of the system calls,
    that is, for computations of the form [Stop c x y]. They are simple
    consequences of the operational behavior of these system calls. *)

  (* [CEval]. *)

  Lemma wp_eval {A X} η e (k : val → micro A X) z φ :
    ▷ WP (eval η e) {{ | RET v => WP (k v) {{ φ }} ;
                       | EXN v => WP (z v) {{ φ }} }} ⊢
    WP (Stop CEval (η, e) k z) {{ φ }}.
  Proof.
    iIntros "Hwp".
    wp_unfold_head.
    intro_state.
    wp_step.

    by iApply wp_try.
  Qed.

  Lemma wp_eval_ret {X} η (e : expr)
    {z : void → micro val X} (φ : _ -> iPropI Σ):
    ▷ WP eval η e
        {{ v, ( | RET v => WP ret v {{ v, φ v }};
                | EXN v => WP z v {{ v, φ v }}) v }} ⊢
    WP (Stop CEval (η, e) (ret : val -> micro val X) z) {{ φ }}.
  Proof.
    iIntros "Hwp".
    iApply wp_eval.
    iNext.
    iApply wp_mono; done.
  Qed.

  (* A reasoning rule for [choose]. *)

  (* A non-separating conjunction is used to express the idea that
    either [m1] or [m2] is executed, but not both. Thus, there is
    no need to split the current resource. It suffices to prove
    that both [m1] and [m2] are safe under the current resource. *)

  Lemma wp_choose {res exn} (m1 m2 : micro res exn) ψ :
    ▷ (WP m1 {{ ψ }} ∧ WP m2 {{ ψ }}) ⊢
    WP (choose m1 m2) {{ ψ }}.
  Proof.
    iIntros "H".
    wp_unfold_head.
    intro_state. wp_step.

    { iDestruct "H" as "[H _]".
      by rewrite try_ret_right. }

    { iDestruct "H" as "[_ H]".
      by rewrite try_ret_right. }
  Qed.

  (* This is a special case of the previous rule, where the left-hand side if
    [ok]. The rule reads as follows: if [φ] holds now, and if the right-hand
    side [m] preserves [φ], then after executing [choose ok m] the assertion
    [φ] still holds. *)

  Lemma wp_choose_ok {E} (m : micro val E) (φ : iProp Σ) :
    φ -∗
    ▷ (φ -∗ WP m {{ λ _, φ }}) -∗
    WP (choose ok m) {{ λ _, φ }}.
  Proof.
    iIntros "Hφ Hm".
    iApply wp_choose. iModIntro. iSplit.
    { iClear "Hm". iApply wp_ret. iAssumption. }
    { by iApply "Hm". }
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [CAlloc]. *)

  (* The standard memory allocation rule of Separation Logic. *)

  Lemma wp_alloc {A X} s E v (k : loc → micro A X) z φ :
    ▷ (
        ∀ l,
          mapsto l (DfracOwn 1) v ∗ meta_token l ⊤ -∗
          WP (k l) @ s; E {{ φ }}
      ) ⊢
    WP (Stop CAlloc v k z) @ s; E {{ φ }}.
  Proof.
    iIntros "H".
    wp_unfold_head.
    intro_state.

    wp_intro_mask "Hmod".

    destruct_step.

    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi HH]"; first done.

    wp_resolve_mask "Hmod".

    by iApply "H".
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma wp_store {A X} s E l v v' (k : unit → micro A X) z φ :
    mapsto l (DfracOwn 1) v ⊢
    ▷ (
        mapsto l (DfracOwn 1) v' -∗
        WP (k tt) @ s; E {{ φ }}
      ) -∗
    WP (Stop CStore (l, v') k z) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    wp_unfold_head.
    intro_state.
    wp_intro_mask "Hmod".

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    wp_resolve_mask "Hmod".

    iApply ("Hwp" with "Hl").
  Qed.

  (* The standard memory load rule of Separation Logic. *)

  Lemma wp_load {A X} s E l v dq (k: val → micro A X) z φ :
    mapsto l dq v ⊢
    ▷ (
        mapsto l dq v -∗
        WP (k v) @ s; E {{ φ }}
      ) -∗
    WP (Stop CLoad l k z) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    wp_unfold_head.
    intro_state.
    wp_intro_mask "Hmod".

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.

    wp_resolve_mask "Hmod".
    iApply ("Hwp" with "Hl").
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [CLoop] *)

  (* The following lemmas help reason on loops. *)

  (* The following lemma is inspired by the corresponding CFML rule. *)
  Lemma wp_loop {A X}
        (η : env) (x : var) (i1 i2 : int) (e : expr)
        (k : val → micro A X) (z : void → micro A X) (φ : outcome → iProp Σ) :
    (* If *)
    (▷ (* Either: *)
      if int.lt i2 i1
      then
        (* - i2 < i1,
             and the rest of the program satisfies the postcondition. *)
        wp NotStuck ⊤ (k #()) φ
      else
        (* - i1 <= i2,
               and the evaluation of the body succeeds and the remaining
               iterations satisfy the postcondition. *)
        wp NotStuck ⊤ (eval ((x, (VInt i1)) :: η) e)
          (| RET _ => WP stop CLoop (η, x, add i1 int.one, i2, e)
                            {{ v, ( | RET x1 => WP k x1 {{ v, φ v }};
                                    | EXN y => WP z y {{ v, φ v }}) v }};
           | EXN y => WP throw y {{ v, ( | RET x0 => WP k x0 {{ v, φ v }};
                                        | EXN y0 => WP z y0 {{ v, φ v }}) v }})) ⊢
    (* Then the loop (with the rest of the program as continuation) satisfies
      the postcondition. *)
    wp NotStuck ⊤ (Stop CLoop (η, x, i1, i2, e) k z) φ.
  Proof.
    iIntros "H".

    (* We proceed by case analysis on the comparison of [i1] and [i2]. *)
    destruct (int.lt i2 i1) eqn:Hlt; (* In each case: *)
      (* we enter into the WP of the goal, eliminate modalities, use the fact
        that the [Stop CLoop _ _ _] can step (in a unique way) and frame the
        state interp. *)
      wp_unfold (Stop CLoop (η, x, i1, i2, e) k z);
      intro_state; wp_step.

    { (* Finally, expand the definition of the helper function [loop]. *)
      rewrite/loop Hlt; by iFrame. }

    { (* In the base case, the loop is over. One can use the hypothesis to end
          the proof. *)
      iApply wp_try.

      rewrite/loop Hlt; iFrame.
      rewrite bind_as_try.
      by iApply wp_try. }
  Qed.

  Local Lemma wp_loop_inv_pos_aux {A X}
        (η : env) (x : var) (n i1 i2 : nat) (e : expr)
        (k : val → micro A X) (z : void → micro A X) (φ : outcome → iProp Σ)
        (Hinv : nat → iProp Σ) :
    representable i1 →
    representable (S i2) →
    le i1 i2 →
    n = S (i2 - i1)%nat →
    (Hinv i1) ⊢
    (□ ∀ (i: nat), ⌜le i1 i⌝ →
                  ⌜le i i2⌝ →
                  Hinv i -∗ wp NotStuck ⊤
                                (eval ((x, (VInt $ repr i)) :: η) e)
                                (λ _, Hinv (S i))) -∗
    (Hinv (S i2) -∗ wp NotStuck ⊤ (k #()) φ) -∗
    wp NotStuck ⊤ (Stop CLoop (η, x, repr i1, repr i2, e) k z) φ.
  Proof.
    generalize dependent i1 ; generalize dependent i2.
    induction n;
      iIntros(i2 i1 Hrepr1 Hrepr2 Hle Hn) "Hinit #Hpreservation Hccl";

      (* Three cases: either the loop is over, or the loop is entered one last
        time, or it is entered. *)
      last (destruct (decide (i1 = i2)) as [ -> | Hneq ]; last first);

      (* First, we take a step in the WP and frame the state interp. *)
      wp_unfold_head; intro_state; wp_step.

    { (* The loop is over. *)
      assert (i1 = S i2) as -> by lia.
      iApply wp_try.
      rewrite/loop lt_repr_repr; try representable.
      replace (i2 <? S i2)%Z with true by lia.
      iApply wp_ret.
      iApply ("Hccl" with "Hinit"). }

    { (* The body of the loop will be executed (not for the last time). *)
      assert (Hlt: int.lt (repr i2) (repr i1) = false).
      { rewrite lt_repr_repr; try assumption.
        - lia.
        - unfold representable in *; lia. }

      (* The loop is really a try... *)
      rewrite/loop Hlt.
      rewrite try_bind.

      (* ...which leads to a bind.
        The first element of the bind is the evaluation of the body of the
        loop. The assumption ["Hpreservation"] prove that this evaluation
        preserves the loop invariant predicate. It takes the invariant at i1
        and gives back the invariant at [S i1]. *)
      iApply (wp_try_binary with "[Hinit Hpreservation]");
        first iApply ("Hpreservation" $! i1 with "[//][//]Hinit").
      iIntros(v)"Hinit".

      (* The goal is the proof of a WP for [for x = S i1 to i2 do e done]. The
        induction hypothesis can take care of it.
        Note: it is to use ["Hpreservation"] a second time that it needs to be
              persistent.  *)
      iPoseProof (IHn i2 (S i1)) as "IH"; unfold representable in *; try lia.

      iSpecialize ("IH" with "Hinit[]Hccl").
      { iIntros "!>" (i Hi Hi').
        iApply ("Hpreservation"); iPureIntro; lia. }
        destruct v; cycle 1.
        (* Why doesn't this get automatically discharged with [contradiction]? *)
        { exfalso. exact (elim_void e0). }
        cbn.

        replace (add (repr i1) int.one) with (repr (S i1)); last first.
        { rewrite add_repr_repr. f_equal. lia. }
        done. }

    { (* Last run of the loop. *)
      iApply wp_try.
      rewrite/loop lt_repr_repr; try assumption.
      rewrite Z.ltb_irrefl.
      iApply (wp_bind_binary with "[Hinit Hpreservation]");
        first iApply ("Hpreservation" with "[//][//]Hinit").
      iIntros(v)"Hinit".
      destruct v; cycle 1.
      (* Why doesn't this get automatically discharged with [contradiction]? *)
      { exfalso. exact (elim_void e0). }
      cbn.
      iSpecialize ("Hccl" with "Hinit").

      assert (Hlt: int.lt (repr i2) (add (repr i2) int.one) = true).
      { rewrite add_repr_repr lt_repr_repr; unfold representable in *; lia. }

      wp_unfold (Stop CLoop (η, x, add (repr i2) int.one, repr i2, e) ret throw).
      intro_state. iClear "Hmod".

      iRename "H£" into "H£'".
      wp_step.
      iApply wp_try.
      rewrite/loop Hlt.
      do 2 iApply wp_ret.
      iExact "Hccl". }
  Qed.

  Definition wp_loop_inv_pos {A X}
        (η : env) (x : var) (i1 i2 : nat) (e : expr)
        (k : val → micro A X) (z : void → micro A X) (φ : outcome → iProp Σ)
        (Hinv : nat → iProp Σ) :
    representable i1 →
    representable (S i2) →
    le i1 i2 →
    (Hinv i1) ⊢
    (□ ∀ (i: nat), ⌜le i1 i⌝ →
                ⌜le i i2⌝ →
                Hinv i -∗ wp NotStuck ⊤
                              (eval ((x, (VInt $ repr i)) :: η) e)
                              (λ _, Hinv (S i))) -∗
    (Hinv (S i2) -∗ wp NotStuck ⊤ (k #()) φ) -∗
    wp NotStuck ⊤ (Stop CLoop (η, x, repr i1, repr i2, e) k z) φ :=
    let n := S (i2 - i1)%nat in
    fun repr1 repr2 Hle =>
      wp_loop_inv_pos_aux η x n i1 i2 e k z φ Hinv
                          repr1 repr2 Hle eq_refl.

  (* ------------------------------------------------------------------------ *)

  (* Simplification is sound. *)

  (* That is, as announced in semantics/simplification.v, if [simplify n m ms]
    holds then the safety of the simplified program [ms] implies the safety
    of the more complex original program [ms]. *)

  Local Lemma wp_simp_prelim {R E} (m ms : micro R E) φ :
    WP ms {{ φ }} -∗
    ⌜ simp m ms ⌝ -∗
    WP m  {{ φ }}.
  Proof.
    (* Proceed by Löb induction. *)
    iLöb as "IH" forall (m ms).
    (* Introduce the hypotheses. *)
    iIntros "Hwp" (Hsimp).

    (* Examine [m]. *)
    wp_case_is_ret m Hretm.
    (* If [m] is [ret a], then [ms] is also [ret a], so we are done. *)
    { clarify_simp. iAssumption. }

    (* Thus, in the following, we assume [m] is not [ret _]. *)
    (* Examine [m] again, on whether it is a [throw]. *)
    wp_case_is_throw m Hthrow.
    { (* If [m] is [throw e], then [ms] is also [throw e], so we are done. *)
      clarify_simp. iAssumption. }

    (* Begin unfolding the definition of [WP m ...]. *)
    wp_unfold m.

    (* Simplify match on [m]. *)
    pose proof (is_not_ret_or_throw_to_outcome _ Hretm Hthrow) as ->.
    intro_state.

    (* Examine [ms] on whether it is a [ret]. *)
    wp_case_is_ret ms Hretms.
    (* TODO the cases [ms = ret _] and [ms = throw _] can probably
            be merged. In both cases, [ms] is final. *)

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is able to step. *)
      iApply fupd_frame_l; iSplit.
      { pose proof (invert_simp_final σ Hsimp) as [|];
          [ prove_final | subst; simpl in Hretm; congruence |].
        iPureIntro. by apply can_step_reducible. }

      wp_intro_mask "Hmod".
      intro_step.

      (* Examine one step of [m] to [m']. The simulation diagram in this case
      tells us that this reduction step takes us closer to [ret a].
      That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
      simp_final_step_diagram.
      wp_resolve_mask "Hmod".

      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "Hwp [//]"). }

    (* Examine [ms] on whether it is a [throw]. *)
    wp_case_is_throw ms Hthrow_ms.
    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is able to step. *)
      iApply fupd_frame_l; iSplit.
      { pose proof (invert_simp_final σ Hsimp) as [|];
          [ prove_final | subst; simpl in Hthrow; congruence |].
        iPureIntro. by apply can_step_reducible. }

      wp_intro_mask "Hmod".
      intro_step.

      (* Examine one step of [m] to [m']. The simulation diagram in this case
      tells us that this reduction step takes us closer to [ret a].
      That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
      simp_final_step_diagram.
      wp_resolve_mask "Hmod".

      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "Hwp [//]"). }

    (* [ms] is neither a [ret _] or [throw _]. *)

    (* Then, [WP ms ...] implies than [ms] can step.
    This implies that [m], too, can step. *)

    iAssert (|={⊤}=> ⌜ can_step (σ, m) ⌝
                    ∗ wp NotStuck ⊤ ms φ
                    ∗ store_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".
    { iApply ((fupd_plain_keep_l ⊤ ⌜can_step (σ, m)⌝
                                (wp NotStuck ⊤ ms φ ∗ store_interp σ))%I
              with "[$Hwp $Hsi]").
      iIntros "[??]";
        iMod (wp_can_step' with "[$][$]") as "%Hdisj".
      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simp_can_step. }
      destruct H; exfalso; eauto. }

    wp_intro_mask "Hmod".

    (* We now examine an arbitrary step of [m] to [m']. *)
    (* Exploit the main simulation diagram. *)
    simp_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { wp_resolve_mask "Hmod".
      iApply ("IH" with "Hwp [//]"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    wp_unfold ms.

    pose proof (is_not_ret_or_throw_to_outcome _ Hretms Hthrow_ms) as ->.
    iMod "Hmod" as "_"; spec_state.

    assert (prim_step ms σ nil _ _ nil) by (by constructor).
    iSpecialize ("Hwp" $! _ _ nil H0 with "H£").

    (* TODO: messy modality handling.. *)
    iMod "Hwp"; iModIntro; iNext; iMod "Hwp"; iModIntro; iMod "Hwp"; iModIntro.

    iDestruct "Hwp" as "(SI & Hwp & _)"; wp_frame.
    iApply ("IH" with "Hwp [//]").
  Qed.

  (* A corollary, for public use: [simp] is sound. *)

  Lemma wp_simp {R E} (m m' : micro R E) φ :
    simp m m' →
    WP m' {{ φ }} ⊢
    WP m  {{ φ }}.
  Proof.
    iIntros (Hsimp) "Hwp".
    iApply (wp_simp_prelim with "Hwp [//]").
  Qed.

End wp_rules.
