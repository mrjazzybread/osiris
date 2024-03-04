Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.semantics Require Import step code.

(** *Reasoning principles of [Osiris] wp-based Hoare triples *)

(* Properties about [outcome2] *)
Lemma is_outcome2_is_Some {A E} (m : micro A E) v:
  is_outcome2 m = Some v ->
  (∃ v', v = O2Throw v' /\ m = Throw v') \/
    (∃ v', v = O2Ret v' /\ m = Ret v').
Proof.
  intros; destruct m; inversion H; subst; eauto.
Qed.

Lemma is_not_ret_or_throw_to_outcome2 {A E} m :
  is_not_ret m ->
  is_not_throw m ->
  @is_outcome2 A E m = None.
Proof.
  intros H; destruct m; inversion H; intros H'; inversion H'; eauto.
Qed.

Lemma is_outcome2_None_bind {A B E} (m1 : micro A E) (m2 : A -> micro B E):
  is_outcome2 m1 = None ->
  is_outcome2 (bind m1 m2) = None.
Proof.
  intros; destruct m1; eauto; inversion H.
Qed.

Lemma is_outcome2_None_try {A B E' E}
  (m : micro A E') (f : A -> micro B E) (h : E' -> micro B E) :
  is_outcome2 m = None ->
  is_outcome2 (try m f h) = None.
Proof.
  intros; destruct m; eauto; inversion H.
Qed.

(* ------------------------------------------------------------------------ *)
(** *EWP tactics *)

(* TODO: Move to a different file *)

Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

(* This tactic unfolds [ewp] applied to the computation [m]. *)
Ltac ewp_unfold m :=
  setoid_rewrite (ewp_unfold m); rewrite /ewp_pre /=.

(* This tactic unfolds one occurrence of [ewp] at the head of the goal. *)

Ltac ewp_unfold_head :=
  iApply ewp_unfold; rewrite /ewp_pre /=.

(* Reason about case analysis on [is_ret]*)
Ltac destruct_is_ret :=
  repeat match goal with
    (* Inversion for if a computation is a ret *)
    | [H : is_ret ?x = Some _ |- _] =>
        apply invert_is_ret_Some in H;
        try subst x
    (* Inversion if some bind is equivalent to a return *)
    | [H : bind _ _ = ret _ |- _] =>
        let Hm := fresh "Hm_ret" in
        let Hk := fresh "Hk_ret" in
        let a := fresh "a" in
        apply invert_bind_eq_ret in H;
        destruct H as (a & Hm & Hk);
        subst
    (* Inversion if some try is equivalent to a return *)
    | [H : try _ _ _ = ret _ |- _] =>
        let Hm := fresh "Hm_ret" in
        let Hk := fresh "Hk_ret" in
        let a := fresh "a" in
        apply invert_try_eq_ret_disj in H;
        destruct H as [(a & Hm & Hk) | (a & Hm & Hk)];
        subst
    (* Absurd goal *)
    | [H : is_not_ret (ret _) |- _] =>
        by inversion H
    end.

Ltac destruct_is_throw :=
  repeat match goal with
    (* Inversion for if a computation is a ret *)
    | [H : is_throw ?x = Some _ |- _] =>
        apply invert_is_throw_Some in H;
        try subst x
    end.

Ltac destruct_is_not_ret_or_throw :=
  match goal with
  (* Inversion for if a computation is not a [ret] or [throw] *)
  | [H : is_not_ret ?a, H' : is_not_throw ?a |- _] =>
      let Houtcome := fresh "Houtcome" in
      pose proof (is_not_ret_or_throw_to_outcome2 a H H') as Houtcome
  end.


(* -------------------------------------------------------------------------- *)

(* Assert that [bind m1 m2] is not an outcome, deduced by [m1] not being an
    outcome *)
Tactic Notation "not_outcome:" "bind" constr(m1) constr(m2) :=
  match goal with
  | [H: is_outcome2 m1 = None |- _ ] =>
      apply (is_outcome2_None_bind m1 m2) in H;
      try rewrite H
  end.

(* Assert that [try m _ _] is not an outcome, deduced by [m] not being an
    outcome *)
Tactic Notation "not_outcome:" "try" constr(m) constr(f) constr(h) :=
  match goal with
  | [H: is_outcome2 m = None |- _ ] =>
      apply (is_outcome2_None_try m f h) in H;
      try rewrite H
  end.

(* Discharge pure subgoal that follows immediately by [tac] *)
Tactic Notation "discharge_pure" tactic(tac) :=
  match goal with
  | |- environments.envs_entails _ (bi_sep (bi_pure _) _) =>
      iSplitL ""; [ iPureIntro; by tac | ]
  | |- environments.envs_entails _ (bi_sep  _ (bi_pure _)) =>
      iSplitL ""; [ | iPureIntro; by tac ]
  end.

(* Discharge emp subgoal *)
Ltac discharge_emp :=
  match goal with
  | |- environments.envs_entails _ (bi_sep emp _) =>
      iSplitL ""; [ done | ]
  | |- environments.envs_entails _ (bi_sep  _ emp) =>
      iSplitR ""; [ | done ]
  end.

(* -------------------------------------------------------------------------- *)

Ltac is_outcome2_is_Some Hm :=
  apply is_outcome2_is_Some in Hm;
  destruct Hm as [ (?&?&?) | (?&?&?) ]; subst.

(* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
   of the form [ret a], or it is not. In the second branch, the equality
   [is_ret m = None] appears under the name [Hret]. *)

Tactic Notation "wp_case_is_ret" constr(x) ident(Hret) :=
  case_eq (is_ret x);
  [ intros ? Hret;
    try destruct_is_ret |
    intros Hret;
    try destruct_is_not_ret_or_throw].

Tactic Notation "wp_case_is_ret" constr(x) :=
  let Hret := fresh "Hret" in
  wp_case_is_ret x Hret.

(* [wp_case_is_throw m Hthrow] performs a case analysis on [m]: either it is
   of the form [throw a], or it is not. In the second branch, the equality
   [is_throw m = None] appears under the name [Hthrow]. *)

Tactic Notation "wp_case_is_throw" constr(x) ident(Hthrow) :=
  case_eq (is_throw x);
  [ intros ? Hthrow;
    try destruct_is_throw |
    intros Hthrow;
    try destruct_is_not_ret_or_throw ].

Tactic Notation "wp_case_is_throw" constr(x) :=
  let Hthrow := fresh "Hthrow" in
  wp_case_is_throw x Hthrow.


(* Working with the state interpretation invariant. *)

(* [intro_state] introduces [σ] and [state_interp σ]. *)
(* [spec_state H] specializes the hypothesis H with [state_interp σ]. *)

Ltac intro_state := iIntros (σ) "Hsi".

Ltac spec_state :=
  lazymatch goal with
  | |- context [environments.Esnoc _ ?Hwp
      (bi_forall (fun σ1 : store => bi_wand (state_interp σ1) _))] =>
      match goal with
      | |- context [environments.Esnoc _ ?SI (state_interp ?σ)] =>
          let Hstep := fresh "Hstep" in
          iSpecialize (Hwp with SI);
          iMod Hwp;
          iDestruct Hwp as (Hred) Hwp
      end
  end.

(* -------------------------------------------------------------------------- *)
(* More [wp] tactics *)

Ltac wp_frame := iFrame; cbn.

(* [intro_step] introduces [prim_step] along with the new expression and state *)
Ltac intro_step :=
  let Hstep := fresh "Hstep" in
  let efs := fresh "efs" in
  iIntros (?? Hstep).

(* NEXT: EDIT *)
(* The following two tactics correspond to the branch [is_ret _ = None] in
  the definition of [wp]. This branch is a conjunction
    ⌜can_step (σ, m)⌝ ∗ ∀ σ' m', ...
  [construct_wp_nonret] is used when this form appears in the goal.
  [destruct_wp_nonret] is used when it appears in the hypothesis "Hwp". *)

Ltac construct_wp_nonret :=
  (* Prove [can_step]: *)
  (discharge_pure (eauto with step can_step || econstructor; constructor));
  (* Introduce a hypothetical step: *)
  intro_step.

(* -------------------------------------------------------------------------- *)

(* Some tactics relevant to [step] relation *)

(* Try to search the environment if there is something known about the head of
  the computation, i.e. [m] ; if so, try to extract as much information as
  possible *)
Tactic Notation "step_inv_aux" constr(m) constr(lem) tactic(tac) :=
  (* Generate some fresh names *)
  let Hred := fresh "Hred" in
  let m' := fresh "m'" in
  let Hstep' := fresh "Hstep'" in
  destruct lem as (m' & Hstep' & ->); [ done | ].

(* Invert hypotheses of the shape
    [step (σ, bind _ _) _] and [step (σ, try _ _ _) _] *)
Tactic Notation "step_inv" hyp(Hstep) :=
  match type of Hstep with
  | step.step (_, bind ?m _) _ =>
      (step_inv_aux m (invert_step_bind Hstep) idtac)
  | step.step (_, try ?m _ _) _ =>
      (step_inv_aux m (invert_step_try Hstep) idtac)
  end.

(* Change goals of form [step _ _] to [prim_step _ _ _ _ _ ] *)
Tactic Notation "to_prim_step" hyp(H) :=
  match type of H with
  | step (?σ, ?m) (?σ', ?m') =>
      let H' := fresh "H'" in
      rename H into H';
      assert (H: prim_step m σ [] m' σ' []) by (constructor; eauto);
      clear H'
  end.

(* -------------------------------------------------------------------------- *)

(* [tick_wp] is used when the goal is
    [|==> ▷ (state_interp σ' ∗ wp E m' φ)]. *)

Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro.

(* Specialize hypothesis that expects a [step] relation and extract out
information *)
Ltac spec_step :=
  match goal with
  | |- context[environments.Esnoc _ ?Hwp
                (bi_forall (fun _ : store =>
                              bi_forall (fun _ : micro _ _ =>
                                            bi_wand (bi_pure (step.step (?σ, ?m) _)) _)))] =>
      match goal with
      | [Hstep : step.step (σ, m) _ |- _] =>
          (* Specialize step relation *)
          iSpecialize (Hwp $! _ _ Hstep);
          (* Destruct the hypothesis *)
          iMod Hwp;
          tick_wp
      end
  end.

(* ------------------------------------------------------------------------ *)

Section wp_rules.

  Context `{!osirisGS Σ} `{protocol Σ}.

  (* ------------------------------------------------------------------------ *)
  (** *Some properties about [step] *)

  Lemma step_not_outcome2 {A E} {σ σ'} {m m' : micro A E} :
    step.step (σ, m) (σ', m') ->
    is_outcome2 m = None.
  Proof.
    destruct m; inversion 1; try dependent destruction H8; eauto.
  Qed.

  Lemma fupd_wp {A X} s E (e : micro A X) Φ :
    (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    rewrite ewp_unfold /ewp_pre. iIntros "H".
    destruct (is_outcome2 e) as [v|] eqn:?.
    { by iMod "H". }
    iIntros (σ) "Hσ1". iMod "H". by iApply "H".
  Qed.

  (* Local Instance for eliminating fancy updates *)
  (* For some reason this has to be shown explicitly (perhaps the quantification
    over return and exception types for the language make the tc resolution
    finnicky) *)
  Global Instance elim_modal_fupd_wp {A X} p s E (e : micro A X) P Φ :
    classes.ElimModal True p false (fupd E E P) P (WP e @ s; E {{ Φ }})
      (WP e @ s; E {{ Φ }}).
  Proof.
    rewrite /classes.ElimModal bi.intuitionistically_if_elim.
    rewrite fupd_frame_r. rewrite bi.wand_elim_r. intro.
    by pose proof (fupd_wp s E e Φ).
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *General properties about [WP] and [step] *)

  Lemma wp_can_step {R E} {σ} φ (m : micro R E) {M}:
    state_interp σ -∗
    wp NotStuck M m φ ={M, ∅}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros "SI Hwp".
    ewp_unfold_all.
    destruct (is_outcome2 m) eqn: Hm.
    { iMod "Hwp". iApply fupd_mask_intro; first set_solver.
      iIntros "_".
      is_outcome2_is_Some Hm; [ iRight; iRight | iRight; iLeft ];
      iPureIntro; eauto. }
    { spec_state; iPureIntro; by left. }
  Qed.

  Lemma wp_can_step' {R E} {σ φ} (m : micro R E) {M}:
    state_interp σ -∗
    wp NotStuck M m φ ={M}=∗
    ⌜can_step (σ, m) ∨ is_ret m <> None \/ is_throw m <> None⌝.
  Proof.
    iIntros.
    iPoseProof (wp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

  Lemma wp_step_not_eff {R E} {σ σ'} {m n : micro R E} {φ}:
    is_eff m = None ->
    step.step (σ, m) (σ', n) →
    state_interp σ -∗
    WP m {{ φ }} ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    (state_interp σ' ∗ WP n {{ φ }}).
  Proof.
    intros Heff Hstep.
    iIntros "Hsi Hwp".

    ewp_unfold m.
    pose proof (step_not_outcome2 Hstep) as ->.
    spec_state. iModIntro.
    iSpecialize ("Hwp" $! _ _ Hstep).
    iMod "Hwp". iModIntro. iNext.
    iMod "Hwp".
    iMod (@fupd_mask_subseteq _ _ _ ∅) as "Hmod";
      [ set_solver | iModIntro ]. iMod "Hmod". iModIntro.
    rewrite Heff.
    iDestruct "Hwp" as "[$ $]".
  Qed.

  Lemma wp_covariant {A X} s E (m : micro A X) φ φ' :
    WP m @ s; E {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    WP m @ s; E {{ φ' }}.
  Proof.
    iIntros "Hwp Himpl";
      iApply (ewp_strong_mono with "Hwp [Himpl]"); try done.
    iIntros (?) "Hφ"; iModIntro; iApply ("Himpl" with "Hφ").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Inversion Laws *)
  Lemma invert_wp_ret {R E} φ r :
    ∀ σ, state_interp σ -∗
        WP (Ret r : micro R E) {{ φ }} -∗
        |={⊤}=> state_interp σ ∗ φ (O2Ret r).
  Proof.
    iIntros (?) "Hsi Hwp"; ewp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_throw {R E} φ exn:
    ∀ σ, state_interp σ -∗
        WP (throw exn : micro R E) {{ φ }} -∗
        |={⊤}=> state_interp σ ∗ φ (O2Throw exn).
  Proof.
    iIntros (?) "Hsi Hwp"; ewp_unfold_all; by iFrame.
  Qed.

  Lemma invert_wp_crash {R E} φ:
    ∀ σ, state_interp σ -∗
        WP (crash : micro R E) {{ φ }} -∗
        |={⊤}=> False.
  Proof.
    iIntros (?) "Hsi Hwp".
    ewp_unfold_all. spec_state.

    inversion Hred; destruct x.
    inversion H0.
  Qed.

  (* NEXT: Move *)
  Lemma is_eff_bind {A1 A2 X} (m1 : micro A1 X) (m2 : A1 -> micro A2 X) v k:
    is_eff m1 = Some (v, k)->
    is_eff (bind m1 m2) = Some (v, fun v => bind (k v) m2).
  Proof.
    intros Hm1.
    destruct m1; inversion Hm1.
    destruct c; inversion H1; subst; by cbn.
  Qed.

  Lemma is_eff_try {A B E' E}
    (m : micro A E') (f : A -> micro B E) (h : E' -> micro B E) v k:
    is_eff m = Some (v, k)->
    is_eff (try m f h) = Some (v, fun v => try (k v) f h).
  Proof.
    intros Hm.
    destruct m; inversion Hm.
    destruct c; inversion H1; subst; by cbn.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Hoare-style reasoning rules for primitive [micro] and monadic combinators *)

  (* Pure outcomes *)
  Definition wp_ret {R E} s a e φ:
    φ (O2Ret a) ⊢ WP (Ret a : micro R E) @ s; e {{ φ }}.
  Proof.
    iIntros "Hφ"; rewrite ewp_unfold; by cbn.
  Qed.
  Definition wp_ret' {R E} s a e φ:
    φ a ⊢ WP (Ret a : micro R E) @ s; e {{ RET v, φ v }}.
  Proof.
    iIntros "Hφ"; rewrite ewp_unfold; by cbn.
  Qed.

  (* Cut rule *)
  Lemma wp_bind {A1 A2 X} (m1 : micro A1 X) (m2 : A1 -> micro A2 X) ψ:
    WP m1 {{ RET v, WP (m2 v) {{ ψ }} }} ⊢
    WP (bind m1 m2) {{ ψ }}.
  Proof.
    iLöb as "IH" forall (m1 m2 ψ); iIntros "Hwp".

    wp_case_is_ret m1.
    (* Case: [m1] is [ret _]. *)
    { repeat ewp_unfold_all; destruct (is_outcome2 (m2 a));
      by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { ewp_unfold m1.
      (* Case analysis on [bind] :
            If [m1] is not [ret _]; [bind m1 m2] is not [ret _] *)
      wp_case_is_ret (bind m1 m2); subst.

      wp_case_is_throw m1.
      (* Case : [m1] is [throw _]; trivial *)
      { cbn. by iMod "Hwp". }

      (* Case : [m1] is not [throw _] *)
      ewp_unfold (bind m1 m2); rewrite Houtcome.
      (* Since [m1] is not an outcome, [bind m1 m2] is not an outcome, either. *)
      not_outcome: bind m1 m2.

      (* Process a step of computation. *)
      intro_state; spec_state; iModIntro.

      construct_wp_nonret.

      (* Get more information out of [e2] *)
      step_inv Hstep.

      (* Can use information from above to get [wp] about stepped computation *)
      spec_step.

      (* TODO: Clean up *)
      destruct (is_eff m1) eqn: Hm1.
      { destruct p; apply (is_eff_bind m1 m2) in Hm1; rewrite Hm1.
        iDestruct "Hwp" as "[Si [Heff Hwp]]"; iFrame.
        iIntros (??) "SI"; iSpecialize ("Hwp" with "SI").
        iMod "Hwp". iModIntro; iNext.
        by iApply ("IH" with "Hwp"). }

      destruct m1; inversion Hm1; cbn.
      all: try (iDestruct "Hwp" as "[SI Hwp]"; iFrame;
                  by iApply ("IH" with "Hwp")).

      2 : {
        destruct c; inversion H1;
        try (iDestruct "Hwp" as "[SI Hwp]"; iFrame;
        by iApply ("IH" with "Hwp")). }

      (* [m1] is [ret _] *)
      inversion Hstep'. }
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
    iApply (wp_covariant with "Hm1"); try set_solver.
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
    { repeat ewp_unfold_all; cbn;
        destruct (is_outcome2 (f a)); by iMod "Hwp". }

    (* Case: [m1] is not [ret _]. *)
    { ewp_unfold m.

      (* Case analysis on [try] :
            If [m1] is not [ret _]; [try m1 _ _] is not [ret _] *)
      wp_case_is_ret (try m f h) Hret'; subst.
      { rewrite /= Hk_ret /=.
        ewp_unfold_all; cbn; rewrite Hk_ret; by iMod "Hwp". }

      wp_case_is_throw m Hthrow; cbn.
      (* Case : [m1] is [throw _]; trivial  *)
      { iMod "Hwp"; by iFrame. }

      (* Case : [m1] is not [throw _]. *)
      rewrite Houtcome. ewp_unfold_head.

      (* Since [m] is not an outcome, [try m f h] is not an outcome, either. *)
      not_outcome: try m f h.

      (* Process a step of computation. *)
      intro_state; spec_state; iModIntro.

      construct_wp_nonret.

      (* Get more information out of [e2]; *)
      step_inv Hstep.

      (* Can use information from above to get [wp] about stepped computation *)
      spec_step.

      (* TODO: Clean up *)
      destruct (is_eff m) eqn: Hm.
      { destruct p; apply (is_eff_try m f h) in Hm; rewrite Hm.
        iDestruct "Hwp" as "[Si [Heff Hwp]]"; iFrame.
        iIntros (??) "SI"; iSpecialize ("Hwp" with "SI").
        iMod "Hwp". iModIntro; iNext.
        by iApply ("IH" with "Hwp"). }

      destruct m; inversion Hm; cbn.
      all: try (iDestruct "Hwp" as "[SI Hwp]"; iFrame;
                  by iApply ("IH" with "Hwp")).

      3 : {
        destruct c; inversion H1;
        try (iDestruct "Hwp" as "[SI Hwp]"; iFrame;
        by iApply ("IH" with "Hwp")). }

      all: inversion Hstep'. }
  Qed.

  (* A binary version of the previous lemma. *)

  (* This version must be preferred when the proof of [m1] requires a case
    analysis. The scope of the case analysis is then limited to the first
    premise, so the proof of [m2] is not duplicated. *)

  Lemma wp_try_binary {A1 A2 X' X} (m1: micro A1 X') (m2: A1 → micro A2 X)
    (h : X' -> micro A2 X) (φ ψ : outcome2 _ _ -> _) :
    WP m1 {{ φ }} ⊢
      (∀ v, φ v -∗
                   (| RET x => WP m2 x {{ v, ψ v }};
                   | EXN y => WP h y {{ v, ψ v }}) v) -∗
                                                        WP (try m1 m2 h) {{ ψ }}.
  Proof.
    iIntros "Hm1 Hm2".
    iApply wp_try.
    iApply (wp_covariant with "Hm1"); try set_solver.
  Qed.



From osiris.semantics Require Import simplification.

Ltac wp_mask_intro Hmod :=
  iApply fupd_mask_intro; [ set_solver | ]; iIntros Hmod.

(* Try to introduce modalities "as much as possible" *)
Ltac try_iModIntro :=
  repeat iModIntro; try iNext; repeat iModIntro.

(* Try to "cleanup" the goal; remove any modalities from the premise that can
   be discharged trivially and then introduce any "straight forward" modalities
  that can be introduced *)
Ltac wp_cleanup_mod :=
  repeat match goal with
    | |- context[environments.Esnoc _
                  ?Hmod (fupd empty empty _)] =>
        iMod Hmod
    end;
  try_iModIntro.

(* Try to restore a mask from a previous mask update. *)
Ltac wp_mask_elim :=
  wp_cleanup_mod;
  match goal with
  | |- environments.envs_entails _ (fupd ?mask1 ?mask2 _) =>
    try match goal with
      | |- context[environments.Esnoc _ ?Hmod (fupd mask1 mask2 emp)] =>
          iMod Hmod as "_"
      end
  end;
  wp_cleanup_mod.

(* -------------------------------------------------------------------------- *)
(** *WP step tactics *)

Ltac wp_try_step := try construct_wp_nonret; destruct_step.
Ltac wp_try_final_step := try construct_wp_nonret; simp_final_step_diagram.

(* Try to take a step of [wp] for goals of shape
    [⊢ WP e {{ v, Ψ v }}] where [e] is known to take a step, and generate
    appropriate [WP] subgoals for each possible step. *)
Ltac wp_step :=
  try ewp_unfold_head; try intro_state;
  (* Introduce mask for entering into WP *)
  wp_mask_intro "Hmod";
  (* Try to step, possibly generating multiple subgoals if there is more than
     one way of stepping *)
  wp_try_step;
  (* Eliminate mask to "exit" WP *)
  wp_mask_elim;
  (* Frame state interp *)
  try wp_frame.

(* We enter into the WP of the goal, eliminate modalities, use the fact
  that the program can be the final step of a diagram and frame the state
  interp. *)
Ltac wp_final_step_diagram :=
  try ewp_unfold_head; try intro_state;
  (* Introduce mask for entering into WP *)
  wp_mask_intro "Hmod";
  (* Try to step in a unique way *)
  wp_try_final_step;
  (* Eliminate mask to "exit" WP *)
  wp_mask_elim;
  (* Frame state interp *)
  try wp_frame.

(* Try to take a step of [wp] but leave the mask associated with [Hmod] unresolved *)
Tactic Notation "wp_step_mask" constr(Hmod) :=
  try ewp_unfold_head; try intro_state;
  wp_mask_intro Hmod; wp_try_step.


  (* A reasoning rule for [choose]. *)

  (* A non-separating conjunction is used to express the idea that
    either [m1] or [m2] is executed, but not both. Thus, there is
    no need to split the current resource. It suffices to prove
    that both [m1] and [m2] are safe under the current resource. *)

  Lemma wp_choose {res exn} (m1 m2 : micro res exn) ψ :
    ▷ (WP m1 {{ ψ }} ∧ WP m2 {{ ψ }}) ⊢
      WP (choose m1 m2) {{ ψ }}.
  Proof.
    iIntros "H"; wp_step.
    { iDestruct "H" as "[H _]".
      rewrite try2_ret_right; iFrame. }

    { iDestruct "H" as "[_ H]".
      rewrite try2_ret_right; iFrame. }
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [CAlloc]. *)

  (* The standard memory allocation rule of Separation Logic. *)

  Lemma wp_alloc {A X} s E v (k : outcome2 loc exn → micro A X) (φ : outcome2 A X -> _) :
    ▷ (∀ l,
          mapsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤ -∗
          WP (k (O2Ret l)) @ s; E {{ φ }}) ⊢
    WP (Stop CAlloc v k) @ s; E {{ φ }}.
  Proof.
    iIntros "H".
    wp_step_mask "Hmod".
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi HH]"; first done.
    wp_mask_elim.

    wp_frame. by iApply "H".
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma wp_store {A X} s E l v v' (k : outcome2 _ exn → micro A X) φ :
    mapsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        mapsto l (DfracOwn 1) (V v') -∗
        WP (k (O2Ret tt)) @ s; E {{ φ }}
      ) -∗
    WP (Stop CStore (l, v') k) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; wp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%";
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    wp_mask_elim. wp_frame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* The standard memory load rule of Separation Logic. *)

  Lemma wp_load {A X} s E l v dq (k: outcome2 _ exn → micro A X) φ :
    mapsto l dq (V v) ⊢
    ▷ (
        mapsto l dq (V v) -∗
        WP (k (O2Ret v)) @ s; E {{ φ }}
      ) -∗
    WP (Stop CLoad l k) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; wp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.

    wp_mask_elim. wp_frame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Effect-relevant rules *)

  (* LATER: Without [eval], [CPerform] on its own doesn't do anything interesting *)
  Lemma wp_perform {A X} v (k : outcome2 _ exn -> micro A X) s E φ :
    ⊢ WP (Stop CPerform v k) @ s; E {{ φ }}.
  Proof.
    ewp_unfold_head; intro_state; wp_mask_intro "Hmod".
  Abort.

  Lemma wp_handle_ret {A X} v (h : outcome3 _ _ -> micro A X) s E φ:
    WP h (O3Ret v) @ s; E {{ v, φ v }}
    ⊢ WP (Handle (Ret v) h) @ s; E {{ φ }}.
  Proof.
    iIntros "Hwp". wp_step. inversion Hstep.
  Qed.

  Lemma wp_handle_throw {A X} e (h : outcome3 _ _ -> micro A X) s E φ:
    WP h (O3Throw e) @ s; E {{ v, φ v }}
                            ⊢ WP (Handle (Throw e) h) @ s; E {{ φ }}.
  Proof.
    iIntros "Hwp". wp_step. inversion Hstep.
  Qed.

  (* NEXT : Move to [step.v] *)
  Lemma invert_step_continue {A E} σ σ' l v k c m' :
    σ !! l = Some (K c) →
    @step A E (σ, Stop CContinue (l, v) k) (σ', m') →
    σ' = <[l := Shot]> σ ∧
    m' = try2 (continue c v) k.
  Proof.
    intros Heq Hstep. destruct_step.
    rewrite Heq in x. inversion x; subst. by split.
  Qed.

  (* NEXT : Move to [step.v] *)
  Lemma invert_step_discontinue {A E} σ σ' l v k c m' :
    σ !! l = Some (K c) →
    @step A E (σ, Stop CDiscontinue (l, v) k) (σ', m') →
    σ' = <[l := Shot]> σ ∧
    m' = try2 (discontinue c v) k.
  Proof.
    intros Heq Hstep. destruct_step.
    rewrite Heq in x. inversion x; subst. by split.
  Qed.

  Lemma wp_continue {A X} l v c (k : _ -> micro A X) s E φ:
    mapsto l (DfracOwn 1) (K c) ⊢
    ▷ (
        mapsto l (DfracOwn 1) Shot -∗
        WP (try2 (continue c v) k) @ s; E {{ φ }}
      ) -∗
    WP (Stop CContinue (l, v) k) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; wp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_continue in Hstep; [ destruct Hstep | eauto ]. subst.

    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    wp_mask_elim. wp_frame.
    iApply ("Hwp" with "Hl").
  Qed.

  Lemma wp_disccontinue {A X} l v c (k : _ -> micro A X) s E φ:
    mapsto l (DfracOwn 1) (K c) ⊢
    ▷ (
        mapsto l (DfracOwn 1) Shot -∗
        WP (try2 (discontinue c v) k) @ s; E {{ φ }}
      ) -∗
    WP (Stop CDiscontinue (l, v) k) @ s; E {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; wp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_discontinue in Hstep; [ destruct Hstep | eauto ]. subst.

    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    wp_mask_elim. wp_frame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* TODO ------------------------------ *)
  (* ------------------------------------------------------------------------ *)
  (* Invert cases where there are premises of the form *)
  (*   [WP (ret _) _] [WP crash _] or [WP (throw _) _] *)
  Local Ltac wp_invert :=
    match goal with
    | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
        match goal with
        (* WP crash Ψ is an absurd goal; can conclude immediately *)
        | |- context [environments.Esnoc _ ?Hwp (wp _ _ crash _)] =>
            iPoseProof (invert_wp_crash with SI) as "Hinv";
              by iMod ("Hinv" with "[$]") as "%"
        (* WP throw Ψ *)
        | |- context [environments.Esnoc _ ?Hwp (wp _ _ (throw _) _)] =>
            iPoseProof (invert_wp_throw with SI) as "Hinv";
            iMod ("Hinv" with "[$]") as "[$ Hinv]";
            wp_mask_intro "Hmod"; wp_mask_elim; wp_frame
        | |- context [environments.Esnoc _ ?Hwp (wp _ _ (ret _)_)] =>
            iMod (invert_wp_ret with "[$][$]") as "[Hsi Hret]"
        end
    end.

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

    (* Make a case study over the possible step. In each case, use FupdIntro to
      add the modality [ |={E,∅}=> ] in front of the goal. *)
     wp_unfold_head. intro_state.

     wp_mask_intro "Hmod".
     construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    (* We now examine each of the ways in which [Par m1 m2 k z] can step. *)
    { (* Case: [StepParRetRet].
        Both [m1] and [m2] represent outcomes [v1] and [v2]. One can consume [H1]
        and [H2] to learn that the outcomes respect their postconditions.
        The inversion does not consume the state-interpretation, which can be
        framed behind the modalities. *)
      wp_invert; iRename "Hret" into "Hret'"; wp_invert.

      wp_mask_intro "Hmod"; wp_mask_elim.

      (* Finally, use the hypothesis on [k] to finish the proof. *)
      iSpecialize ("Hjoin" with "Hret Hret'"); by iFrame. }

    (* In the four following cases, one of the branches of the [Par] is either a
      [crash] or [throw _].

      We invert the cases where there are premises of the form [WP crash _] or
        [WP (throw _) _] *)
    1-4: wp_invert;
      try iApply ("Hexn1" with "[$]");
      try iApply ("Hexn2" with "[$]").

    { (* Case: [StepParLeft] *)
      (* [m1] steps to [m'1]. Steps preserve the conjunction of the [WP] and the
        state interpretation. Some modalities need to be stripped from the
        result. *)
      iPoseProof (wp_step Hstep with "Hsi H£ H1") as ">H1".

      wp_mask_elim.

      iMod "H1"; iModIntro.

      iDestruct "H1" as "[$ H1]"; wp_frame.

      (* The induction hypothesis ends the proof. *)
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* Case: [StepParRight]
        This case is similar to the previous one. *)
      iMod (wp_step Hstep with "Hsi H£ H2") as ">H2".

      wp_mask_elim.
      iMod "H2"; iModIntro.

      iDestruct "H2" as "[$ H2]"; wp_frame.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }
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
    destruct (int.lt i2 i1) eqn:Hlt; wp_unfold_head; wp_step; reduce_loop.

    { (* Finally, expand the definition of the helper function [loop]. *)
      by iFrame. }

    { (* In the base case, the loop is over. One can use the hypothesis to end
          the proof. *)
      iApply wp_try.
      iFrame; rewrite bind_as_try; by iApply wp_try. }
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
    wp_step.

    { (* The loop is over. *)
      replace i1 with (S i2) ; [ | lia].
      iApply wp_try.

      reduce_loop. iApply wp_ret.
      iApply ("Hccl" with "Hinit"). }

    { (* The body of the loop will be executed (not for the last time). *)
      reduce_loop.

      (* The loop is really a try... *)
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
        destruct v; [ | done]; cbn.

        replace (add (repr i1) int.one) with (repr (S i1)); [ done | ].
        rewrite add_repr_repr; f_equal; lia. }

    { (* Last run of the loop. *)
      iApply wp_try.

      reduce_loop.
      iApply (wp_bind_binary with "[Hinit Hpreservation]");
        first iApply ("Hpreservation" with "[//][//]Hinit").
      iIntros(v)"Hinit".
      destruct v; [ | done]; cbn.
      iSpecialize ("Hccl" with "Hinit").

      assert (Hlt: int.lt (repr i2) (add (repr i2) int.one) = true).
      { rewrite add_repr_repr lt_repr_repr; unfold representable in *; lia. }

      wp_unfold (Stop CLoop (η, x, add (repr i2) int.one, repr i2, e) ret throw).
      intro_state.

      iRename "H£" into "H£'".
      wp_step.
      iApply wp_try. reduce_loop. do 2 iApply wp_ret.
      iExact "Hccl". }
  Qed.

  (* LATER: do something with this? *)
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

  Lemma wp_simp {R E} (m ms : micro R E) φ :
    simp m ms →
    WP ms {{ φ }} ⊢
    WP m  {{ φ }}.
  Proof.
    (* Proceed by Löb induction. *)
    iLöb as "IH" forall (m ms).
    (* Introduce the hypotheses. *)
    iIntros (Hsimp) "Hwp".

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

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      wp_final_step_diagram;
        (* We are then able to use the induction hypothesis. *)
        iApply ("IH" with "[//] Hwp"). }

    (* Examine [ms] on whether it is a [throw]. *)
    wp_case_is_throw ms Hthrow_ms.
    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      wp_final_step_diagram;
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* [ms] is neither a [ret _] or [throw _]. *)

    (* Then, [WP ms ...] implies than [ms] can step.
    This implies that [m], too, can step. *)

    iAssert (|={⊤}=> ⌜ can_step (σ, m) ⌝
                    ∗ wp NotStuck ⊤ ms φ
                    ∗ state_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".
    { iApply ((fupd_plain_keep_l ⊤ ⌜can_step (σ, m)⌝
                                (wp NotStuck ⊤ ms φ ∗ state_interp σ))%I
              with "[$Hwp $Hsi]").
      iIntros "[??]";
        iMod (wp_can_step' with "[$][$]") as "%Hdisj".
      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simp_can_step. }
      destruct H; exfalso; eauto. }

    wp_mask_intro "Hmod". construct_wp_nonret.

    (* We now examine an arbitrary step of [m] to [m']. *)
    (* Exploit the main simulation diagram. *)
    simp_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { wp_mask_elim. wp_frame.
      iApply ("IH" with "[//] Hwp"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    wp_unfold ms.

    pose proof (is_not_ret_or_throw_to_outcome _ Hretms Hthrow_ms) as ->.
    iMod "Hmod" as "_"; spec_state.

    assert (prim_step ms σ nil _ _ nil) by (by constructor).
    iSpecialize ("Hwp" $! _ _ nil H0 with "H£").

    wp_mask_elim.

    iMod "Hwp"; iModIntro.

    iDestruct "Hwp" as "(SI & Hwp & _)"; wp_frame.
    iApply ("IH" with "[//] Hwp").
  Qed.

End wp_rules.
