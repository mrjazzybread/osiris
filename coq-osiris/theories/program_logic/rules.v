Require Import Coq.Program.Equality.

From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import ewp tactics.
From osiris.semantics Require Import step code simplification.
From osiris Require Import util.order.

(* ------------------------------------------------------------------------ *)

Notation state_interp := osiris_state_interp.

Section ewp_basic_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  (* Values *)
  Lemma ewp_value E Ψ Φ v :
    Φ (O2Ret v) -∗ EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_ret_inv E Ψ Φ v :
    EWP (Ret v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Ret v).
  Proof. iIntros "HRet". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw E Ψ Φ (v : X) :
    Φ (O2Throw v) -∗ EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw_inv E Ψ Φ v :
    EWP (Throw v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ (O2Throw v).
  Proof. iIntros "HThrow". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_crash_inv E (Ψ : P) (Φ : outcome2 A X -> _) σ:
    state_interp σ -∗
    EWP (Crash : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ False.
  Proof.
    ewp_unfold (@crash A X).
    iIntros "Hsi HCrash".
    spec_state. destruct Hred, x; spec_step.
    inversion H0.
  Qed.

  Lemma ewp_outcome2 E Ψ Φ v :
    Φ v -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ". destruct v; simpl.
    { by iApply ewp_value. }
    { by iApply ewp_throw. }
  Qed.

  Lemma ewp_outcome2_inv E Ψ Φ v :
    EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
  Proof.
    iIntros "Hv". destruct v; simpl.
    { by iApply ewp_ret_inv. }
    { by iApply ewp_throw_inv. }
  Qed.

  Lemma ewp_outcome2_fupd E Ψ Φ v :
    (|={E}=> Φ v) -∗ EWP (inject2 v : micro A X) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ".
    destruct v; simpl.
    { by ewp_unfold (@ret A X a). }
    { by ewp_unfold (@throw A X e). }
  Qed.

  (* ------------------------------------------------------------------------ *)

  Lemma ewp_step {σ σ'} E m n {φ} Ψ:
    step (σ, m) (σ', n) →
    state_interp σ -∗
     EWP m @ E <| Ψ |> {{ φ }} ={E,∅}=∗ |={∅}▷=> |={∅,E}=>
     (state_interp σ' ∗ EWP n @ E <| Ψ |> {{ φ }}).
  Proof.
    intro Hstep.
    iIntros "Hsi Hwp".
    ewp_unfold m.
    ewp_case_is_handleable m; spec_state; spec_step.
    by ewp_mask_elim.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_mono E m φ φ' Ψ:
    EWP m @ E <| Ψ |> {{ φ }} -∗
    (∀ a, φ a -∗ φ' a) -∗
    EWP m @ E <| Ψ |> {{ φ' }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "Hwp Hmon".
    ewp_unfold m.
    ewp_case_is_handleable m.
    (* Case: [m] is a [HRet] or a [HThrow]. We easily conclude. *)
    1, 2 : iMod "Hwp"; iModIntro; iApply ("Hmon" with "[$]").

    { (* Case: [m] is a [HPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iApply prot_mono_post; iFrame.
      iIntros (w) "Hewp"; iApply ("IH" with "Hewp").
      by iModIntro. }

    intro_state. spec_state. iModIntro.
    construct_wp_nonret.
    spec_step. ewp_mask_elim.

    iDestruct "Hwp" as ">[$ Hwp]".
    by iApply ("IH" with "Hwp").
  Qed.

  Lemma ewp_prot_mono E m φ Ψ Ψ':
    Ψ ⊆ Ψ' -∗
    EWP m @ E <| Ψ |> {{ φ }} -∗
    EWP m @ E <| Ψ' |> {{ φ }}.
  Proof.
    iLöb as "IH" forall (m).
    iIntros "#Hmono Hwp".
    ewp_unfold m.
    ewp_case_is_handleable m; try done.

    { (* Case: [m] is a [HPerform]. We use [prot_mono]. *)
      iMod "Hwp"; iModIntro.
      iApply prot_mono; iFrame.
      iFrame "Hmono".
      iIntros (w) "Hewp". iNext.
      iApply ("IH" with "Hmono Hewp"). }

    intro_state. spec_state. iModIntro.
    construct_wp_nonret.
    spec_step. ewp_mask_elim.

    iDestruct "Hwp" as ">[$ Hwp]".
    by iApply ("IH" with "[//] Hwp").
  Qed.

  (* TODO: Strong monotonicity principle over ordering on protocols *)

  Lemma ewp_pers_smono E E' Ψ Φ Φ' m :
    E ⊆ E' →
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E'}=∗ Φ' v) -∗
    EWP m @ E' <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros (HE) "He #HΦ".
    iLöb as "IH" forall (m).
    ewp_unfold m.
    ewp_case_is_handleable m.
    1,2: iApply ("HΦ" with "[> -]"); by iApply (fupd_mask_mono E _).
    - iApply (fupd_mask_mono E _); first done.
      iMod "He"; iModIntro.
      iApply prot_mono_post; iFrame.
      iIntros (w) "Hk"; iNext; by iApply ("IH" with "Hk").
    - intro_state.
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      spec_state. iModIntro. construct_wp_nonret.
      spec_step. ewp_mask_elim.
      iDestruct "He" as ">(SI & H)"; iFrame.
      iMod "Hclose"; iApply ("IH" with "H").
  Qed.

  Corollary ewp_pers_mono E Ψ Φ Φ' m :
    EWP m @ E <| Ψ |> {{ Φ }} -∗
    □ (∀ v, Φ v ={E}=∗ Φ' v) -∗
    EWP m @ E <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros "He #HΦ".
    by iApply (ewp_pers_smono with "He").
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd_post E m Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => |={E}=> Φ v }} -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (ewp_pers_mono with "He").
    auto.
  Qed.

  (* TODO: Change to typeclass for modality elimination *)
  Lemma ewp_fupd E m Ψ Φ :
    (|={E}=> EWP m @ E <| Ψ |> {{ Φ }}) -∗
    EWP m @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "He".
    ewp_unfold_all. destruct (is_handleable m).
    { destruct h; iMod "He"; done. }
    intro_state. iMod "He".
    spec_state. by iFrame.
  Qed.

  Lemma ewp_can_step {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E, ∅}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None⌝.
  Proof.
    iIntros "SI Hwp".
    ewp_unfold_all.
    ewp_case_is_handleable m.
    1-3: try iMod "Hwp";
        try (iApply fupd_mask_intro; first set_solver);
        iIntros "_"; iPureIntro; right; eauto.

    spec_state. iModIntro. iPureIntro; auto.
  Qed.

  Lemma ewp_can_step' {σ} Ψ φ m E:
    state_interp σ -∗
    EWP m @ E <| Ψ |> {{ φ }} ={E}=∗
    ⌜can_step (σ, m) ∨ is_handleable m  <> None⌝.
  Proof.
    iIntros.
    iPoseProof (ewp_can_step with "[$][$]") as "?".
    iApply (fupd_plain_mask_empty with "[$]").
  Qed.

End ewp_basic_rules.

Section ewp_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma is_handleable_try_None {B X'} m (f : A -> micro B X') (h : X -> micro B X'):
    is_handleable m = None ->
    is_handleable (try m f h) = None.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H1; done.
  Qed.

  Lemma is_handleable_try2_None {B X'} m (f : _ -> micro B X'):
    is_handleable m = None ->
    is_handleable (try2 m f) = None.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H1; done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)

  Lemma ewp_try2 {B X'} E m (f : _ -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{ fun v => EWP (f v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP (try2 m f) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iLöb as "IH" forall (m f Ψ Φ).
    iIntros "Hwp".
    ewp_case_is_handleable m.
    (* Case: [m1] is [ret _]. *)
    (* The result is immediate. *)
    { iPoseProof (ewp_ret_inv with "[$]") as "Hret"; cbn.
      by iApply ewp_fupd. }

    (* Case : [m1] is [throw _]; trivial  *)
    { ewp_unfold (throw (A := A) e); by iApply ewp_fupd. }

    (* Case : [m1] is [Perform _ _]. *)
    { cbn. ewp_unfold_all. iMod "Hwp"; iModIntro.
      iApply prot_mono_post; iFrame.
      iIntros (w) "Hewp".
      iNext; by iSpecialize ("IH" with "Hewp"). }

    (* Since [m] is not handleable, [try m f h] is not handleable, either. *)
    ewp_unfold_all; rewrite Hhm.
    apply (is_handleable_try2_None m f) in Hhm; rewrite Hhm.

    (* Process a step of computation. *)
    intro_state. spec_state.
    iModIntro. construct_wp_nonret.

    (* Get more information out of [e2]; *)
    apply invert_step_try2 in Hstep; auto; destruct Hstep as (?&Hstep&->).

    (* Can use information from above to get [wp] about stepped computation *)
    spec_step.
    ewp_mask_elim. iDestruct "Hwp" as ">(SI & Hwp)"; iFrame.
    iModIntro.

    (* Apply induction hypothesis  *)
    by iApply ("IH" with "Hwp").
  Qed.

  Lemma ewp_try {B X'} E m (f : A -> micro B X') (h : X -> micro B X') Ψ Φ :
    EWP m @ E <| Ψ |> {{| RET v => EWP (f v) @ E <| Ψ |> {{ Φ }};
                        | EXN v => EWP (h v) @ E <| Ψ |> {{ Φ }}}} -∗
    EWP (try m f h) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply ewp_try2.
    iApply (ewp_mono with "Hwp").
    iIntros ([]) "Hwp"; by cbn.
  Qed.

  (** *Bind rule *)
  Lemma ewp_bind {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ RET v, EWP (k v) @ E <| Ψ |> {{ Φ }} }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]"). iIntros (a) "H".
    destruct a; done.
  Qed.

  Lemma ewp_bind_exn {B} E m (k : _ -> micro B X) Ψ Φ :
    EWP m @ E <| Ψ |> {{| RET v => EWP (k v) @ E <| Ψ |> {{ Φ }};
                        | EXN v => Φ (O2Throw v) }} -∗
    EWP bind m k @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]"). iIntros (a) "H".
    destruct a. done. by iApply ewp_throw.
  Qed.

  (** *Fmap rule *)
  Lemma ewp_fmap {B} E (f : A -> B) (m : micro A X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ RET v, Φ (f v) }} -∗
    EWP fmap f m @ E <| Ψ |> {{ RET v, Φ v }}.
  Proof.
    iIntros "Hwp". iApply ewp_bind.
    iApply (ewp_mono with "[$]"). iIntros (?) "H".
    destruct a; last done. cbn.
    iApply ewp_value; by cbn.
  Qed.

(* ------------------------------------------------------------------------ *)

  (* [CAlloc]. *)

  (* The standard memory allocation rule of Separation Logic. *)

  Lemma ewp_alloc {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          mapsto l (DfracOwn 1) (V v) -∗
          EWP (continue k l) @ E <| Ψ |>  {{ φ }}) ⊢
    EWP (Stop CAlloc v k) @ E <| Ψ |>  {{ φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_step.
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH _]]"; first done.
    ewp_mask_elim. iFrame. by iApply "H".
  Qed.

  Lemma ewp_alloc' {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          mapsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤ -∗
          EWP (continue k l) @ E <| Ψ |> {{ φ }}) ⊢
      EWP (Stop CAlloc v k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_step.
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH HM]]"; first done.
    ewp_mask_elim. iFrame. by iApply "H"; iFrame.
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma ewp_store {B Y} E l v v' (k : _ → micro B Y) φ Ψ :
    mapsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        mapsto l (DfracOwn 1) (V v') -∗
        EWP (continue k tt) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CStore (l, v') k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%";
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* The standard memory load rule of Separation Logic. *)

  Lemma ewp_load {B Y} E l v dq (k: _ → micro B Y) φ Ψ:
    mapsto l dq (V v) ⊢
    ▷ (
        mapsto l dq (V v) -∗
        EWP (continue k v) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CLoad l k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.

    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

End ewp_rules.

(* ------------------------------------------------------------------------ *)
(* Invert cases where there are premises of the form
          [EWP (ret _) _] [EWP crash _] or [EWP (throw _) _] *)

Local Ltac ewp_invert :=
  match goal with
  | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
      match goal with
      (* EWP throw *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
          iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
      (* EWP ret *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
          iMod (ewp_ret_inv with "[$]") as "HΦ"
      (* EWP crash *)
      | |- context [environments.Esnoc _ ?Hwp (ewp_def _ Crash _ _)] =>
          match goal with
          | |- context [environments.Esnoc _ ?SI (state_interp _)] =>
            iMod (ewp_crash_inv with "[$][$]") as "%"
          end
      end
  end.

(* ------------------------------------------------------------------------ *)

(* Effect and handler rules *)

Section wp_handler_rules.

  Context `{!osirisGS Σ} `{protocol_wf Σ P}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Implicit Type Ψ : P.
  Import ewp_rules_tactics.

  Lemma ewp_stop_perform {B X'} E Ψ v Φ (k : _ -> micro B X'):
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }} >> -∗
    EWP (Stop CPerform v k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP".
    ewp_unfold_head.
    iApply prot_mono_post; iFrame. iModIntro.
    iIntros (?) "HΦ". by iNext.
  Qed.

  Lemma ewp_perform E Ψ v Φ:
    Ψ allows perform v << Φ >> ⊢ EWP (perform v) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HP". iApply ewp_stop_perform.
    iApply prot_mono_post; iFrame.
    iIntros (?) "HΦ". iNext.
    cbn. iApply ewp_outcome2; by cbn.
  Qed.

  Lemma ewp_perform_inv {B X'} E Ψ v Φ (k : _ -> micro B X'):
    EWP (Stop CPerform v k) @ E <| Ψ |> {{ Φ }} ={E}=∗
    Ψ allows perform v << fun w => ▷ EWP (k w) @ E <| Ψ |> {{ Φ }} >>.
  Proof.
    iIntros "HP".
    ewp_unfold_all.
    iApply prot_mono_post; iMod "HP"; iModIntro; iFrame.
    iIntros (?) "HΦ". by iNext.
  Qed.

  Definition shallow_handler E Ψ (Φ : outcome2 val exn -d> iProp Σ)
    (h : outcome3 val exn -> microvx)
    Ψ' Φ' :=
    ((∀ o, Φ o -∗ ▷ EWP (h o) @ E <| Ψ' |> {{ Φ' }}) ∧
    (∀ v l, Ψ allows perform v
        << fun r =>
           match r with
           | O2Ret v => ▷ EWP (stop CContinue (l, v)) @ E <| Ψ |> {{ Φ }}
           | O2Throw e => ▷ EWP (stop CDiscontinue (l, e)) @ E <| Ψ |> {{ Φ }}
            end >> -∗
       ▷ EWP (h (O3Perform v l)) @ E <| Ψ' |> {{ Φ' }}))%I.

  (* Specification for handlers (shallow by default) *)
  Lemma ewp_handler E Ψ Φ Ψ' Φ' e h:
    EWP e @ E <| Ψ |> {{ Φ }} -∗
    shallow_handler E Ψ Φ h Ψ' Φ' -∗
    EWP (Handle e h) @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [e] [h] and [eh]. *)
    iLöb as "IH" forall (e h).

    iIntros "He Hsh".
    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    1,2: (* [StepHandleRet] and [StepHandleThrow] *)
      ewp_invert; iFrame;
      iDestruct "Hsh" as "[Hsh _]";
      iSpecialize ("Hsh" with "HΦ");
      try iMod "Hsh";
      by ewp_mask_intro "Hmod"; ewp_mask_elim.

    { (* [StepHandlePerform] *)
      iDestruct "Hsh" as "[_ Hsh]".
      iPoseProof (ewp_perform_inv with "[$]") as "HP".
      iMod "HP".

      iDestruct (gen_heap_alloc _ _ (K k) with "Hsi") as ">[Hsi [HH _]]";
        [ exact H0 | ].

      iAssert (prot_spec Ψ e0
                 (fun r =>
                    match r with
                    | O2Ret v => ▷ EWP (stop CContinue (l, v)) @ E <| Ψ |> {{ Φ }}
                    | O2Throw e => ▷ EWP (stop CDiscontinue (l, e)) @ E <| Ψ |> {{ Φ }}
                    end))%I
        with "[HP HH]" as "HΨ".
      { iApply prot_mono_post; iFrame.
        iIntros (?) "Hwp"; cbn.
        destruct w.
        { iNext.
        rename σ into σ'.
        ewp_unfold_head.
        intro_state.
        ewp_mask_intro "Hmod". unfold stop.
        construct_wp_nonret. destruct_step.
        iDestruct (gen_heap_valid with "Hsi HH") as %Hl.
        rewrite Hl in x; inversion x; subst.
        rewrite try2_ret_right.
        iDestruct (gen_heap_update with "Hsi HH") as ">(Hsi & HH)";
          iFrame.
        by ewp_mask_elim. }

        { iNext.
        rename σ into σ'.
        ewp_unfold_head.
        intro_state.
        ewp_mask_intro "Hmod". unfold stop.
        construct_wp_nonret. destruct_step.
        iDestruct (gen_heap_valid with "Hsi HH") as %Hl.
        rewrite Hl in x; inversion x; subst.
        rewrite try2_ret_right.
        iDestruct (gen_heap_update with "Hsi HH") as ">(Hsi & HH)";
          iFrame.
        by ewp_mask_elim. } }

      iSpecialize ("Hsh" with "HΨ").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iFrame. }

    { (* [StepHandleCrash] *)
      by ewp_invert. }

    { (* [StepHandleLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi He") as ">H".
      ewp_mask_elim. iMod "H" as "[$ H]". iModIntro.
      iApply ("IH" with "H Hsh"). }
  Qed.

  (* Par combinator *)
  Lemma ewp_Par {E A1 A2 A3 X' Y} (m1 : micro A1 X') (m2 : micro A2 X')
    (k: outcome2 (A1 * A2) X' → micro A3 Y) {φ} φ1 φ2 Ψ :
      EWP m1 @ E <| Ψ |> {{ φ1 }} ⊢
      EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
      (∀ e, φ1 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ e, φ2 (O2Throw e) -∗ EWP (k (O2Throw e)) @ E <| Ψ |> {{ φ }}) -∗
      (∀ a1 a2,
          φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗
          EWP (k (O2Ret (a1, a2))) @ E <| Ψ |> {{ φ }}) -∗
      EWP (Par m1 m2 k) @ E <| Ψ |> {{ φ }}.
  Proof.
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2 k); iIntros "H1 H2 Hexn1 Hexn2 Hjoin".

    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_step; cbn; iMod "Hmod" as "_"; cbn.

    { (* Case: [StepParRetRet].. *)
      ewp_invert; iRename "HΦ" into "HΦ2"; ewp_invert; iFrame.
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iSpecialize ("Hjoin" with "HΦ HΦ2"); by iFrame. }

    (* In the four following cases, one of the branches of the [Par] is either a
      [crash] or [throw _].

      We invert the cases where there are premises of the form [WP crash _] or
        [WP (throw _) _] *)
    1-4: ewp_invert; try done.

    (* [StepParThrowLeft/Right] *)
    1,2: iMod "HΦ";
        ewp_mask_intro "Hmod"; ewp_mask_elim;
        iFrame;
        try iApply ("Hexn1" with "[$]");
        try iApply ("Hexn2" with "[$]");
        done.

    { (* [ParPerformLeft] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      iPoseProof (ewp_perform_inv with "[$]") as "H1".
      iApply ewp_fupd. iMod "H1"; iModIntro. (* TODO: cleanup *)
      iApply ewp_stop_perform.
      iApply prot_mono_post; iFrame.
      iIntros (?) "Hk".
      iNext.
      iApply ("IH" with "Hk H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParPerformRight] *)
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
      iPoseProof (ewp_perform_inv with "[$]") as "H2".
      iApply ewp_fupd. iMod "H2"; iModIntro. (* TODO: cleanup *)
      iApply ewp_stop_perform.
      iApply prot_mono_post; iFrame.
      iIntros (?) "H2".
      iNext.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParLeft] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H1") as ">H1".
      ewp_mask_elim. iMod "H1" as "[$ H1]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }

    { (* [ParRight] *)
      iPoseProof (ewp_step _ _ _ _ Hstep with "Hsi H2") as ">H2".
      ewp_mask_elim. iMod "H2" as "[$ H2]". iModIntro.
      iApply ("IH" with "H1 H2 Hexn1 Hexn2 Hjoin"). }
  Qed.

  Lemma ewp_par {E A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X') {φ} φ1 φ2 Ψ :
    EWP m1 @ E <| Ψ |> {{ φ1 }} ⊢
    EWP m2 @ E <| Ψ |> {{ φ2 }} -∗
    (∀ e, φ1 (O2Throw e) -∗ φ (O2Throw e))-∗
    (∀ e, φ2 (O2Throw e) -∗ φ (O2Throw e)) -∗
    (∀ a1 a2,
      φ1 (O2Ret a1) -∗ φ2 (O2Ret a2) -∗ φ (O2Ret (a1, a2))) -∗
    EWP (par m1 m2) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hm1 Hm2 Hφ1 Hφ2 Hr".
    iApply (ewp_Par m1 m2 inject2 with "Hm1 Hm2 [Hφ1] [Hφ2] [Hr]").
    { iIntros (?) "Hφ". cbn.
      iApply ewp_throw. iApply ("Hφ1" with "Hφ"). }
    { iIntros (?) "Hφ". cbn.
      iApply ewp_throw. iApply ("Hφ2" with "Hφ"). }
    { iIntros (??) "Hφ1 Hφ2". cbn.
      iApply ewp_value. iApply ("Hr" with "Hφ1 Hφ2"). }
  Qed.

    (* The following lemmas offer reasoning rules for each of the system calls,
    that is, for computations of the form [Stop c x y]. They are simple
    consequences of the operational behavior of these system calls. *)

  (* [CEval]. *)

  Lemma ewp_eval {B E'} E η e (k : _ → micro B E') φ Ψ :
    ▷ EWP (eval η e) @ E <| Ψ |>
        {{ fun v => EWP (k v) @ E <| Ψ |> {{ φ }} }} ⊢
      EWP (Stop CEval (η, e) k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    try ewp_unfold_head; try intro_state;
      (* Introduce mask for entering into WP *)
      ewp_mask_intro "Hmod".
    try construct_wp_nonret; destruct_step.
    ewp_mask_elim;
      (* Frame state interp *)
      try iFrame; cbn.
    by iApply ewp_try2.
  Qed.

  Lemma ewp_eval_ret E η e Ψ (φ : _ -> iPropI Σ):
    ▷ EWP eval η e @ E <| Ψ |>
      {{ fun v => EWP inject2 v @ E <| Ψ |> {{ φ }} }} ⊢
      EWP stop CEval (η, e) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp".
    iApply ewp_eval.
    iNext. iApply (ewp_mono with "Hwp"); iIntros (?) "H"; done.
  Qed.


  Lemma invert_simp_perform {E} {m1 : micro A E} σ v k :
    simp m1 (Stop CPerform v k) →
    match m1 with
    | Stop CPerform v' k' => v = v' /\ (forall o, simp (k' o) (k o))
    | _ => False
    end ∨
      can_step (σ, m1).
  Proof.
    (* The only terms that cannot step are the final terms, and these
     terms cannot be simplified, so the result is almost immediate. *)
    intro h; dependent induction h; simpl in *;
      eauto with step.
    { left; split; eauto. constructor. }
    (* Only [SimpTransitive] requires some work. *)
    destruct (IHh2 _ _ _ _ eq_refl); clear IHh2; [ subst |].
    { destruct m2; try done. destruct c; try done. destruct H0; subst.
      destruct (IHh1 _ _ _ _ eq_refl); eauto.
      left; auto.
      destruct m1; try done. destruct c; try done.
      destruct H0; subst; split; eauto.
      intros; eapply SimpTransitive; eauto. }
    { eauto using invert_simp_can_step. }
  Qed.

  Lemma simp_final_step_diagram_perform {m1 : micro A X} {σ σ' m'1} v k:
    (* If there is a simplification step of [m1] to [m2], *)
    simp m1 (Stop CPerform v k) →
    (* if there is also a reduction step out of [m1], *)
    step (σ, m1) (σ', m'1) →
    (* and if [m2] is final, *)
    (* then this reduction step does not prevent us from reaching [m2]. *)
    σ' = σ ∧
      simp m'1 (Stop CPerform v k).
  Proof.
    intros Hsimp Hstep.
    simp_step_diagram; eauto.
    inversion Hstep.
  Qed.


  Lemma ewp_simp E m ms Ψ φ:
    simp m ms →
    EWP ms @ E <| Ψ |> {{ φ }} ⊢
    EWP m @ E <| Ψ |> {{ φ }}.
  Proof.
    (* Proceed by Löb induction. *)
    iLöb as "IH" forall (m ms).
    (* Introduce the hypotheses. *)
    iIntros (Hsimp) "Hwp".

    destruct (is_handleable m) eqn: Hmh.
    { destruct m; inversion Hmh; subst; try solve [inversion Hsimp];
      clarify_simp; subst; try done.
      inversion Hmh. destruct c; inversion H1; subst.
      clarify_simp.
      iApply ewp_fupd.
      iApply ewp_stop_perform.
      iPoseProof (ewp_perform_inv with "Hwp") as "Hwp".
      iMod "Hwp"; iModIntro.
      iApply prot_mono_post; iFrame.
      iIntros (w) "Hw". iNext.
      iApply ("IH" $! _ _ (H2 w) with "Hw"). }

    (* Examine [ms] on whether it is a [ret]. *)
    ewp_case_is_handleable ms.

    (* Case: [ms] is [ret _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh.
      intro_state. ewp_mask_intro "Hmod".
      iSplitL "".
      { iPureIntro.
        epose proof (invert_simp_final _ Hsimp) as [|];
          [ by prove_final |
            subst; try destruct_is_ret; try destruct_is_throw |
            eauto with can_step ].
        inversion Hmh. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Case : [ms] is [throw _]. *)
    { (* Prove that [m] is a final step in the diagram. *)
      ewp_unfold_head. rewrite Hmh.
      intro_state. ewp_mask_intro "Hmod".
      iSplitL "".
      { iPureIntro.
        epose proof (invert_simp_final _ Hsimp) as [|];
          [ by prove_final |
            subst; try destruct_is_ret; try destruct_is_throw |
            eauto with can_step ].
        inversion Hmh. }
      intro_step.
      eapply simp_final_step_diagram in Hsimp; eauto; last done.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    (* Case : [ms] is [Perform _]. *)
    { ewp_unfold_head. rewrite Hmh.
      intro_state. ewp_mask_intro "Hmod".
      iSplitL "".
      { iPureIntro.
        epose proof (invert_simp_perform _ _ _ Hsimp) as [|];
          [subst; try destruct_is_ret; try destruct_is_throw |
            eauto with can_step ].
        destruct m; try done; destruct c; try done. }
      intro_step.

      eapply simp_perform_step_diagram in Hsimp; eauto.
      destruct Hsimp; subst; iFrame.
      ewp_mask_elim.
      (* We are then able to use the induction hypothesis. *)
      iApply ("IH" with "[//] Hwp"). }

    ewp_unfold_head. rewrite Hmh.
    intro_state.

    iAssert (|={E}=> ⌜ can_step (σ, m) ⌝
                      ∗ EWP ms @ E <| Ψ |> {{ φ }}
                      ∗ state_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".

    { iApply ((fupd_plain_keep_l E ⌜can_step (σ, m)⌝
                 (EWP ms @ E <| Ψ |>  {{ φ }} ∗ state_interp σ))%I
               with "[$Hwp $Hsi]").
      iIntros "[??]".
        iMod (ewp_can_step' with "[$][$]") as "%Hdisj".

      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simp_can_step. }

      exfalso. apply H0; auto. }

    ewp_mask_intro "Hmod".
    construct_wp_nonret.

    simp_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { ewp_mask_elim. iFrame.
      iApply ("IH" with "[//] Hwp"). }

    (* Case: the reduction step is preserved through the diagram. *)
    (* We can now commit to stepping [ms] -- a commitment which we have
    carefully avoided up to this point. *)
    ewp_unfold ms. rewrite Hhm. iMod "Hmod". spec_state. spec_step.
    ewp_mask_elim.
    iDestruct "Hwp" as ">(SI & Hwp)"; iFrame.
    iModIntro; iApply ("IH" with "[//] Hwp").
  Qed.

End wp_handler_rules.
