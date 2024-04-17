From stdpp Require Import telescopes.

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_localstate.

(* ========================================================================== *)
(** * Protocol. *)

Section localstate_example.
(* Location for the get/set eff *)
Context (read_eff write_eff : loc).
Context (Hloc: address read_eff <> address write_eff).

(* LATER: Make the type of state abstract (i.e. Encode .. ) *)
Definition state := int.

Definition read : val := VXData read_eff (VTuple []).
Definition write (v : state) : val := VXData write_eff (VTuple [VInt v]).

Definition READ {Σ} (St : state -> _) : iEff Σ :=
  (>> x >> ! (read) {{ St x }}; ? (O2Ret (VInt x)) {{ St x }} @ OS).
Definition WRITE {Σ} St : iEff Σ :=
  (>> x y >> ! (write y) {{ St x }}; ? (O2Ret VUnit) {{ St y }} @ OS).
Definition STATE {Σ} (St : state -> _) : iEff Σ := (READ St <+> WRITE St)%ieff.

Lemma upcl_state {Σ} St v Φ :
  iEff_car (upcl OS (STATE (Σ:=Σ) St)) v Φ ⊣⊢
    ((iEff_car (upcl OS (READ  St)) v Φ) ∨
     (iEff_car (upcl OS (WRITE St)) v Φ)).
Proof. by rewrite /STATE; apply upcl_sum. Qed.

Lemma upcl_read {Σ} St v Φ :
  iEff_car (upcl OS (READ (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x, ⌜ v = read ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (VInt x))))%I.
Proof. by rewrite /READ (upcl_tele' [tele _] [tele]). Qed.

Lemma upcl_write {Σ} St v Φ :
  iEff_car (upcl OS (WRITE (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x y, ⌜ v = write y ⌝ ∗ St x ∗ (St y -∗ Φ (O2Ret #())))%I.
Proof. by rewrite /WRITE (upcl_tele' [tele _ _] [tele]). Qed.

(* ========================================================================== *)
(** * Verification. *)

(* -------------------------------------------------------------------------- *)
(** Ghost Theory. *)

Section ghost_theory.
  Context `{!inG Σ (excl_authR (leibnizO val))}.

  Definition auth_state γ v := own γ (●E (v : ofe_car (leibnizO val))).
  Definition points_to  γ v := own γ (◯E (v : ofe_car (leibnizO val))).

  Lemma ghost_var_alloc v : ⊢ (|==> ∃ γ, auth_state γ v ∗ points_to γ v)%I.
  Proof.
    iMod (own_alloc ((●E (v : ofe_car (leibnizO val))) ⋅
                     (◯E (v : ofe_car (leibnizO val))))) as (γ) "[??]";
    [ apply excl_auth_valid | eauto with iFrame ]; done.
  Qed.
  Lemma ghost_var_agree γ v w : ⊢ (auth_state γ v ∗ points_to γ w) → ⌜ v = w ⌝.
  Proof.
    iIntros "[H● H◯]".
    by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agree_L.
  Qed.
  Lemma ghost_var_update γ w u v :
    auth_state γ u -∗ points_to γ v ==∗ auth_state γ w  ∗ points_to γ w.
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E (w : ofe_car (leibnizO val)) ⋅
                              ◯E (w : ofe_car (leibnizO val)))
      with "Hγ● Hγ◯") as "[$$]";
    [ apply excl_auth_update | ]; done.
  Qed.

End ghost_theory.

Opaque auth_state.

(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!osirisGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Definition run := __fun7.

  (* TODO: Move *)
  Definition eval_anon_fun η f := eval η (EAnonFun f).

  Fixpoint call_anon_fun_ (arg : list val) (acc : microvx) : microvx :=
    match arg with
      | nil => acc
      | x :: tl =>
          call_anon_fun_ tl (bind acc (fun f => call f x))
    end.

  (* LATER: Make this normal form. *)
  Definition call_anon_fun η f args :=
    call_anon_fun_ args (eval_anon_fun η f).

  Local Instance encode_state : Encode state.
  constructor. exact VInt.
  Defined.

  (* TODO: Move *)
  (* LATER: Can we generalize this so we don't manually write down existentials
     everywhere? *)
  (* Specialized postconditions *)
  Definition val_points_to (v : val) (b : step.block) :=
    (∃ l, ⌜v = VLoc l⌝ ∗ l ↦ b)%I.

  Fact val_points_to_unfold l b :
    l ↦ b ⊣⊢ val_points_to (VLoc l) b.
  Proof.
    rewrite /val_points_to.
    iSplit; iIntros "H".
    { iExists _; by iFrame. }
    { iDestruct "H" as (? Heq) "H"; by inversion Heq. }
  Qed.

  Definition env_post (η : env) (Φ : iProp Σ) := (λ v, ⌜v = η⌝ ∗ Φ)%I.

  Lemma run_spec Φ init main :
    let env := [("Get", (VLoc read_eff)); ("Set", (VLoc write_eff))] ++ stdlib_env in
    (∀ St, St init -∗ EWP call main #() <| STATE St |> {{ RET v, Φ v }}) -∗
    EWP call_anon_fun env run [ #init ; main]
      {{ RET # v, Φ (snd (v : state * val)) }}.
  Local Ltac ecbn := cbn -[pre_eval_match_aux].
  Proof.
    ecbn. iIntros "Hmain". iApply ewp_fupd.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]". iModIntro.

    (* -------------------------------------------------------------------------- *)
    (* 1. Symbolic execution..? *)

    rewrite /call_anon_fun /= bind_bind /eval_anon_fun /run.

    do 2 (Bind; Simp; Ret; cbn).
    rewrite /__fun6.

    Simp.
    (* FIXME ? The [simp_enter_call_VClo] should not be needed explicitly *)
    { eapply simp_enter_call_VClo.
      with_strategy transparent [eval_bindings] unfold eval_bindings.
      cbn. eapply SimpEval. }

    rewrite try2_ret_right.

    (* -------------------------------------------------------------------------- *)
    (* 2. Evaluate allocation of [init] *)

    iApply (ewp_ELet_total
      (fun x => ∃ l, env_post [("var", VLoc l)] (l ↦ V (VInt init)) x)%I).

    { iApply (ewp_eval_bindings_singleton_total
                (fun v => val_points_to v (V (VInt init)))).
      Simp.

      (* Allocate a new location with value [init] *)
      { iApply ewp_alloc; iNext.
        iIntros (?) "Hl"; Ret.
        by iApply val_points_to_unfold. }

      (* TODO: Invert the conclusion from the successful let-bound evaluation *)
      iIntros (?) "H"; iDestruct "H" as (??) "Hl"; subst.

      iApply ewp_widen.
      { rewrite /irrefutably_extend. (* FIXME *)
        simp. }

      iExists l; by iFrame. }

    (* TODO: Another inversion *)
    iIntros (?) "H"; iDestruct "H" as (??) "Hl"; subst.

    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] !! *)
    iApply ewp_EMatch.

    iApply (ewp_deep_handler with "[Hpoints_to Hmain]").
    { (* 3A. Call to [main] in the handled expression *)
      (* TODO iApply ewp_EApp. *)
      rewrite eval_eval' /=; Simp.
      iApply ("Hmain" $! (fun init => points_to γ (VInt init)) with "Hpoints_to"). }

    (* Finally, we prove the specification over handler. *)

    (* TODO: We need to abstract over the environment "just enough" *)
    remember (VInt init). rewrite {1 2}Heqv; clear Heqv.
    iLöb as "IH" forall (γ main init).
    rewrite deep_handler_spec_unfold. iSplit.
    { (* Outcome case *)
      iIntros (?) "H"; destruct o; [ | done]; ecbn.

      (* TODO: Aux lemma *)
      iClear "IH". cbn.
      iApply ewp_try2.
      with_strategy transparent [extend] unfold extend. (* FIXME *)

      iNext. Ret. cbn. Simp. Bind.
      (* FIXME [evals] is reading from a location, so we cannot use [simp] *)
      with_strategy transparent [evals] unfold evals. (* FIXME *)
      cbn. Simp.

      ewp_tactics.Load "Hl".
      cbn. Ret; cbn. iExists (init, a); cbn; iFrame.
      encode. }

    (* Effectful case *)
     iIntros (e k) "Hp".
     iDestruct (upcl_sum_elim with "Hp") as "[ H_READ | H_WRITE ]".

     (* READ case *)
     { (* TODO: Notation on [iEff_car] is really ugly.. *)
       ecbn.
       rewrite upcl_read.
       iDestruct "H_READ" as (?->) "(Hx & H_READ)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %Hag.

       rewrite {3}/pre_eval_match_aux; ecbn.
       with_strategy transparent [extend] unfold extend. (* FIXME *)

       ecbn.

       inversion Hag; subst.
       iApply ewp_try2. rewrite !bind_bind.
       Simp.
       destruct (locations.eqb read_eff read_eff) eqn: Hread_eff; cycle 1.
       { rewrite Z.eqb_neq in Hread_eff; lia. }

       Simp. Ret. ecbn.

       iDestruct "H" as "(Hauth & Hx)".
       iSpecialize ("H_READ" with "Hx").
       iSpecialize ("H_READ"
          $! iEff_bottom
             (RET v', ∃ v : state * val, ⌜v' = encode_pair v⌝ ∧ Φ v.2))%I.
       iNext.

       Simp. rewrite /as_cont. Simp. Simp.
       ewp_tactics.Load "Hl".
       ecbn.
       iApply "H_READ".
       iNext. iSpecialize ("IH" with "Hauth Hl").
       by rewrite /deep_handler_spec seal_eq. } (* FIXME: opacity control *)

     { (* TODO: Notation on [iEff_car] is really ugly.. *)
       ecbn; rewrite upcl_write.
       iDestruct "H_WRITE" as (??->) "(Hx & H_WRITE)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %Hag.

       rewrite {3}/pre_eval_match_aux; ecbn.
       with_strategy transparent [extend] unfold extend. (* FIXME *)

       ecbn.

       iApply ewp_try2; rewrite !bind_bind; Simp.

       destruct (locations.eqb write_eff read_eff) eqn: Hwrite_eff.
       { by rewrite Z.eqb_eq in Hwrite_eff. }
       clear Hwrite_eff.

       Simp. iNext. Throw. ecbn.
       iApply ewp_try2. Bind.

       destruct (locations.eqb write_eff write_eff) eqn: Hwrite_eff; cycle 1.
       { by rewrite Z.eqb_neq in Hwrite_eff. }

       do 2 (Ret; ecbn).

       iDestruct "H" as "(Hauth & Hx)".

       iApply ewp_fupd.
       iDestruct (ghost_var_update γ (VInt y) with "Hauth Hx") as ">(Hauth & Hx)".
       iSpecialize ("H_WRITE" with "Hx").

       iSpecialize ("H_WRITE"
          $! iEff_bottom
             (RET v', ∃ v : state * val, ⌜v' = encode_pair v⌝ ∧ Φ v.2))%I.

       Simp. iModIntro. Simp.
       Store "Hl".
       ecbn.
       iApply "H_WRITE".
       iNext. iSpecialize ("IH" $! _ main y with "Hauth Hl").
       by rewrite /deep_handler_spec seal_eq. }

   Qed.

End verification.
(* ========================================================================== *)

End localstate_example.
