From stdpp Require Import telescopes.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_localstate.

(* ========================================================================== *)
(** * Protocol. *)

(* LATER: Make the type of state abstract (i.e. Encode .. ) *)
Definition state := Z.

Definition READ {Σ} (St : state -> _) : iEff Σ :=
  (>> x >> ! (VUnit) {{ St x }}; ? (O2Ret (# x)) {{ St x }} @ OS).
Definition WRITE {Σ} St : iEff Σ :=
  (>> x (y : Z) >> ! (# y) {{ St x }}; ? (O2Ret VUnit) {{ St y }} @ OS).
Definition STATE {Σ} (St : state -> _) : iEff Σ := (READ St <+> WRITE St)%ieff.

Lemma upcl_state {Σ} St v Φ :
  iEff_car (upcl OS (STATE (Σ:=Σ) St)) v Φ ⊣⊢
    ((iEff_car (upcl OS (READ  St)) v Φ) ∨
     (iEff_car (upcl OS (WRITE St)) v Φ)).
Proof. by rewrite /STATE; apply upcl_sum. Qed.

Lemma upcl_read {Σ} St v Φ :
  iEff_car (upcl OS (READ (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x, ⌜ v = VUnit ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (#x))))%I.
Proof. by rewrite /READ (upcl_tele' [tele _] [tele]). Qed.

Lemma upcl_write {Σ} St v Φ :
  iEff_car (upcl OS (WRITE (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x y, ⌜ v = # y ⌝ ∗ St x ∗ (St y -∗ Φ (O2Ret #())))%I.
Proof. by rewrite /WRITE (upcl_tele' [tele _ _] [tele]). Qed.

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth.
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


(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!osirisGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Definition run := __fun6.

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

  Lemma run_spec Φ init main :
    (* FIXME: The notation spacing is weird for [EWP]. *)
    (∀ St, St init -∗ EWP call main #() <| STATE St |> {{ RET v, Φ v }}) -∗
    EWP call_anon_fun stdlib_env run [ #init ; main] {{ RET v, Φ v }}.
  Proof.
    (* unfold run. *)
    iIntros "Hmain". iApply ewp_fupd.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]". iModIntro.

    (* -------------------------------------------------------------------------- *)
    (* 1. Symbolic execution..? *)
    rewrite /call_anon_fun /=. rewrite bind_bind /eval_anon_fun /run.

    do 2 (Bind; Simp; Ret; cbn).

    rewrite /__fun5.
    Simp.

    (* FIXME ? The [simp_enter_call_VClo] should not be needed explicitly *)
    { eapply simp_enter_call_VClo.
      with_strategy transparent [eval_bindings] unfold eval_bindings.
      cbn. eapply SimpEval. }

    rewrite try2_ret_right.

    (* -------------------------------------------------------------------------- *)
    (* 2. Evaluate allocation of [init] *)
    iApply (ewp_ELet _ _ _ (fun x => ∃ v l, ⌜x = O2Ret ([(v, VLoc l)])⌝ ∗ l ↦ V (VInt (repr init))))%I.
    (* TODO: Version of [ELet] where we know that the evaluation of the let-bound
      term will not fail *)
    { (* FIXME : some auxiliary lemma about [eval_bindings] *)
      with_strategy transparent [eval_bindings] unfold eval_bindings.
      cbn. Simp.

      (* Allocate a new location with value [init] *)
      iApply ewp_alloc.
      iNext.

      iIntros (?) "Hl". cbn.
      iApply ewp_simp.
      { eapply simp_widen.
        rewrite /irrefutably_extend. (* FIXME *)
        simp. }

      iApply ewp_value.
      iExists "var", l; by iFrame. }

    { iIntros (?) "H"; by iDestruct "H" as (???) "H". }

    (* TODO: Invert the conclusion from the successful let-bound evaluation *)
    iIntros (?) "H"; iDestruct "H" as (???) "Hl"; inversion H; subst; clear H.
    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] !! *)

    (* rewrite eval_eval'; cbn. *)
    (* Bind. *)
    (* (* Prove specification over handler. *) *)
    (* iApply (ewp_bind' (AppRCtx _)). { done. } *)
    (* iApply (ewp_deep_try_with with "[Hstate Hmain]"). *)
    (* { iApply "Hmain". by iApply "Hstate". } *)
    (* iLöb as "IH" forall (γ init). *)
    (* rewrite !deep_handler_unfold. iSplit; [|iSplit]; *)
    (* last by iIntros (??) "HFalse"; rewrite upcl_bottom. *)
    (* - iIntros (y) "Hy". by ewp_pure_steps. *)
    (* - iIntros (args k). *)
    (*   rewrite upcl_state upcl_write upcl_read. *)
    (*   iIntros "[[%x (->&Hx&Hk)]|[%x [%y (->&Hx&Hk)]]]"; *)
    (*   ewp_pure_steps; ewp_bind_rule. *)
    (*   + iDestruct (ghost_var_agree γ x init with "[$]") as %->. *)
    (*     iApply (ewp_mono with "[Hk Hpoints_to Hx]"). *)
    (*     { iSpecialize ("IH" with "Hpoints_to"). *)
    (*       by iApply ("Hk" with "Hx IH"). } *)
    (*     by auto. *)
    (*   + iApply fupd_ewp. *)
    (*     iMod ((ghost_var_update _ y) with "Hx Hpoints_to") as *)
    (*       "[Hy Hpoints_to]". *)
    (*     iModIntro. simpl. iApply ("Hk" with "Hy"). *)
    (*     by iApply "IH". *)
  Admitted.

End verification.
(* ========================================================================== *)
