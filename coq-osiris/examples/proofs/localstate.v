From stdpp Require Import telescopes.

From iris.proofmode Require Import base tactics classes environments.
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
Definition state := Z.

Definition read : val := VXData read_eff (VTuple []).
Definition write (v : state) : val := VXData write_eff (VTuple [ # v]).

Definition READ {Σ} (St : state -> _) : iEff Σ :=
  (>> x  >> ! (read) {{ St x }}; ? (O2Ret (# x)) {{ St x }} @ OS).
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
    (∃ x, ⌜ v = read ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (# x))))%I.
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

  (* LATER: Can we generalize this so we don't manually write down existentials
     everywhere? *)

End ghost_theory.

Section val_points_to.
  Context `{!osirisGS Σ}.

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

End val_points_to.

(* LATER: Give more control on opacity *)
Opaque auth_state.
Opaque encode.encode.

Arguments deep_handler_body : simpl never.

Ltac prove_handler_spec := rewrite deep_handler_spec_unfold; iSplit.

(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!osirisGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Definition run := __fun7.

  Ltac LetV Φ :=
    match goal with
    | |- envs_entails _
          (bi_later (ewp_def _ (eval _ (deco _ (ELet [ Binding (PVar _) _ ] _))) _ _)) =>
        iApply (ewp_ELet_PVar_1 Φ)
    end.

  Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

  Example localstate_run_spec Φ init main :
    let env := [("Get", (VLoc read_eff)); ("Set", (VLoc write_eff))] ++ stdlib_env in
    (∀ St, St init -∗ EWP call main #() <| STATE St |> {{ RET v, Φ v }}) -∗
    EWP call_anonfun env run [ #init ; main]
      {{ RET # v, Φ (snd (v : state * val)) }}.
  Proof.
    cbn zeta.
    iIntros "Hmain". iApply ewp_fupd.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]"; iModIntro.

    (* Call the anonymous function. *)
    Call.

    (* Evaluate allocation of [init] *)
    LetV (fun x => val_points_to x (V (# init)))%I.

    (* Evaluating the let-bound expression *)
    { (* Allocate a new location with value [init] *)
      iApply ewp_ERef. { iApply ewp_EPath; by Ret. }
      iIntros (? -> ?) "?".
      by iApply val_points_to_unfold. }

    (* Continuing with the rest of the computation *)

    (* TODO: Cleaner inversion of facts learned from let-bound term. *)
    iNext.
    iIntros (?) "H"; iDestruct "H" as (?->) "Hl".

    (* LATER : Hide the [V] constructor for blocks *)

    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] -- more interesting part of this proof. *)
    iApply ewp_EMatch.

    iApply (ewp_deep_handler with "[Hpoints_to Hmain]").
    { (* 3A. Call to [main] in the handled expression *)
      iApply (ewp_EApp with "[] [] [Hmain Hpoints_to]"); last first.
      { iApply ("Hmain" $! (fun init => points_to γ (# init)) with "Hpoints_to"). }
      { Simp; by Ret. }
      { iApply ewp_EPath. by Ret. } }

    (* Finally, we prove the specification over handler. *)

    (* We need to abstract over the environment "just enough" *)

    remember (# init) eqn:Heqv; rewrite {1 2}Heqv; clear Heqv.
    (* Q. Better way to handle this? *)

    (* Löb induction *)
    iLöb as "IH" forall (γ main init).

    (* Prove that the spec is met. *)
    prove_handler_spec.

    (* -------------------------------------------------------------------------- *)
    { (* Outcome case *)
      iIntros (?) "H"; destruct o; [ | done]; iClear "IH"; iNext.

      red_match.

      iApply (ewp_EPair_ret _ _ _ _ (ieq a) with "[Hl]").

      (* Load from location *)
      { iApply (ewp_ELoad_simple with "[] Hl").
        iApply ewp_EPath. by Ret. }
      { iApply ewp_EPath. by Ret. }

      iIntros (??) "(%Hinit & Hl) %Heq"; subst.
      iExists (init, a); iFrame; encode. }

     (* -------------------------------------------------------------------------- *)
     (* Effectful case *)
     iIntros (e k) "Hp".
     iDestruct (upcl_sum_elim with "Hp") as "[ H_READ | H_WRITE ]".

     { (* READ case *)
       (* TODO: Notation on [iEff_car] is really ugly.. *)
       cbn; rewrite upcl_read.
       iDestruct "H_READ" as (x ->) "(Hx & H_READ)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %->.

       iNext. red_match.

       (* EWP Goal: [continue k (!var : t)]. *)
       iDestruct "H" as "(Hauth & Hx)".
       iSpecialize ("H_READ" with "Hx").
       iSpecialize ("H_READ" $! iEff_bottom (RET # v, Φ v.2))%I.

       iApply (ewp_EContinue _ _ _ _ (ieq ?[y1]) with "[] [Hl]");
         [ | | iIntros (?? ->) ].
       { rewrite /as_cont; iApply ewp_bind.
         iApply ewp_EPath. Ret. by Ret. }
       { iApply (ewp_ELoad_simple with "[] Hl").
         iApply ewp_EPath. by Ret. }

       iIntros "[-> Hl]".
       iSpecialize ("IH" with "Hauth Hl").
       iSpecialize ("H_READ" with "[IH]").
       { iNext. by rewrite /deep_handler_spec seal_eq. } (* FIXME: opacity control *)
       iApply "H_READ". }

    (* -------------------------------------------------------------------------- *)
     { (* WRITE case *)
       cbn; rewrite upcl_write.
       iDestruct "H_WRITE" as (??->) "(Hx & H_WRITE)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %Hag.

       (* Skip the return, exception, and [Get] branches. *)
       iNext. red_match.

       (* EWP Goal: [var := y; continue k ()]. *)
       iApply ewp_ESeq.

       (* EWP Subgoal: [var := y]. *)
       iApply (ewp_mono with "[Hl]").
       { iApply (ewp_EStore_simple).
         { iApply ewp_EPath; by Ret. }
         { iApply ewp_EPath. Ret. by iFrame. } }
       iIntros ([|]) "Hl"; simpl;
         [ iDestruct "Hl" as "[-> Hl]" | iDestruct "Hl" as "[]" ].

       (* EWP Subgoal: [continue k ()]. *)
       iDestruct "H" as "(Hauth & Hx)".

       iApply ewp_fupd.
       iDestruct (ghost_var_update γ (# y) with "Hauth Hx") as ">(Hauth & Hx)".
       iModIntro.

       iSpecialize ("H_WRITE" with "Hx").
       iSpecialize ("H_WRITE" $! iEff_bottom (RET # v, Φ v.2))%I.

       iApply (ewp_EContinue _ _ _ _ (ieq ?[y1]) (ieq ?[y2])); [| | iIntros (?? -> ->) ].
       { rewrite /as_cont; iApply ewp_bind.
         iApply ewp_EPath. Ret. by Ret. }
       { by iApply ewp_EConstant. }

       (* Resume the continuation. *)
       iApply "H_WRITE". iNext.
       rewrite /deep_handler_spec seal_eq.
       iApply ("IH" with "Hauth Hl"). }
   Qed.

End verification.
(* ========================================================================== *)

End localstate_example.
