From stdpp Require Import telescopes.

From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_localstate.

(* ========================================================================== *)
(** * Protocol. *)

Section localstate_example.

(* LATER: Make the type of state abstract (i.e. Encode .. ) *)
Definition state := Z.

Local Instance : Encode state := { encode := λ z, VInt (repr z) }.

Definition read rl : val := VXData rl [].
Definition write wl (v : state) : val := VXData wl [ # v].

Definition READ {Σ} rl (St : state -> _) : iEff Σ :=
  (>> x  >> ! (read rl) {{ St x }}; ? (O2Ret (# x)) {{ St x }} @ OS).
Definition WRITE {Σ} wl St : iEff Σ :=
  (>> x y >> ! (write wl y) {{ St x }}; ? (O2Ret VUnit) {{ St y }} @ OS).
Definition STATE {Σ} rl wl (St : state -> _) : iEff Σ := (READ rl St <+> WRITE wl St)%ieff.

Lemma upcl_state {Σ} rl wl St v Φ :
  iEff_car (upcl OS (STATE (Σ:=Σ) rl wl St)) v Φ ⊣⊢
    ((iEff_car (upcl OS (READ  rl St)) v Φ) ∨
     (iEff_car (upcl OS (WRITE wl St)) v Φ)).
Proof. by rewrite /STATE; apply upcl_sum. Qed.

Lemma upcl_read {Σ} rl St v Φ :
  iEff_car (upcl OS (READ (Σ:=Σ) rl St)) v Φ ⊣⊢
    (∃ x, ⌜ v = read rl ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (# x))))%I.
Proof. by rewrite /READ (upcl_tele' [tele _] [tele]). Qed.

Lemma upcl_write {Σ} wl St v Φ :
  iEff_car (upcl OS (WRITE (Σ:=Σ) wl St)) v Φ ⊣⊢
    (∃ x y, ⌜ v = write wl y ⌝ ∗ St x ∗ (St y -∗ Φ (O2Ret #())))%I.
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

  Lemma confront_addresses l1 l2 :
    ∀ v1 v2,
      (l1 ↦ v1) -∗
      (l2 ↦ v2) -∗
      ⌜address l1 ≠ address l2⌝.
  Proof.
    iIntros (v1 v2) "Hl1 Hl2".
    iPoseProof (gen_heap.pointsto_ne with "Hl1 Hl2") as "%Hne".
    iPureIntro. destruct l1, l2. simpl.
    intros ->. by apply Hne.
  Qed.

  Definition main_spec spec (t : unit) (m : microvx) :=
    (∀ (init : state) rl wl St,
        St init -∗
        EWP m <| STATE rl wl St |> {{ ensures v, spec v }} )%I.

  Definition run_spec (init : state) (main : val) (m : microvx) :=
    (∀ (spec : val -> iProp Σ),
       iSpec τ[unit] main (main_spec spec) -∗
       EWP m {{ ensures #v, spec (snd (v : state * val)) }})%I.

  (* EWP eval η (EAnonFun __fun7)
   {{ ensures v, iSpec τ[ val;val] v run_spec }} *)

  Lemma localstate_run_spec rl wl :
    ∀ η,
      ⌜ lookup_name η "Get" = ret (VLoc rl) ⌝ -∗
      ⌜ lookup_name η "Set" = ret (VLoc wl) ⌝ -∗
      ⌜ address rl ≠ address wl ⌝ -∗
      EWP eval η (EAnonFun __fun7)
        {{ ensures run, iSpec τ[ state;val] run run_spec }}.
  Proof.
    cbn zeta.
    iIntros (env HGet HSet Haddr).

    (* Call the anonymous function. *)
    iApply (ewp_eval_anon τ[ state; val ]); simpl.
    iIntros (init main); unfold run_spec.
    iIntros (spec) "Hspec".
    iApply ewp_please; iNext.
    iApply ewp_fupd.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]"; iModIntro.

    (* Evaluate allocation of [init] *)
    iApply (ewp_ELet_PVar_1 (fun x => val_points_to x (V (#init)))%I).

    (* Evaluating the let-bound expression *)
    { (* Allocate a new location with value [init] *)
      iApply ewp_ERef. { iApply ewp_EPath. iApply ewp_ret. done. }
      iIntros (? <- ?) "?".
      by iApply val_points_to_unfold. }

    (* Continuing with the rest of the computation *)

    iIntros (?) "H"; iDestruct "H" as (?->) "Hl".

    (* LATER : Hide the [V] constructor for blocks *)

    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] -- more interesting part of this proof. *)
    iApply ewp_EMatch.

    iApply (ewp_deep_handler with "[Hpoints_to Hspec]").
    {
      (* 3A. Call to [main] in the handled expression *)
      iApply (ewp_EApp τ[unit] with "[Hspec]").
      { simpl_eval. iApply ewp_ret. iApply "Hspec". }
      { simpl_eval. iApply ewp_ret. instantiate (1 := (λ x, ⌜x = tt⌝)%I).
        simpl. iExists tt; done. }
      simpl. iIntros (? -> m) "Hmain".
      unfold main_spec. simpl.
      iSpecialize ("Hmain" $! _ _ _ (fun init => points_to γ (# init))).
      iSpecialize ("Hmain" with "Hpoints_to").
      iApply (ewp_mono with "Hmain").
      iIntros ([|]); [ | iIntros ([])]; simpl.
      iIntros "Hspec".
      iExists a; iSplit. by rewrite <- (solve_encode_val a).
      iExact "Hspec". }

    (* Finally, we prove the specification over handler. *)

    (* We need to abstract over the environment "just enough" *)

    remember (# init) eqn:Heqv; rewrite {1 2}Heqv; clear Heqv.
    (* Q. Better way to handle this? *)

    (* Löb induction *)
    iLöb as "IH" forall (γ main init).

    (* Prove that the spec is met. *)
    iApply prove_deep_handler_spec; iIntros (ι); iSplit.

    (* -------------------------------------------------------------------------- *)
    { (* Outcome case *)
      iIntros (?) "H"; destruct o; [ | done]; iClear "IH"; iNext.
      next_branch. iIntros (η ->).
      iApply ewpi_ewp.
      iApply (ewp_EPair_ret _ _ _ _ (ieq a) with "[Hl]").

      (* Load from location *)
      { iApply (ewp_ELoad_simple with "[] Hl").
        iApply ewp_EPath. by iApply ewp_ret. }
      { iApply ewp_EPath. by iApply ewp_ret. }

      iIntros (??) "(%Hinit & Hl) %Heq"; subst.
      simpl. iDestruct "H" as "(%c & -> & HSpec)".
      iExists (init, c); iFrame; encode. }

     (* -------------------------------------------------------------------------- *)
     (* Effectful case *)
     iIntros (e k) "Hp". instantiate (1 := wl); instantiate (1 := rl).
     iDestruct (upcl_sum_elim with "Hp") as "[ H_READ | H_WRITE ]".

     { (* READ case *)
       cbn; rewrite upcl_read.
       iDestruct "H_READ" as (x ->) "(Hx & H_READ)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %->.

       iNext.
       next_branch. iIntros (? []).
       next_branch. iIntros (η ->).

       (* EWP Goal: [continue k (!var : t)]. *)
       iDestruct "H" as "(Hauth & Hx)".
       iSpecialize ("H_READ" with "Hx").
       iSpecialize ("H_READ" $! iEff_bottom (ensures #v, spec v.2))%I.
       iApply (ewpi_EContinue' _ _ _ _ _ _ (ieq ?[y1]) with "[] [Hl]");
         [ | | iIntros (?? ->) ].
       { iApply ewpi_EPath. iApply ewpi_ret. simpl.
         iExists k; iSplitL; iPureIntro; reflexivity. }
       { iApply (ewp_ELoad_simple with "[] Hl").
         iApply ewp_EPath. by iApply ewp_ret. }

       iIntros "[-> Hl]".
       iSpecialize ("IH" with "Hauth Hl").
       iSpecialize ("H_READ" with "[IH]").
       { iNext. rewrite /deep_handler_spec /deep_handler_spec' seal_eq. iApply "IH". }
       iApply "H_READ".

       (* Hard to guess that this is trivial. *) tauto. }

    (* -------------------------------------------------------------------------- *)
     { (* WRITE case *)
       cbn; rewrite upcl_write.
       iDestruct "H_WRITE" as (??->) "(Hx & H_WRITE)".
       iCombine "Hstate Hx" as "H".
       iDestruct (ghost_var_agree with "H") as %Hag.

       (* Skip the return, exception, and [Get] branches. *)
       iNext.
       next_branch. iIntros (? []).
       iApply ideep_handle_cons; [ | iSplit ].
       { iPureIntro. ltac2:(specify_cpattern ()).
         (* This causes a Match_failure, why?
         pattern_match. *)
         eapply pat_PXData_neq. simpl. eassumption.
         assumption. }
       iIntros (? []).
       iIntros "no_match2".
       next_branch. iIntros (η ->).

       { (* EWP Goal: [var := y; continue k ()]. *)
         iApply ewpi_ESeq.

         (* EWP Subgoal: [var := y]. *)
         iApply (ewpi_mono with "[Hl]").
         { iApply (ewpi_EStore_simple).
           { iApply ewpi_EPath; by iApply ewpi_ret. }
           { iApply ewpi_EPath. iApply ewpi_ret. by iFrame. } }
         iIntros_RET "[-> Hl]".

         (* EWP Subgoal: [continue k ()]. *)
         iDestruct "H" as "(Hauth & Hx)".

         iApply ewpi_fupd.
         iDestruct (ghost_var_update γ (# y) with "Hauth Hx") as ">(Hauth & Hx)".
         iModIntro.

         iSpecialize ("H_WRITE" with "Hx").
         iSpecialize ("H_WRITE" $! iEff_bottom (ensures #v, spec v.2))%I.

         iApply (ewpi_EContinue' _ _ _ _ _ _ (ieq ?[y1]) (ieq ?[y2])); [| | iIntros (?? -> ->) ].
         { iApply ewpi_EPath. iApply ewpi_ret.
           iExists _; iSplitL; iPureIntro; reflexivity. }
         { simpl_eval. by iApply ewpi_ret. }

         (* Resume the continuation. *)
         iApply "H_WRITE". iNext.
         rewrite /deep_handler_spec /deep_handler_spec' seal_eq.
         iApply ("IH" with "Hauth Hl"). }

       tauto.
       Unshelve. apply True. }
   Qed.

  Definition dummy_env := ("Effect", VStruct [("Deep", VStruct [])]) :: stdlib_env.

  Lemma module_proof (Q : val -> iProp Σ) :
    ⊢ EWP (eval_mexpr dummy_env __main)
      {{ ensures v, ∃ η, ⌜v = VStruct η⌝ ∧
                       ∃ run, ⌜lookup_name η "run" = ret run⌝ ∗
                              iSpec τ[state; val] run run_spec }}.
  Proof.
    iStartProof. rewrite /__main.
    iApply ewp_module.
    iApply (ewp_sitems_cons _ _ _ _ _ _ (ieq ?[φ])).

    (* [open Effect] *)
    { iApply (ewp_sitem_open _ _ _ _ _ _ (ieq ?[φ3])).
      { simpl_eval_mexpr. iApply ewp_ret. equality. }
      iIntros (δ' ->). equality. }

    (* [open Effect.Deep] *)
    iIntros (? ->).
    iApply (ewp_sitems_cons _ _ _ _ _ _ (ieq ?[φ])); [ | iIntros (? ->)].
    { iApply (ewp_sitem_open _ _ _ _ _ _ (ieq ?[φ2]));
        [ | iIntros (? ->); equality ].
      simpl_eval_mexpr. iApply ewp_ret. equality. }

    (* [type _ Effect.t += Get : t Effect.t] *)
    iApply ewp_sitems_extend.
    iIntros ([η δ]) "[%rl [-> Hrl]]"; clear η δ.

    (* [type _ Effect.t += Set : t -> unit Effect.t] *)
    iApply ewp_sitems_extend.
    iIntros ([η δ]) "[%wl [-> Hwl]]"; clear η δ.

    (* [let get () = perform Get] *)
    iApply (ewp_sitems_let_singleton_var
                (λ v,
                  □ ∀ St x,
                      St x -∗
                      EWP call v #()  <|STATE rl wl St|>
                        {{ ensures #X, ⌜X = x⌝ }})%I).
      { simpl_eval; iApply ewp_ret; simpl.
        iIntros "!>" (St x) "HSt".
        iApply ewp_call_nonrec. iNext.
        iApply ewp_EMatch.
        iApply ewp_deep_handler.
        { simpl_eval. iApply ewp_ret. instantiate (1 := (ensures #v, ⌜v = tt⌝)%I).
          iExists _. iSplit; equality. }
        iApply prove_deep_handler_spec; iIntros (ι); iSplit.
        { iIntros ([|]); [ | iIntros ([]) ].
          iIntros ((? & -> & ->)) "!>".
          iApply ideep_handle_cons.
          { iPureIntro. ltac2:(specify_cpattern ()).
            apply pat_PUnit. apply eq_refl.
            reflexivity. }
          iSplit.
          - iIntros (η <-).
            iApply (ewp_EPerform with "[] [HSt]").
            simpl_eval. iApply ewp_ret. instantiate (1 := (λ v, ⌜v = VXData rl []⌝)%I).
            equality.
            iIntros (? ->).
            iApply ewp_perform.
            rewrite /prot. rewrite upcl_state upcl_read.
            iLeft. iFrame.
            iSplit. equality. iIntros "HSt".
            simpl. iExists _; iSplit; equality.
          - iIntros ([]). }
        iIntros (??). instantiate (1 := ⊥).
        rewrite /prot upcl_bottom.
        iIntros ([]). }

    (* [let set y = perform (Set y)] *)
    iIntros ([η δ]) "[%get [-> get_spec]]"; clear η δ.
    iApply (ewp_sitems_let_singleton_var (λ v, □ ∀ St x y,
                           St x -∗
                             EWP call v #y  <|STATE rl wl St|>
                             {{ ensures _, St y }})%I ).
    { simpl_eval; iApply ewp_ret; simpl.
      iIntros "!>" (St x y) "HSt".
      iApply ewp_call_nonrec. iNext.
      iApply (ewp_EPerform _ _ _ _ (λ v, ⌜v = VXData wl [encode.encode y]⌝)%I).
      { simpl_eval. unfold widen. unfold try. simpl.
        iApply prove_ewp_Par.
        iApply ewp_ret. instantiate (1 := (λ v, ⌜v = #y⌝)%I). equality.
        iApply ewp_ret. instantiate (1 := (λ v, ⌜v = []⌝)%I). equality.
        iIntros (?? -> ->) "/=".
        iApply ewp_ret. equality. }
      iIntros (? ->).
      iApply ewp_perform.
      rewrite /prot. rewrite upcl_state upcl_write.
      iRight. iExists _, _. iFrame. iSplit. equality.
      by iIntros "Hsty". }

    (* [let run (type a) init maint : t * a =] *)
    iIntros ([η δ]) "[%set [-> set_spec]]"; clear η δ.
    iPoseProof (confront_addresses with "Hrl Hwl") as "%Haddr".
    iApply (ewp_sitems_let_singleton_var (λ run, iSpec τ[state; val] run run_spec)).
    { iApply localstate_run_spec; iPureIntro.
      reflexivity.
      reflexivity.
      apply Haddr. }

    iIntros ([η δ]) "[%run [-> Hrun]]".
    iApply ewp_sitems_nil; simpl.

    (* Establish postcondition. *)
    iExists _; iSplit; [ equality | ].
    iExists _; iSplit; [ equality | ].
    iApply "Hrun".
  Qed.

End verification.

End localstate_example.
