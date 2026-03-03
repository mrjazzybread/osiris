From stdpp Require Import telescopes.

From iris.proofmode Require Import base ltac_tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_localstate.

(* ========================================================================== *)
(** * Protocol. *)

(* LATER: Make the type of state abstract (i.e. Encode .. ) *)
Definition state := Z.

Local Instance : Encode state := { encode := λ z, VInt (repr z) }.

Section protocols.

  Context (rl wl : loc).

  Definition read : val := VXData rl [].
  Definition write (v : state) : val := VXData wl [ # v].

  Definition READ {Σ} (St : state -> _) : iEff Σ :=
    (>> x  >> ! (read) {{ St x }}; ? (O2Ret (# x)) {{ St x }}).
  Definition WRITE {Σ} St : iEff Σ :=
    (>> x y >> ! (write y) {{ St x }}; ? (O2Ret VUnit) {{ St y }}).
  Definition STATE {Σ} (St : state -> _) : iEff Σ := (READ St <+> WRITE St)%ieff.

  Lemma upcl_state {Σ} St v Φ :
    STATE (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (READ St allows perform v << Φ >>) ∨
      (WRITE St allows perform v << Φ >>).
  Proof. by rewrite /STATE; apply upcl_sum. Qed.

  Lemma upcl_read {Σ} St v Φ :
    READ (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (∃ x, ⌜ v = read ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (# x))))%I.
  Proof. by rewrite /READ /prot (upcl_tele' [tele _] [tele]). Qed.

  Lemma upcl_write {Σ} St v Φ :
    WRITE (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (∃ x y, ⌜ v = write y ⌝ ∗ St x ∗ (St y -∗ Φ (O2Ret #())))%I.
  Proof. by rewrite /WRITE /prot (upcl_tele' [tele _ _] [tele]). Qed.

End protocols.

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

(* LATER: Give more control on opacity *)
Opaque auth_state.
Opaque encode.encode.

(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!osirisGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Section alloc_effects.

  Context (rl wl : loc).

  Inductive effects : Type :=
  | Read
  | Write (y : Z).

  Local Instance encode_effects : Encode effects :=
    { encode eff := match eff with
                    | Read => VXData rl []
                    | Write y => VXData wl [ #y ]
                    end }.

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

  Definition main_spec `{Encode A} (spec : A → iProp Σ) (t : unit) (m : microvx) :=
    (∀ (init : state) rl wl St,
        St init -∗
        imp m <| STATE rl wl St |> {{ spec }} )%I.

  Definition run_spec (init : state) (main : val) (m : microvx) :=
    (∀ (A : Type) (_ : Encode A) (spec : A → iProp Σ),
       iSpec τ[unit] main (main_spec spec) -∗
       imp m {{ λ (v : state * A), spec (snd v) }})%I.

  Lemma localstate_run_spec :
    ∀ η,
      ⌜ lookup_name η "Get" = Some #rl ⌝ -∗
      ⌜ lookup_name η "Set" = Some #wl ⌝ -∗
      ⌜ address rl ≠ address wl ⌝ -∗
      imp eval η (EAnonFun __fun7)
        {{ λ run,  □ iSpec τ[ state;val] run run_spec }}.
  Proof.
    cbn zeta.
    iIntros (env HGet HSet Haddr).

    (* Call the anonymous function. *)
    iApply (imp_EAnon_pers τ[ state; val ]); simpl.
    iIntros "!>" (init main A HencA spec) "Hspec".
    iApply imp_please; iNext.
    iApply imp_fupd.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]"; iModIntro.

    (* Evaluate allocation of [init] *)
    iApply (imp_ELet_var (λ l, l ↦ #init)%I).

    (* Evaluating the let-bound expression *)
    { (* Allocate a new location with value [init] *)
      iApply imp_ERef. imp_path. }

    (* Continuing with the rest of the computation *)
    iIntros (l) "Hl".

    (* LATER : Hide the [V] constructor for blocks *)

    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] -- more interesting part of this proof. *)
    iApply (imp_EHandler (A':=A) with "[Hspec Hpoints_to]").

    { (* 3A. Call to [main] in the handled expression *)
      iApply (imp_EApp τ[unit] with "[Hspec]").
      { imp_path. }
      { iApply imp_EConstant. encode.
        by instantiate (1 := (λ x, ⌜x = tt⌝)%I). }
      simpl. iIntros (? -> m) "Hmain".
      rewrite /main_spec /=.
      iSpecialize ("Hmain" $! _ _ _ (λ init, points_to γ #init) with "Hpoints_to").
      iApply "Hmain". }

    generalize (# init) at 3 as init_; intros init_.
    iLöb as "IH" forall (init).
    iApply prove_deep_handler_spec.
    iSplit; last (iSplit; first iIntros (? [])).

    { (* Value case *)
      iIntros (?) "Hspec"; iNext.
      iApply deep_handle_cons. iPureIntro. ltac2:(let _ := specify_cpattern () in ()). pattern_match.
      iSplit; last iIntros ([]).
      iIntros (? ->).
      iApply (imp_EPair with "[Hl]").
      { iApply (imp_ELoad with "Hl"). imp_path. }
      { imp_path. }
      iIntros (? ?) "(-> & Hl) ->". iApply "Hspec". }
    (* Finally, we prove the specification over handler. *)

    instantiate (1 := wl). instantiate (1 := rl).
    (* -------------------------------------------------------------------------- *)
    (* Effectful case *)
    iIntros (v k) "Hp".
    iDestruct (upcl_state with "Hp") as "[ H_READ | H_WRITE ]".

    { (* READ case *)
      rewrite upcl_read.
      iDestruct "H_READ" as (x ->) "(Hx & H_READ)".
      iCombine "Hstate Hx" as "H".
      iDestruct (ghost_var_agree with "H") as %->.

      iNext.
      iApply deep_handle_cons. iPureIntro. ltac2:(let _ := specify_cpattern () in ()).
      iSplit; [ iIntros (? []) | iIntros (_) ].
      iApply deep_handle_cons.
      { iPureIntro. ltac2:(let _ := specify_cpattern () in ()). pattern_match. }
      iSplit ; [ iIntros (? ->) | iIntros ([[] | []]) ].

      (* EWP Goal: [continue k (!var : t)]. *)
      iDestruct "H" as "(Hauth & Hx)".
      iSpecialize ("H_READ" with "Hx"). simpl.
      fold eval.
      iApply (imp_EContinue (B:=state) with "[] [Hl]").
      { imp_path. }
      { iApply (imp_ELoad with "Hl"). imp_path. }

      iIntros (? ? ->) "[-> Hl]".
      iApply "H_READ". iApply ("IH" with "Hauth Hl"). }

    (* -------------------------------------------------------------------------- *)
    { (* WRITE case *)
      cbn; rewrite upcl_write.
      iDestruct "H_WRITE" as (??->) "(Hx & H_WRITE)".
      iCombine "Hstate Hx" as "H".
      iDestruct (ghost_var_agree with "H") as %Hag.

      (* Skip the return, exception, and [Get] branches. *)
      iNext.
      iApply deep_handle_cons. iPureIntro. ltac2:(let _ := specify_cpattern () in ()).
      iSplit; first iIntros (? []).
      iIntros (_).
      iApply deep_handle_cons.
      { iPureIntro. ltac2:(let _ := specify_cpattern () in ()).
        (* This causes a Match_failure, why?
           pattern_match. *)
        eapply pat_PXData_neq. simpl. eassumption.
        assumption. }
      iSplit; first iIntros (? []).
      instantiate (1 := False). iIntros "%no_match2".
      iApply deep_handle_cons. iPureIntro. ltac2:(let _ := specify_cpattern () in ()). pattern_match.
      iSplit; [ iIntros (? ->) | iIntros "%Hf"; tauto ].
      { (* EWP Goal: [var := y; continue k ()]. *)
        iApply (imp_ESeq with "[Hl]").

        { (* EWP Subgoal: [var := y]. *)
          iApply (imp_EStore (A:=state) with "Hl").
          { imp_path. }
          { imp_path. } }

        iIntros "Hl".

        (* EWP Subgoal: [continue k ()]. *)
        iDestruct "H" as "(Hauth & Hx)".

        iApply imp_fupd.
        iDestruct (ghost_var_update γ (# y) with "Hauth Hx") as ">(Hauth & Hx)".
        iModIntro.

        iApply (imp_EContinue (B:=unit)).
        { imp_path. }
        { instantiate (1 := (λ u, ⌜u = tt⌝)%I).
          iApply imp_EConstant; auto; encode. }
        iIntros (??) "-> -> !>".
        iApply ("H_WRITE" with "Hx").
        iApply ("IH" with "Hauth Hl"). } }
  Qed.

  End alloc_effects.

  Definition dummy_env := ("Effect", VStruct [("Deep", VStruct [])]) :: stdlib_env.

  Lemma module_proof (Q : val -> iProp Σ) :
    ⊢ imp (eval_mexpr dummy_env __main)
      {{ λ η, ∃ run, ⌜lookup_name η "run" = Some run⌝ ∗
                     □ iSpec τ[state; val] run run_spec }}.
  Proof.
    iApply imp_module.
    iApply (imp_sitems_cons).

    (* [open Effect] *)
    { iApply (imp_sitem_open).
      { simpl_eval_mexpr.
        iApply imp_ret; first encode.
        instantiate (1 := (λ δ, ⌜δ = [_]⌝)%I). done. }
      iIntros (? ->) "/=".
      instantiate (1 := (λ η, ⌜η = (_, _)⌝)%I). done. }
    iIntros (? ->).

    (* [open Effect.Deep] *)
    iApply imp_sitems_cons.
    { iApply (imp_sitem_open).
      { simpl_eval_mexpr.
        iApply imp_ret; first encode.
        instantiate (1 := (λ δ, ⌜δ = []⌝)%I). done. }
      iIntros (? ->) "/=".
      instantiate (1 := (λ η, ⌜η = (_, _)⌝)%I). done. }
    iIntros (? ->).

    (* [type _ Effect.t += Get : t Effect.t] *)
    iApply imp_sitems_extend.
    iIntros (rl) "Hrl".

    (* [type _ Effect.t += Set : t -> unit Effect.t] *)
    iApply imp_sitems_extend.
    iIntros (wl) "Hwl".

    set enc_eff := encode_effects rl wl.

    (* [let get () = perform Get] *)
    iApply (imp_sitems_let (λ v, □ iSpec τ[unit] v (λ _ m,
                                                      ∀ St x,
                                                      St x -∗
                                                      imp m <|STATE rl wl St|> {{ λ X, ⌜X = x⌝ }}))%I ).
    { iApply (imp_EAnon_pers τ[unit]).
      iIntros "!>" ([] St x) "HSt".
      iApply imp_please. iNext.
      iApply (imp_EMatch (A':=unit)).
      { imp_path. }
      iIntros (? ->) "!>".
      iApply deep_handle_cons.
      { iPureIntro. ltac2:(let _ := specify_cpattern () in ()). pattern_match.
        apply eq_refl. }
      iSplit; last iIntros ([]).
      iIntros (? <-).
      iApply (imp_EPerform (B:=effects) with "[] [HSt]").
      { simpl_eval. instantiate (1 := (λ eff, ⌜eff = Read⌝)%I).
        iApply imp_ret; last done. encode. }
      iIntros (? ->).
      rewrite upcl_state.
      iLeft. rewrite upcl_read. iFrame. iSplit.
      - equality.
      - iIntros "HSt".
        simpl. iExists _; iSplit; equality. }
    iIntros (get) "#Hget".

    (* [let set y = perform (Set y)] *)
    iApply (imp_sitems_let (λ v, □ iSpec τ[Z] v (λ y m,
                                                   ∀ St x,
                                                   St x -∗
                                                   imp m <|STATE rl wl St|> {{ λ (_ : unit), St y }}))%I).
    { iApply (imp_EAnon_pers τ[Z]).
      iIntros "!>" (y St x) "HSt".
      iApply imp_please; iNext.
      iApply (imp_EPerform (λ eff, ⌜eff = Write y⌝)%I).
      { iApply imp_EXData. reflexivity.
        instantiate (1 := ([(λ x, ⌜x = #y⌝)])%I).
        simpl; fold eval; iSplit; last done.
        imp_path.
        iIntros (?) "Hvs".
        iPoseProof (big_sepL2_length with "Hvs") as "%Hlen".
        destruct vs; first discriminate; destruct vs; last discriminate.
        simpl; iDestruct "Hvs" as "[-> _]". iExists _; iSplit; equality.
        iPureIntro. encode. }
      iIntros (? ->).
      rewrite upcl_state upcl_write.
      iRight. iExists x, y. iFrame. iSplit.
      - iPureIntro. encode.
      - iIntros "$". iExists _; auto. }
    iIntros (fset) "#Hset".

    (* [let run (type a) init maint : t * a =] *)
    iPoseProof (confront_addresses with "Hrl Hwl") as "%Haddr".
    iApply (imp_sitems_let (λ run, □ iSpec τ[state; val] run run_spec)%I).
    { iApply (localstate_run_spec with "[] [] []"); iPureIntro.
      reflexivity.
      reflexivity.
      apply Haddr. }

    iIntros (run) "#Hrun".
    iApply imp_sitems_nil; simpl.
    iExists _; iFrame "#". equality.
  Qed.

End verification.
