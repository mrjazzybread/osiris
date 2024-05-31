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

Definition read rl : val := VXData rl (VTuple []).
Definition write wl (v : state) : val := VXData wl (VTuple [ # v]).

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

  Lemma confront_addresses l1 l2 :
    ∀ v1 v2,
      (l1 ↦ v1) -∗
      (l2 ↦ v2) -∗
      ⌜address l1 ≠ address l2⌝.
  Proof.
    iIntros (v1 v2) "Hl1 Hl2".
    iPoseProof (gen_heap.mapsto_ne with "Hl1 Hl2") as "%Hne".
    iPureIntro. destruct l1, l2. simpl.
    intros ->. by apply Hne.
  Qed.

  Definition run_env_requirements η rl wl :=
    (rl ↦ V #() ∗
     wl ↦ V #() ∗
     ⌜ lookup_name η "Get" = ret (VLoc rl) ⌝ ∗
     ⌜ lookup_name η "Set" = ret (VLoc wl) ⌝)%I.

  Definition main_spec main init rl wl spec :=
    (∀ St,
        St init -∗
        EWP call main #() <| STATE rl wl St |> {{ RET v, spec v }} )%I.

  Definition run_spec rl wl run :=
    (∀ (* η *) (spec : val -> iProp Σ) init main,
       (* run_env_requirements η rl wl -∗ *)
       main_spec main init rl wl spec -∗
       EWP c ← (call run #init);
           call c main {{ RET #v, spec (snd (v : state * val)) }})%I.

  Lemma localstate_run_spec rl wl :
    ∀ η (Φ : val -> iProp Σ) init main,
      ⌜ lookup_name η "Get" = ret (VLoc rl) ⌝ -∗
      ⌜ lookup_name η "Set" = ret (VLoc wl) ⌝ -∗
      ⌜ address rl ≠ address wl ⌝ -∗
      (∀ St,
          St init -∗
          EWP call main #() <| STATE rl wl St |> {{ RET v, Φ v }} ) -∗
      EWP call_anonfun η run [ #init ; main]
        {{ RET # v, Φ (snd (v : state * val)) }}.
  Proof.
    cbn zeta.
    iIntros (env Φ init main HGet HSet Haddr) "Hmain".
    iApply ewp_fupd.
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

  Definition dummy_env := ("Effect", VStruct [("Deep", VStruct [])]) :: stdlib_env.

  Lemma ewp_mexpr_MStruct η sitems E ψ Q :
    EWP eval_sitems (η, []) sitems @ E <| ψ |> {{ RET ηδ, let '(_, δ) := ηδ in Q (O2Ret (VStruct δ)) }} -∗
    EWP (eval_mexpr η (MStruct sitems)) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitems".
    with_strategy transparent [eval_mexpr] simpl. Bind.
    iApply (ewp_mono with "Hsitems").
    iIntros ([ηδ|]); [ simpl; iIntros "HQ" | done ].
    destruct ηδ; by iApply ewp_value.
  Qed.

  Lemma ewp_sitem_open η δ me E ψ Q φ δ' :
    EWP eval_mexpr η me @ E <| ψ |> {{ RET v, ⌜ v = VStruct δ' ⌝ ∗ φ δ' }} -∗
    ( ∀ δ', φ δ' -∗ Q (O2Ret (δ' ++ η, δ)) ) -∗
    EWP eval_sitem (η, δ) (IOpen me) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hme Hcov".
    with_strategy transparent [eval_sitem] simpl. Bind. Bind.
    iApply (ewp_mono with "Hme").
    iIntros ([|]); [ simpl | done ].
    iIntros "[-> Hφ]".
    iApply ewp_try. Ret.
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma ewp_sitem_extend η δ es E ψ (Q : env * env -> iProp Σ) :
    EWP eval_type_extensions es @ E <| ψ |>
      {{ RET δ', Q (δ' ++ η, δ' ++ δ) }} -∗
    EWP eval_sitem (η, δ) (IExtend es) @ E <| ψ |> {{ RET v, Q v }}.
  Proof.
    iIntros "Hes".
    with_strategy transparent [eval_sitem] Simp.
    Bind. iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl; by iIntros "HQ" | done ].
  Qed.

  Lemma ewp_type_extension_cons e es E ψ Q :
    ▷ (∀ l, l ↦ V #() -∗
          EWP eval_type_extensions es @ E <| ψ |>
            {{ RET δ, Q (O2Ret ((e, VLoc l) :: δ)) }}) -∗
    EWP eval_type_extensions (e :: es) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hes". simpl.
    iApply ewp_alloc.
    iModIntro.
    iIntros "%l Hl".
    rewrite /continue; simpl. Bind.
    iSpecialize ("Hes" with "Hl").
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl | done ]; iIntros "HQ".
    by iApply ewp_value.
  Qed.

  Lemma ewp_type_extension_nil E ψ Q :
    Q (O2Ret []) -∗
    EWP eval_type_extensions [] @ E <| ψ |> {{ Q }}.
  Proof. iIntros "HQ". simpl. by iApply ewp_value. Qed.

  Lemma ewp_sitems_nil ηδ E ψ Q :
    Q (O2Ret ηδ) -∗
    EWP eval_sitems ηδ [] @ E <| ψ |> {{ Q }}.
  Proof.
    with_strategy transparent [eval_sitems] simpl.
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitems_cons ηδ sitem sitems E ψ Q (φ : env * env -> iProp Σ) :
    EWP eval_sitem ηδ sitem @ E <| ψ |> {{ RET ηδ, φ ηδ }} -∗
    (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| ψ |> {{ Q }}) -∗
    EWP eval_sitems ηδ (sitem :: sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    with_strategy transparent [eval_sitems] simpl. Bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

  Lemma ewp_sitem_let_singleton_var (spec : val -> iProp Σ) η δ x e E ψ Q :
    EWP eval η e @ E <| ψ |> {{ RET v, spec v }} -∗
    (∀ v, spec v -∗ Q (O2Ret ((x, v) :: η, (x, v) :: δ))) -∗
    EWP eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "He HQ".
    with_strategy transparent [eval_sitem eval_bindings] simpl.
    Par. Bind.
    iApply (ewp_mono with "He").
    iIntros ([|]); [ simpl | done ].
    iIntros "Hspec".
    with_strategy transparent [extend] simpl; Ret.
    by iApply "HQ".
  Qed.

  Lemma lemmaname (Q : val -> iProp Σ) :
    ⊢ EWP (eval_mexpr dummy_env __main)
      {{ RET v, ∃ η, ⌜v = VStruct η⌝ ∧
                       ∃ run, ⌜lookup_name η "run" = ret run⌝ ∗
                              ∃ rl wl, run_spec rl wl run }}.
  Proof.
    iIntros. rewrite /__main.
    iApply ewp_mexpr_MStruct.
    iApply (ewp_sitems_cons _ _ _ _ _ _ (ieq ?[φ])).

    (* [open Effect] *)
    { iApply (ewp_sitem_open _ _ _ _ _ _ (ieq ?[φ3])).
      { with_strategy transparent [eval_mexpr] Simp. Ret. simpl.
        equality. }
      iIntros (δ' ->). equality. }

    (* [open Effect.Deep] *)
    iIntros (? ->).
    iApply (ewp_sitems_cons _ _ _ _ _ _ (ieq ?[φ])); [ | iIntros (? ->)].
    { iApply (ewp_sitem_open _ _ _ _ _ _ (ieq ?[φ2]));
        [ | iIntros (? ->); equality ].
      with_strategy transparent [eval_mexpr] Simp. Ret. simpl.
      equality. }

    (* [type _ Effect.t += Get : t Effect.t] *)
    iApply ewp_sitems_cons.
    { iApply (ewp_sitem_extend _ _ _ _ _
                (fun (ηδ : env * env) => ∃ l,
                     ⌜ ηδ = (("Get", VLoc l) :: ("Deep", VStruct []) :: dummy_env,
                              [("Get", VLoc l)]) ⌝
                              ∗ l ↦ V #())%I).
      iApply ewp_type_extension_cons.
      iIntros "!> %rl Hrl".
      iApply ewp_type_extension_nil.
      iExists rl; iFrame; equality. }

    (* [type _ Effect.t += Set : t -> unit Effect.t] *)
    iIntros ([η δ]) "[%rl [-> Hrl]]"; clear η δ.
    iApply ewp_sitems_cons.
    { iApply (ewp_sitem_extend _ _ _ _ _
                (fun (ηδ : env * env) => ∃ l',
                     ⌜ ηδ = (("Set", VLoc l') ::
                               ("Get", VLoc rl) ::
                               ("Deep", VStruct []) ::
                               dummy_env,
                              [("Set", VLoc l'); ("Get", VLoc rl)]) ⌝
                   ∗ l' ↦ V #())%I).
      iApply ewp_type_extension_cons.
      iIntros "!> %wl Hwl".
      iApply ewp_type_extension_nil.
      iExists wl; iFrame; equality. }

    (* [let get () = perform Get] *)
    iIntros ([η δ]) "[%wl [-> Hwl]]"; clear η δ.
    iApply (ewp_sitems_cons _ _ _ _ _ _ (λ ηδ,
                ∃ v, ⌜ ηδ =
                       (("get", v) ::
                         ("Set", VLoc wl) ::
                         ("Get", VLoc rl) ::
                         ("Deep", VStruct []) :: dummy_env,
                       [("get", v); ("Set", VLoc wl); ("Get", VLoc rl)]) ⌝ ∗
                  □ ∀ St x,
                      St x -∗
                      EWP call v #()  <|STATE rl wl St|>
                        {{ RET #X, ⌜X = x⌝ }})%I ).
    { iApply (ewp_sitem_let_singleton_var
                (λ v,
                  □ ∀ St x,
                      St x -∗
                      EWP call v #()  <|STATE rl wl St|>
                        {{ RET #X, ⌜X = x⌝ }})%I).
      { Simp; Ret; simpl.
        iIntros "!>" (St x) "HSt".
        iApply ewp_call_nonrec. iNext. Simp. rewrite /continue.
        (* TODO: there must be a better way. *)
        Local Transparent eval_match.
        rewrite /deep_eval_match /eval_match.
        Local Opaque eval_match.
        red_match.
        with_strategy transparent [evals] Simp.
        iApply ewp_perform.
        rewrite /prot. rewrite upcl_state upcl_read.
        iLeft. iExists _. iFrame. iSplit. equality.
        iIntros "_". iExists _; iSplit; equality. }

      { iIntros (get) "get_spec".
        iExists get. iSplit; [ equality | ]. iApply "get_spec". } }


    (* [let set y = perform (Set y)] *)
    iIntros ([η δ]) "[%get [-> get_spec]]"; clear η δ.
    iApply (ewp_sitems_cons _ _ _ _ _ _ (λ ηδ,
                ∃ v, ⌜ ηδ =
                       (("set", v) ::
                          ("get", get) ::
                          ("Set", VLoc wl) ::
                          ("Get", VLoc rl) ::
                          ("Deep", VStruct []) :: dummy_env,
                         [("set", v); ("get", get); ("Set", VLoc wl); ("Get", VLoc rl)]) ⌝ ∗
                         □ ∀ St x y,
                           St x -∗
                             EWP call v #y  <|STATE rl wl St|>
                             {{ RET _, St y }})%I ).
    { iApply (ewp_sitem_let_singleton_var
                (λ v,
                  □ ∀ St x y,
                      St x -∗
                      EWP call v #y  <|STATE rl wl St|>
                      {{ RET _, St y }})%I).
      { Simp; Ret; simpl.
        iIntros "!>" (St x y) "HSt".
        iApply ewp_call_nonrec. iNext.
        with_strategy transparent [evals] Simp.
        iApply ewp_perform.
        rewrite /prot. rewrite upcl_state upcl_write.
        iRight. iExists _, _. iFrame. iSplit. equality.
        by iIntros "Hsty". }

      { iIntros (set) "set_spec".
        iExists set. iSplit; [ equality | done ]. } }


    (* [let run (type a) init maint : t * a =] *)
    iIntros ([η δ]) "[%set [-> set_spec]]"; clear η δ.
    iPoseProof (confront_addresses with "Hrl Hwl") as "%Haddr".
    iApply (ewp_sitems_cons _ _ _ _ _ _ (λ ηδ,
                ∃ v, ⌜ ηδ = ?[H1] v ⌝ ∗ run_spec rl wl v)%I).
    { iApply (ewp_sitem_let_singleton_var (run_spec rl wl)).
      { Simp. Ret. simpl. unfold run_spec.
        iIntros (spec init main) "Hmain".
        iPoseProof (localstate_run_spec rl wl) as "Hrunspec".
        rewrite /call_anonfun. simpl. rewrite /eval_anonfun. rewrite eval_eval'; simpl.
        fold run.
        iApply ("Hrunspec" with "[] [] [] Hmain"); try by equality. }

      iIntros (run) "Hrun". simpl.
      iExists run. iFrame. iPureIntro.
      Unshelve.
      2: exact (λ v : val,
     ("run" ~> v;
      ("set", set)
      :: ("get", get)
         :: ("Set", VLoc wl) :: ("Get", VLoc rl) :: ("Deep", VStruct []) :: dummy_env,
      "run" ~> v;
      [("set", set); ("get", get); ("Set", VLoc wl); ("Get", VLoc rl)])).
      reflexivity. }

    iIntros ([η δ]) "[%run [-> Hrun]]".
    iApply ewp_sitems_nil; simpl.

    (* Establish postcondition. *)
    iExists _; iSplit; [ equality | ].
    iExists _; iSplit; [ equality | ].
    iExists _, _; iApply "Hrun".
  Qed.

End verification.

End localstate_example.
