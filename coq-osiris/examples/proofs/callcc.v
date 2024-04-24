From stdpp Require Import telescopes.

From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_callcc.

(* More experiments following Hazel. *)
(* ========================================================================== *)
(** * Specification. *)

Section protocol.
  Context `{!osirisGS Σ}.
  Context (callcc_eff : loc).
  Context A `{Encode A}.

  Definition callcc : val := VXData callcc_eff (VTuple []).
  Definition isCont (k : val) (Φ : val → iProp Σ) : iProp Σ :=
    □ ∀ (f : val), EWP (call f #()) {{ RET v, Φ v }} -∗ EWP (call k f) {{ RET _, True }}.

  (* IY: Here, the shot is of [OS] (multi-shot)... So is this trying to
        model [callcc] even relevant to our setting? *)
  Definition CALLCC_pre (CALLCC : iEff Σ): iEff Σ :=
    let CT := (CALLCC)%ieff in
    >> (t : A) Φ >> !(# t) {{ ∀ k, isCont k Φ -∗ ▷ EWP (call (# t) k) <| CT |> {{ RET v, Φ v }} }};
    << f   << ?(O2Ret f)   {{ ▷ EWP (call f #()) <| CT |> {{ lift_ret_spec Φ }} }} @ OS.

  Local Instance CALLCC_pre_contractive : Contractive CALLCC_pre.
  Proof.
    rewrite /CALLCC_pre => n CALLCC CALLCC' HI.
    repeat (apply iEffPre_base_ne ||
                rewrite iEffPost_base_eq || unfold iEffPost_base_def ||
                apply HI || f_contractive || f_equiv || intros =>?).
  Admitted.
  Definition CALLCC_def : iEff Σ := fixpoint (CALLCC_pre).
  Definition CALLCC_aux : seal CALLCC_def. Proof. by eexists. Qed.
  Definition CALLCC := CALLCC_aux.(unseal).
  Definition CALLCC_eq : CALLCC = CALLCC_def := CALLCC_aux.(seal_eq).
  Global Lemma CALLCC_unfold : CALLCC ≡ CALLCC_pre CALLCC.
  Proof. by rewrite CALLCC_eq /CALLCC_def;
          apply (fixpoint_unfold (CALLCC_pre)).
  Qed.

  (* The abstract protocol [CT]. *)
  Definition CT : iEff Σ := CALLCC.
  Arguments CT : simpl never.

  (* FIXME : The upcl on [OS] is not quite right... *)
  Lemma upcl_CALLCC v Φ' :
    iEff_car (upcl OS CALLCC) v Φ' ≡
      (∃ (t : A) Φ,
          ⌜ v = # t ⌝ ∗
          (∀ (k : val), isCont k Φ -∗ ▷ EWP call # t k <| CT |> {{ RET v, Φ v }}) ∗
          □ (∀ (f : val), ▷ EWP (call f #()) <| CT |> {{ RET v, Φ v }} -∗ Φ' (O2Ret f)))%I.
  Proof.
  Admitted.

Opaque encode.encode.

(* ========================================================================== *)
(** * Verification. *)

Section verification.

  Definition run := __fun1.

  Ltac prove_handler_spec := rewrite deep_handler_spec_unfold; iSplit.

  (* Local Ltacs from the WIP tactics on localstate. *)
  Local Ltac get_outcome_from_match e :=
    lazymatch e with
    | (pre_eval_match_aux _ _ _ ?o _ _) => constr:(o)
    | (deep_handler_body _ ?o _ _) => constr:(o)
    | (shallow_handler_body _ ?o _ _) => constr:(o)
    end.
  Local Ltac trivial_post_instantiation :=
      lazymatch goal with
      | |- envs_entails _ ?G =>
          lazymatch G with
          | ewp_def _ ?e _ _ =>
              lazymatch (get_outcome_from_match e) with
              | O3Ret _ => constr:(True)
              | O3Throw _ => constr:(True)
              | O3Perform _ _ => constr:(True \/ True)
              end
            end
        end.
  Local Ltac skip_matching_branch :=
    let φ2 := trivial_post_instantiation in
    iApply (handle_cons _ _ _ _ _ _ _ _ _ (λ _, False) φ2);
    [ specify_cpattern; pattern_match
    | iIntros (? [])
    | iIntros (_) ].
  Local Ltac skip_non_matching_branch :=
    iApply handle_cons_skip; [ reflexivity | ].
  Local Ltac skip_branch :=
    (skip_non_matching_branch || skip_matching_branch);
    fold deep_handler_body; fold shallow_handler_body.
  Local Ltac enter_branch :=
    iApply (handle_cons with "[-]");
    [ specify_cpattern; pattern_match; try (apply eq_refl)
    | (iIntros (? ->) || iIntros (? <-))
    | let F := fresh in iIntros (F); tauto ].

  Opaque deep_eval_match.

  Example callcc_run_spec Φ main :
    let env := [("Callcc", (VLoc callcc_eff))] ++ stdlib_env in
    EWP call main #() <| CT |> {{ RET v, Φ v }} -∗
    EWP call_anonfun env run [main] {{ RET v, Φ v }}.
  Proof.
    cbn.
    iIntros "Hmain". iApply ewp_fupd.

    (* -------------------------------------------------------------------------- *)
    (* 1. Symbolic execution.. TODO: automate this *)

    rewrite /call_anonfun /= /eval_anonfun /run.
    Bind; Simp; Ret; cbn. rewrite /__fun1.

    Simp.

    iApply (ewp_deep_handler with "[Hmain]").
    { (* 3A. Call to [main] in the handled expression *)
      iApply (ewp_EApp with "[] [] Hmain"); Simp; by Ret. }

    (* Finally, we prove the specification over handler. *)

    iModIntro.
    (* Löb induction *)
    iLöb as "IH" forall (main).

    (* Prove that the spec is met. *)
    prove_handler_spec.

    (* -------------------------------------------------------------------------- *)
    { (* Outcome case *)
      iIntros (?) "H"; destruct o; [ | try done]; iClear "IH"; iNext.
      (* Enter the return branch. *)
      enter_branch.

      (* FIXME : expr-level lemma about Data type *)
      Simp; with_strategy transparent [evals] unfold evals; Simp.

      by Ret. }

     (* -------------------------------------------------------------------------- *)
     (* Effectful case *)
     iIntros (e k) "Hp".
      rewrite /prot upcl_CALLCC.
      iDestruct "Hp" as (??->) "(Hp & #Hcall)".

       iNext.
       (* Skip return and exception branches. *)
       skip_branch. skip_branch.
       (* Enter [Get] branch. *)

      iApply (handle_cons with "[-]");
      [ specify_cpattern; pattern_match; try (apply eq_refl)
      | (iIntros (? ->) || iIntros (?))
      | let F := fresh in iIntros (F) ]. (* Something is fishy about this *)
    Admitted.

End protocol.
