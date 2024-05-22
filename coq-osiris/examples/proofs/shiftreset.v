From stdpp Require Import telescopes.
From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_shiftreset localstate.

(* Reasoning about delimited control via [shift/reset].

   Note: Sanity check example following [Hazel] [shift_reset] example and
         specification. *)

(* ========================================================================== *)
(** * Protocol. *)

(* Location for the shift eff *)
Context (shift_eff : loc).

(* ------------------------------------------------------------------------ *)
(** Shift Protocol. *)

Section shift_protocol.
  Context `{!osirisGS Σ}.

  Definition shift h : val := VXData shift_eff (VTuple [h]).

  Definition is_shift
    (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) (h : val) : iProp Σ :=
    ∀ k,
      (∀ w, Q w -∗ EWP (stop CResume (k, O2Ret w)) <| Ψ |> {{ Φ ↑ }}) -∗
        ▷ EWP call h (VCont k) <| Ψ |> {{ Φ ↑ }}.

  (* Note that this specification is different from in [Hazel]; there is
    no recursive reference within the specification itself. *)

  Definition SHIFT :
    (iEffO -d> (val -d> iPropO Σ) -d> iEffO) := λ Ψ Φ,
    (>> h Q >> !(shift h) {{ is_shift Ψ Φ Q h }};
      << w   << ?(w) {{ Q ↑ w }} @ OS)%ieff.

  Lemma upcl_SHIFT Ψ Φ v Φ' :
    iEff_car (upcl OS (SHIFT Ψ Φ)) v Φ' ≡
      (∃ t Q,
          ⌜v = shift t ⌝ ∗ is_shift Ψ Φ Q t ∗
          (∀ w, Q ↑ w -∗ Φ' w))%I.
  Proof.
    transitivity (iEff_car (upcl OS (SHIFT Ψ Φ)) v Φ').
    - by iApply iEff_car_proper.
    - by rewrite /SHIFT (upcl_tele' [tele _ _] [tele _]).
  Qed.

End shift_protocol.

(* ------------------------------------------------------------------------ *)
(** Reasoning Rules. *)

Section reasoning_rules.
  Context `{!osirisGS Σ}.

  Definition env := ("Shift", (VLoc shift_eff)) :: stdlib_env.

  (* Mapping of translated function declaration names *)
  Definition shift_f := __fun0.
  Definition reset_f := __fun2.

  Definition Shift b e := (call_anonfun env shift_f [VClo env (AnonFun b e)]).
  Definition Reset e :=
    (call_anonfun env reset_f [VClo env (AnonFun "" e)]).

  Definition reset_spec e (Ψ : iEff Σ) Φ : Prop :=
    (* Note: the environment is manually extended with a unit value;
     LATER: Use [__osiris_anonymous_arg] where [eval] explicitly ignores the
     anonymous_arg keyword. *)
    ⊢ EWP eval ("" ~> VUnit; env) e <|SHIFT Ψ Φ|> {{Φ ↑}} -∗
        EWP Reset e <|Ψ|> {{Φ ↑}}.

  Definition shift_spec
    b e (Ψ : iEff Σ) (Φ Q : val → iProp Σ) : Prop :=
    ⊢ is_shift Ψ Φ Q (VClo env (AnonFun b e)) -∗
        EWP Shift b e <|SHIFT Ψ Φ|> {{Q ↑}}.

End reasoning_rules.

(* ------------------------------------------------------------------------ *)
(** Verification. *)

Opaque eval_match. (* TODO: Move *)

(* [ewp_call_anonfun] expects a goal of the form
          [ EWP call_anonfun η (λ args, body) (args ++ [x]) {{ Q }} ]
      and produces a goal of the form
          [ EWP call (VClo (args ++ η) body) x {{ Q }} ] *)
  Ltac ewp_call_anonfun :=
    (* Unfold [call_anonfun], and get a tower of binds. *)
    rewrite /call_anonfun; simpl; rewrite ?bind_bind;
    (* Unfold [eval_anonfun]. *)
    rewrite /eval_anonfun;
    (* Simplify the tower of binds,
        this should elaborate a closure capturing all arguments.  *)
    repeat (iApply ewp_bind; Simp; Ret);
    simpl.

  (* Non-recursive call. *)
  Ltac Call :=
    match goal with
    | |- envs_entails _ (ewp_def _ (call_anonfun _ _ _) _ _) =>
          ewp_call_anonfun; iApply ewp_call_nonrec
    end.

   Ltac get_outcome_from_match e :=
    lazymatch e with
    | (pre_eval_match_aux _ _ _ ?o _ _) => constr:(o)
    | (deep_handler_body _ ?o _ _) => constr:(o)
    | (shallow_handler_body _ ?o _ _) => constr:(o)
    end.
  Ltac trivial_post_instantiation :=
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
  Ltac skip_matching_branch :=
    let φ2 := trivial_post_instantiation in
    iApply (handle_cons _ _ _ _ _ _ _ _ _ (λ _, False) φ2);
    [ specify_cpattern; pattern_match
    | iIntros (? [])
    | iIntros (_) ].
  Ltac skip_non_matching_branch :=
    iApply handle_cons_skip; [ reflexivity | ].
  Ltac skip_branch :=
    (skip_non_matching_branch || skip_matching_branch);
    fold deep_handler_body; fold shallow_handler_body.
  Ltac enter_branch :=
    iApply (handle_cons with "[-]");
    [ specify_cpattern; pattern_match; try (apply eq_refl)
    | (iIntros (? ->) || iIntros (? <-))
    | let F := fresh in iIntros (F); tauto ].

  (* Try to reduce a [match] expression by skipping all branches seen and then
     entering a branch on match. *)
  Ltac red_match := repeat (skip_branch; [ idtac ]); enter_branch.

Section verification.
  Context `{!osirisGS Σ}.

  Lemma ewp_reset e Ψ Φ : reset_spec e Ψ Φ.
  Proof.
    iIntros "He". unfold Reset.

    Call. Simp. iNext.

    iApply (ewp_deep_handler _ (SHIFT Ψ Φ) (Φ ↑) with "[He]").
    { by Simp. }

    iLöb as "IH".
    rewrite {2}deep_handler_spec_unfold; iSplit.
    { iIntros (?) "H". destruct o; try done.
      iNext. iClear "IH".
      red_match.
      iApply ewp_EPath. by Ret. }

    iIntros (v k) "Hprot"; rewrite /prot.
    rewrite upcl_SHIFT.
    iDestruct "Hprot" as (t Q) "[-> [Hshift Hk]]".

    iSpecialize ("Hshift" $! k with "[Hk]").
    { iIntros (w) "Hw". iSpecialize ("Hk" $! (O2Ret w) with "Hw").
      rewrite /deep_handler_spec seal_eq.
      by iSpecialize ("Hk" $! _ _ with "IH"). }
    iModIntro.

    red_match.

    by Simp.
  Qed.

  Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

  Lemma ewp_shift b e Ψ Φ Q : shift_spec b e Ψ Φ Q.
  Proof.
    iIntros "Hshift". unfold Shift.

    Call. iNext. rewrite /deco.

    iApply (ewp_EPerform _ _ _ (ieq ?[y])).
    { (* TODO: Add expr-level rule for EXdata. *)
      Simp;
      with_strategy transparent [evals] unfold evals;
      Simp. by Ret. }
    iIntros (? ->).
    iApply ewp_perform.

    rewrite /prot upcl_SHIFT.
    iExists _, Q. iSplit; [ done | ]. iFrame.
    by iIntros (w) "Hw".
  Qed.

End verification.
