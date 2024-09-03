From stdpp Require Import telescopes.
From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_shiftreset.

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

Section verification.
  Context `{!osirisGS Σ}.

  Lemma ewp_reset e Ψ Φ : reset_spec e Ψ Φ.
  Proof.
    iIntros "He". unfold Reset.

    Call. iApply ewp_EMatch.

    iApply (ewp_deep_handler _ (SHIFT Ψ Φ) (Φ ↑) with "[He]").
    { by Simp. }

    iLöb as "IH".
    rewrite {2}deep_handler_spec_unfold; iSplit.
    { iIntros (?). iIntros "!> H !>"; destruct o; try done.
      apply_deep_handle_cons_unary.
      - iApply ewp_EPath. by Ret.
      - iIntros "[]". }

    iIntros "!>" (v k) "Hprot"; rewrite /prot.
    rewrite upcl_SHIFT.
    iDestruct "Hprot" as (t Q) "[-> [Hshift Hk]]".

    iSpecialize ("Hshift" $! k with "[Hk]").
    { iIntros (w) "Hw". iSpecialize ("Hk" $! (O2Ret w) with "Hw").
      rewrite /deep_handler_spec seal_eq.
      by iSpecialize ("Hk" $! _ _ with "IH"). }
    iModIntro.

    iApply deep_handle_cons_no_resources. { iPureIntro. specify_cpattern. apply I. }
    iIntros "_".
    iApply deep_handle_cons_no_resources. { iPureIntro. specify_cpattern. apply I. }
    iIntros "_".
    apply_deep_handle_cons_unary.
    { by Simp. }
    iIntros "%F". tauto.
  Qed.


  Lemma ewp_shift b e Ψ Φ Q : shift_spec b e Ψ Φ Q.
  Proof.
    iIntros "Hshift". unfold Shift.
    remember (VClo env _) as f eqn:Heqf; clear Heqf.

    Call. iNext.

    iApply (ewp_EPerform _ _ _ _ (ieq ?[y])).
    { (* TODO: There must be a better way... *)
      iApply ewp_EXData; [ reflexivity | | ].
      iApply big_sepL2_cons. iSplit; [ | by iApply big_sepL2_nil ].
      { iApply ewp_EPath. iApply ewp_value. equality. }
      iIntros (vs) "Hargs".
      iPoseProof (big_sepL2_cons_inv_r with "Hargs") as "Hargs".
      iDestruct "Hargs" as "(%v & %l & -> & -> & Hargs)".
      iPoseProof (big_sepL2_nil_inv_r with "Hargs") as "Hargs".
      iDestruct "Hargs" as "->".
      iPureIntro; reflexivity. }

    iIntros (?) "->".
    iApply ewp_perform.

    rewrite /prot upcl_SHIFT.
    iExists _, Q. iSplit; [ done | ]. iFrame.
    by iIntros (w) "Hw".
  Qed.

End verification.
