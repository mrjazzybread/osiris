
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat.
From iris.program_logic Require Import weakestpre adequacy.

From osiris.program_logic Require Import ewp rules.

(* ========================================================================== *)
(** *Typeclass instance for Iris [Language] mixin *)

Section lang_instance.

  Context {res exn : Type}.

  (* N.B.: We ignore the observation and list of expressions for now. *)
  Definition prim_step
    (e : micro res exn) (σ : store) (obs : list nat)
    (e' : micro res exn) (σ' : store) (exprs : list (micro res exn)) : Prop :=
    step.step (σ, e) (σ', e') /\ exprs = [].

  Definition is_outcome (e : micro res exn) : option (outcome2 res exn) :=
    match e with
    | Ret a => Some (O2Ret a)
    | Throw e => Some (O2Throw e)
    | _ => None
    end.

  Lemma is_outcome_inject2 a :
    is_outcome (inject2 a) = Some a.
  Proof.
    destruct a; auto.
  Qed.

  Definition osiris_lang_mixin :
    LanguageMixin inject2 is_outcome prim_step.
  Proof.
    constructor; auto.
    { apply is_outcome_inject2. }
    { intros; destruct e; inversion H; auto. }
    { intros; destruct e; inversion H; auto; subst; inversion H0. }
  Defined.

  Canonical Structure osiris_lang := Language (osiris_lang_mixin).

End lang_instance.

(* ========================================================================== *)

(* ========================================================================== *)
(** * Adequacy. *)

Section adequacy.

  Context `{!osirisGS Σ} `{protocol_wf Σ P} `{Bottom P}.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP]. *)

  Theorem ewp_adequacy (e : microvx) σ φ E :
    (∀ `{!heapGS Σ}, ⊢ EWP e @ E <| ⊥ |> {{ fun v =>  ⌜ φ v ⌝ }}) →
      adequate NotStuck e σ (λ v _, φ v).
  Proof.
    intros Hwp.
  Admitted.

End adequacy.
