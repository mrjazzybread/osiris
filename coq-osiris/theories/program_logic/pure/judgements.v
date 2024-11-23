From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.
From osiris.program_logic.pure Require Import wp.

(** This file defines the judgements for pure computations. *)

(* TODO: Comment -- Explain encode *)

(* -------------------------------------------------------------------------- *)
(* Value predicates, which are predicates over carrier type [A], which are
    encodable types. *)
Definition returns {A} `{Encode A} (φ : A -> Prop):=
  λ v, ∃ a, v = #a ∧ φ a.

(* TODO Comment *)
Definition returns_list {A} `{Encode A} (φ : list A -> Prop) :=
  λ (v : list val),
    ∃ a, v = map encode.encode a ∧ φ a.

(* -------------------------------------------------------------------------- *)
(** The [total] judgement *)

(* [total m φ] states that [m] is a pure computation that will reduce to a
    value satisfying the predicate [φ]. It is total in the sense that
    the computation may not raise any exceptions. *)
Class TotalJudgement {A A'} :=
  total : forall {E}, micro A' E -> (A -> Prop)-> Prop.

(* TODO Comment *)
#[global] Instance TotalJudgement_val `{Encode A}:
  @TotalJudgement A val :=
  fun _ a Φ => pure_wp a (returns Φ) ⊥.

(* Useful for lifting [total (evals η e) φ]. TODO: Explain *)

#[global] Instance TotalJudgement_list `{Encode A}:
  @TotalJudgement (list A) (list val) :=
  fun _ a Φ => pure_wp a (returns_list Φ) ⊥.

(* -------------------------------------------------------------------------- *)
(** The [pure] judgement *)

(* [pure m φ ψ] states that [m] is a pure computation that will reduce to a
    value satisfying the predicate [φ], or it may throw an exception and
    satisfy [ψ]. *)
Class PureJudgement {A A'} :=
  pure : forall {E}, micro A' E -> (A -> Prop) -> (E -> Prop) -> Prop.

(* TODO Comment *)
#[global] Instance PureJudgement_val {A} {EncA : Encode A} :
  @PureJudgement A val :=
  fun _ a Φ Ψ => pure_wp a (returns Φ) Ψ.

#[global] Instance PureJudgement_list `{Encode A}:
  @PureJudgement (list A) (list val) :=
  fun _ a Φ Ψ => pure_wp a (returns_list Φ) Ψ.

(* -------------------------------------------------------------------------- *)
(* Notations *)

Notation "η ⊢ '{' e 'ensures' Φ '}'" :=
  (total (eval η e) Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "η ⊢ '{' e 'ensures' Φ 'raises' ψ '}'" :=
  (pure (eval η e) Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  e  '/' 'ensures'  Φ  'raises'  ψ  '}' ']'").

Notation "'{' e 'ensures' Φ '}' " :=
  (total e Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "'{' e 'ensures' Φ 'raises' ψ '}'" :=
  (pure e Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  'raises'  ψ  '}' ']'").

Opaque TotalJudgement_val.
(* Opaque TotalJudgement_poly. *)
Opaque PureJudgement_val.
(* Opaque PureJudgement_poly. *)
Opaque pure.
Opaque total.

(* -------------------------------------------------------------------------- *)

(* Inversion tactic. *)

Ltac returns_eauto :=
  repeat match goal with
  | h: returns _ ?v |- _ =>
      let a := fresh "v" in
      let Ha_ensures := fresh "Ha_ensures" in
      destruct h as (a & ? & Ha_ensures); try subst v
  end.

#[export]
  Hint Extern 1 (pure_wp _ (returns _) _) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (total _ _) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (pure _ _ _) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (pure (throw _) _ _) => apply pure_wp_throw : pure.
#[export]
  Hint Extern 1 (pure (ret _) _ _) => apply pure_wp_ret : pure.
#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

(* -------------------------------------------------------------------------- *)
