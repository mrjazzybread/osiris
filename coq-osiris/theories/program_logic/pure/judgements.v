From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.
From osiris.program_logic.pure Require Import wp.

(** This file defines the judgements for pure computations. *)

(* TODO: Comment -- Explain encode *)

(* One justification for [Observe] appears in pure_rules.v, to generalize
   [pure_bind] to more than just [@bind val val] *)

(* -------------------------------------------------------------------------- *)

(* Given an encodable value of type [A], it can be observed as a particular
   value [V]. *)
Class Observe A (EncA: Encode A) V : Type :=
  { observe : A -> V }.

Arguments Observe A {EncA} V.
Arguments observe {_ _ _ _}.

Global Instance observe_encode {A} `{Encode A}:
  Observe A val :=
  {| observe := encode |}.

(* Useful for [pure (evals η _) φ ψ]. *)
Global Instance observe_list {A} `{Encode A}:
  Observe (list A) (list val) | 100 :=
  {| observe := (map encode.encode) |}.

(* NOTE : Do not declare an instance of [Observe val val], as it will
   instantiate evars eagerly to this instance when it is not desired.
   (Even if its weight is very high.) *)

Notation "♯ x" := (observe x) (at level 5).

(* -------------------------------------------------------------------------- *)

(* TODO Comment *)

Lemma solve_observe_nil A (Enc:Encode A) :
  forall (xs : list A),
    [] = xs →
    nil = ♯xs.
Proof. intros; subst; cbn; eauto. Qed.

Lemma solve_observe_cons {A} {Enc: Encode A} :
  forall (v : val) (a : A) tl vtl (x : list A),
    a :: tl = x ->
    v = # a ->
    vtl = ♯ tl ->
    v :: vtl = ♯ x.
Proof.
  induction tl; intros; subst; eauto.
Qed.

Global Hint Extern 0 (_ :: _ = ♯ _) =>
  simple eapply solve_observe_cons : encode.
Global Hint Extern 100 ([] = ♯ _) =>
  simple eapply solve_observe_nil: encode.

(* -------------------------------------------------------------------------- *)

(* TODO Comment *)

Definition returns {A V} `{Observe A V} (φ : A -> Prop):=
  λ (v : V), ∃ a, v = observe a ∧ φ a.

(* -------------------------------------------------------------------------- *)
(** The [pure] judgement *)

(* [pure m φ ψ] states that [m] is a pure computation that will reduce to a
    value satisfying the predicate [φ], or it may throw an exception and
    satisfy [ψ]. *)

(* TODO Comment *)

Definition pure `{Observe A V} :
  forall {E}, micro V E -> (A -> Prop) -> (E -> Prop) -> Prop :=
    fun _ a Φ Ψ => pure_wp a (returns Φ) Ψ.

(* -------------------------------------------------------------------------- *)

(* Notations *)

Notation "η ⊢ₚ '{' e 'ensures' Φ 'raises' ψ '}'" :=
  (pure (eval η e) Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢ₚ'  '{'  e  '/' 'ensures'  Φ  'raises'  ψ  '}' ']'").

Notation "'{' e 'ensures' Φ 'raises' ψ '}'" :=
  (pure e Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  'raises'  ψ  '}' ']'").

Notation "'{' e 'ensures' Φ '}'" :=
  (pure e Φ ⊥)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "η ⊢ₚ '{' e 'ensures' Φ '}'" :=
  (pure (eval η e) Φ ⊥)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢ₚ'  '{'  e  '/' 'ensures'  Φ  '}' ']'").

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
  Hint Extern 1 (pure _ _ _) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (pure (throw _) _ _) => apply pure_wp_throw : pure.
#[export]
  Hint Extern 1 (pure (ret _) _ _) => apply pure_wp_ret : pure.
#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

(* -------------------------------------------------------------------------- *)
