From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.
From osiris.program_logic.pure Require Import wp.

(** This file defines the judgements for pure computations. *)

(* -------------------------------------------------------------------------- *)
(** The [pure] judgement *)

(* [pure m φ ψ] states that [m] is a pure computation that will reduce to a
    value satisfying the predicate [φ], or it may throw an exception and
    satisfy [ψ]. *)

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
