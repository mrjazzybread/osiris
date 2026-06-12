From osiris Require Import base.
From osiris.olang Require Import lang code eval.
Require Import wp.

(** This file defines the judgements for pure computations. *)

(* -------------------------------------------------------------------------- *)
(** The [pure] judgement *)

(* [pure m φ ψ] states that [m] is a pure computation that will reduce to a
    value satisfying the predicate [φ], or it may throw an exception and
    satisfy [ψ]. *)

Definition pure `{Observe A V} {E} (m : micro V E) (Φ : A -> Prop) :
  forall {B} `{Observe B E}, (B -> Prop) -> Prop :=
    fun B _ Ψ => pure_wp m (returns Φ) (returns Ψ).

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
  (pure e Φ (⊥ : void → Prop))
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "η ⊢ₚ '{' e 'ensures' Φ '}'" :=
  (pure (eval η e) Φ (⊥ : void → Prop))
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
  Hint Extern 1 (pure_wp _ (returns _) (returns _)) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (pure _ _ _) => returns_eauto; by firstorder : pure.
#[export]
  Hint Extern 1 (pure (throw _) _ _) => apply pure_wp_throw : pure.
#[export]
  Hint Extern 1 (pure (ret _) _ _) => apply pure_wp_ret : pure.
#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

(* -------------------------------------------------------------------------- *)
