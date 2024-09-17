From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.

From osiris.program_logic.pure Require Import wp.

(** Notational typeclasses for pure hoare triples. *)

(* Value predicates, which are predicates over carrier type [A], which are *)
(*    encodable types. *)
Definition returns {A} `{Encode A} (φ : A -> Prop):=
  λ v, ∃ a, v = #a ∧ φ a.

(* Class of judgements over [micro] expressions, which are lifted over encodable
  values. *)
Class TotalJudgement :=
  total : forall {A E} `{Encode A}, micro val E -> (A -> Prop)-> Prop.

#[global] Instance TotalJudgement_ : TotalJudgement :=
  fun _ _ _ a Φ => pure_wp a (returns Φ) ⊥.

Class PureJudgement :=
  pure : forall {A E} `{Encode A}, micro val E -> (A -> Prop) -> (E -> Prop) -> Prop.

#[global] Instance PureJudgement_ : PureJudgement :=
  fun _ _ _ a Φ Ψ => pure_wp a (returns Φ) Ψ.

Notation "η ⊢ '{' e 'ensures' Φ '}'" :=
  (total (eval η e) Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  '/' e  '/' 'ensures'  Φ  '}' ']'").

Notation "η ⊢ '{' e 'ensures' Φ 'catches' ψ '}'" :=
  (pure (eval η e) Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  '/' e  '/' 'ensures'  Φ  'catches'  ψ  '}' ']'").

Notation "'{' e 'ensures' Φ '}' " :=
  (total e Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "'{' e 'ensures' Φ 'catches' ψ '}'" :=
  (pure e Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  'catches'  ψ  '}' ']'").

Opaque TotalJudgement_.
Opaque PureJudgement.
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
  Hint Extern 1 ({ _ ensures _ }) => returns_eauto : pure.

#[export]
  Hint Extern 1 ({ _ ensures _ catches _ }) => returns_eauto : pure.

#[export]
  Hint Extern 1 ({ throw _ ensures _ catches _ }) =>
  apply pure_wp_throw : pure.

#[export]
  Hint Extern 1 ({ ret _ ensures _ catches _ }) =>
  apply pure_wp_ret : pure.

#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

(* -------------------------------------------------------------------------- *)
