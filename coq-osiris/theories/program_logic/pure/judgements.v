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
Class TotalJudgement {A} {EncA : Encode A} {A'} :=
  total : forall {E}, micro A' E -> (A -> Prop)-> Prop.

#[global] Instance TotalJudgement_val {A} {EncA : Encode A} :
  @TotalJudgement A EncA val | 10 :=
  fun _ a Φ => pure_wp a (returns Φ) ⊥.

#[global] Instance TotalJudgement_poly {A} {EncA : Encode A} :
  @TotalJudgement A EncA A | 100 :=
  fun _ a Φ => pure_wp a Φ ⊥.

Class PureJudgement {A} {EncA : Encode A} {A'} :=
  pure : forall {E}, micro A' E -> (A -> Prop) -> (E -> Prop) -> Prop.

#[global] Instance PureJudgement_val {A} {EncA : Encode A} :
  @PureJudgement A EncA val | 10 :=
  fun _ a Φ Ψ => pure_wp a (returns Φ) Ψ.

#[global] Instance PureJudgement_poly {A} {EncA : Encode A} :
  @PureJudgement A EncA A | 100 :=
  fun _ a Φ Ψ => pure_wp a Φ Ψ.

Notation "η ⊢ '{' e 'ensures' Φ '}'" :=
  (total (eval η e) Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  e  '/' 'ensures'  Φ  '}' ']'").

(* FIXME: [catches] => [raises] *)
Notation "η ⊢ '{' e 'ensures' Φ 'catches' ψ '}'" :=
  (pure (eval η e) Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' η  '⊢'  '{'  e  '/' 'ensures'  Φ  'catches'  ψ  '}' ']'").

Notation "'{' e 'ensures' Φ '}' " :=
  (total e Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").

Notation "'{' e 'ensures' Φ 'catches' ψ '}'" :=
  (pure e Φ ψ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  'catches'  ψ  '}' ']'").

Opaque TotalJudgement_val.
Opaque TotalJudgement_poly.
Opaque PureJudgement_val.
Opaque PureJudgement_poly.
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
