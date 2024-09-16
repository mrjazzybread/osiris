From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.

From osiris.program_logic.pure Require Import pure_judgement.

(** Notational typeclasses for pure hoare triples. *)

(* Value predicates, which are predicates over carrier type [A], which are *)
(*    encodable types. *)
Definition returns {A} `{Encode A} (φ : A -> Prop):=
  λ v, ∃ a, v = #a ∧ φ a.

(* Class of judgements over [micro] expressions, which are lifted over encodable
  values. *)
Class Judgement :=
  jm : forall {A E} `{Encode A}, micro val E -> (A -> Prop)-> Prop.

(* The default instantiation of a judgement uses the pure predicate. *)
#[global] Instance PureJudgement : Judgement :=
  fun _ _ _ a Φ => pure a (returns Φ) ⊥.

Notation "'{' η ⊢ e 'ensures' Φ '}'" :=
  (jm (eval η e) Φ)
   (at level 80, e, Φ at level 100,
     format "'[hv' '{'  η  '⊢'  '/' e  '/' 'ensures'  Φ  '}' ']'").

Notation "'{' e 'ensures' Φ '}' " :=
  (jm e Φ)
   (at level 80, e, Φ at level 200,
     format "'[hv' '{'  e  '/' 'ensures'  Φ  '}' ']'").
