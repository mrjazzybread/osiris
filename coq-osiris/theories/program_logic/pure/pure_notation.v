From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.

(** Notational typeclasses for pure hoare triples. *)

(* Value predicates, which are predicates over carrier type [A], which are *)
(*    encodable types. *)
Structure vPred :=
  { vpred : forall {A} `{Encode A}, (A → Prop) -> val -> Prop }.

Canonical Structure vPred_Instance : vPred :=
  {| vpred := λ _ _  φ v, ∃ a, v = #a ∧ φ a |}.

Class Pure := pure : forall {A E}, micro A E -> vPred -> Prop.

Notation "'EXPR' e 'REQUIRES' Φ" :=
  (pure e Φ)
   (at level 20, e, Φ at level 200,
     format "'[hv' 'EXPR'  e '/' 'REQUIRES'  Φ ']'").

Notation "'ENV' η 'EXPR' e 'REQUIRES' Φ" :=
  (pure (eval η e) Φ)
   (at level 20, e, Φ at level 200,
     format "'[hv' 'ENV'  η '/' 'EXPR'  e '/' 'REQUIRES' Φ ']'").

