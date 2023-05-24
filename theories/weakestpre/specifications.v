From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics.



(* The follwoing section defines the typeclasses to use to define a
   specification. *)
Section TypeclassesDefinitions.
  Context `{!osirisGS_gen hlc Σ}.

  (* [pure_unary_spec] is used to tell osiris that [f] represents a closure
     whose behaviour is that of [ff], a unary Gallina function. *)
  Class pure_unary_spec
        {A B: Type} `{!Encode A} `{!Encode B}
        (f: val) (ff: A → B) :=
    spec:
      ∀ (b: A) s E (φ: val → iProp Σ),
        ▷ (φ #(ff b)) -∗
        wp s E (call f #b) φ.

  (* [pure_binary_spec] is used to tell osiris that [f] represents a closure
     whose behaviour is that of [ff], a binary Gallina function. *)
  Class pure_binary_spec
        {A B C: Type} `{!Encode A} `{!Encode B} `{!Encode C}
        (f: val) (ff: A → B → C) (a: A) (b: B) :=
    spec2:
      ∀ s E (φ: val → iProp Σ),
        ▷ (φ #(ff a b)) -∗
        wp s E (call f #a) (λ (v: val), wp s E (call v #b) φ).
  Global Hint Mode pure_binary_spec - - - - - - - - ! !
    : typeclass_instances.


  (* [pure_partial_binary_spec] is used to tell osiris that [f] represents a
     closure whose behaviour is that of [ff], a binary Gallina function.
     Using this typeclass will allow for automation when encounting partial
     applications of [f]. *)
  Class pure_binary_partial_spec
        {A B C: Type} `{!Encode A} `{!Encode B} `{!Encode C}
        (f: val) (ff: A → B → C) :=
    spec2_1:
      ∀ (a: A) s E (φ: val → iProp Σ),
         (∀ (vpartial: val),
                       (∀ (b: B) s' E',
                           wp s' E' (call vpartial #b)
                              (λ res, ⌜res = #(ff a b)⌝)) -∗
                       φ vpartial) -∗ (* TODO: get a later here. *)
        wp s E (call f #a) φ.

End TypeclassesDefinitions.
