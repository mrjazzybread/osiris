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
   specification and alter the goal. *)
Section TypeclassesDefinitions.
  Context `{!osirisGS_gen hlc Σ}.

  Class TC_change_goal (P Q: iProp Σ) Δ :=
    tc_change_goal : environments.envs_entails Δ P →
                     environments.envs_entails Δ Q.

  Class pure_unary_spec
        {A B: Type} `{!Encode A} `{!Encode B}
        (f: val) (ff: A → B) :=
    spec:
      ∀ (b: A) s E (φ: val → iProp Σ),
        ▷ (φ #(ff b)) -∗
        wp s E (call f #b) φ.

  Class pure_binary_spec
        {A B C: Type} `{!Encode A} `{!Encode B} `{!Encode C}
        (f: val) (ff: A → B → C) (a: A) (b: B) :=
    spec2:
      ∀ s E (φ: val → iProp Σ),
        ▷ (φ #(ff a b)) -∗
        wp s E (call f #a) (λ (v: val), wp s E (call v #b) φ).
  Global Hint Mode pure_binary_spec - - - - - - - - ! !
    : typeclass_instances.


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



(* The following section defines useful instances of the typeclasses defined
   above.
   Currently, the following instances allow for specifying unary and binary
   functions only, so hints are easily defined: The cost of looking for the
   specification of an n-ary function is
    → (100 - 10 * i) for the instance using instances of [Encode] ;
    → (100 - 10 * i + n) for instances which do not use [Encode] n-times ;
   This way, specifications of binary calls are applied first, if possible. *)
Section UsefulInstances.
  Context `{!osirisGS_gen hlc Σ}.

  (* ------------------------------------------------------------------------ *)

  (* On unary functions. *)

  Global Instance tc_change_goal_unary_spec
         {A B} `{!Encode A} `{!Encode B}
         f (ff: A → B) `{!pure_unary_spec f ff}
         {Δ φ s E a} :
    TC_change_goal (▷ (φ  # (ff a))) (wp s E (call f #a) φ) Δ | 90 :=
    tac_change_goal
      Δ
      (▷ (φ  # (ff a))) (wp s E (call f #a) φ)
      (spec _ _ _ φ).

  Global Instance tc_change_goal_unary2_spec
         { A B C} `{!Encode A} `{!Encode B} `{!Encode C}
         f (ff: A → B → C) `{p: !pure_binary_partial_spec f ff}
         {Δ φ s E a} :
    TC_change_goal (∀ (vpartial: val),
                       (∀ (b: B) s' E',
                           wp s' E' (call vpartial #b)
                              (λ res, ⌜res = #(ff a b)⌝)) -∗
                       φ vpartial)
                   (wp s E (call f #a) φ) Δ | 90 :=
    tac_change_goal
      Δ
      _ (wp s E (call f #a) φ)
      (@spec2_1 _ _ _ A B C _ _ _ f ff p a s E φ).



  (* ------------------------------------------------------------------------ *)

  (* On binary functions. *)

  Global Instance tc_change_goal_binary_spec
         {A B C} `{!Encode A} `{!Encode B} `{!Encode C}
         f (ff: A → B → C) {a b} `{p: !pure_binary_spec f ff a b}
         {Δ φ s E} :
    TC_change_goal (▷ (φ  # (ff a b)))
                   (wp s E (call f #a)
                       (λ v, wp s E (call v #b) φ)) Δ | 80 :=
    tac_change_goal Δ (▷ (φ  # (ff a b)))
                    (wp s E (call f #a)
                        (λ v, wp s E (call v #b) φ))
                    (@spec2 _ _ _ _ _ _ _ _ _ _ _ _ _ p s E φ).



  (* ------------------------------------------------------------------------ *)

  (* Unfortunatly, it seems that the typeclasses inference mechanism does not
     read [VBool b] as [#b], typeclasses have to be written to be able to deal
     with explicit encoding of Coq terms. *)
  Global Instance tc_change_goal_unary_bool_bool
         (f: val) (ff: bool → bool) {a Δ φ s E}
         {p: pure_unary_spec f ff}
    : TC_change_goal
        (▷ (φ (VBool (ff a))))(wp s E (call f (VBool a)) φ) Δ | 92.
  Proof.
    replace (VBool (ff a)) with #(ff a); last reflexivity.
    replace (VBool a) with #a; last reflexivity.
    intros H.
    apply tc_change_goal, H.
  Qed.

  Global Instance tc_change_goal_unary_Z_Z
         (f: val) (ff: Z → Z) {a Δ φ s E}
         {p: pure_unary_spec f ff}
    : TC_change_goal
        (▷ (φ #(ff a)))
        (wp s E (call f (VInt (int.repr a))) φ) Δ | 92.
  Proof.
    replace (VInt (int.repr a)) with #a; last reflexivity.
    intros H.
    apply tc_change_goal, H.
  Qed.

  Global Instance tc_change_goal_unary_valPair_val
         (f: val) (ff: val * val → val) {v1 v2 Δ φ s E}
         {p: pure_unary_spec f ff}
    : TC_change_goal
        (▷ (φ #(ff (v1, v2))))
        (wp s E (call f (VTuple (VCons v1 (VCons v2 VNil)))) φ) Δ | 92.
  Proof.
    replace (VTuple (VCons v1 $ VCons v2 VNil)) with #(v1, v2);
      last reflexivity.
    intros H.
    apply tc_change_goal, H.
  Qed.

  Global Instance tc_change_goal_binary_Z_Z_Z
         (f: val) (ff: Z → Z → Z) {a b Δ φ s E}
         {p: pure_binary_spec f ff a b}
    : TC_change_goal (▷ (φ #(ff a b)))
                     (wp s E (call f (VInt (int.repr a)))
                         (λ v, wp s E (call v (VInt (int.repr b))) φ)) Δ | 82.
  Proof.
    replace (VInt (int.repr a)) with #a; last reflexivity.
    replace (VInt (int.repr b)) with #b; last reflexivity.
    intros H.
    apply tc_change_goal, H.
  Qed.

  Global Instance tc_change_goal_binary_partial_Z_Z_Z
         (f: val) (ff: Z → Z → Z) {a Δ φ s E}
         {p: pure_binary_partial_spec f ff}
    : TC_change_goal (∀ (vpartial: val),
                         (∀ (b: Z) s' E',
                             wp s' E' (call vpartial #b)
                                (λ res, ⌜res = #(ff a b)⌝)) -∗
                         φ vpartial)
                     (wp s E (call f #a) φ) Δ | 90 :=
    tac_change_goal
      Δ
      _ (wp s E (call f #a) φ)
      (@spec2_1 _ _ _ Z Z Z _ _ _ f ff _ a s E φ).

End UsefulInstances.



(* All the instances are made opaque. *)
Global Opaque tc_change_goal_unary_spec.
Global Opaque tc_change_goal_unary2_spec.
Global Opaque tc_change_goal_binary_spec.
Global Opaque tc_change_goal_unary_bool_bool.
Global Opaque tc_change_goal_unary_Z_Z.
Global Opaque tc_change_goal_binary_Z_Z_Z.
Global Opaque tc_change_goal_binary_partial_Z_Z_Z.
