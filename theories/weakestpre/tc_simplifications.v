From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics specifications.



(* -------------------------------------------------------------------------- *)

(* This Section defines classes to simplify the goal. *)

Section TypeclassesDefinitions.
  Context `{!osirisGS_gen hlc Σ}.

  (* [TC_change_goal] can either be used to simplify the goal
     (Cf. [inst_TCsimp_change_goal]) or to help with automation (Cf. the section
     [Specifications]. *)
  Class TC_change_goal (P Q: iProp Σ) Δ :=
    tc_change_goal : environments.envs_entails Δ P →
                     environments.envs_entails Δ Q.

  Class TCsimp {A} (m m': free A) :=
    tc_simp: simp m m'.

End TypeclassesDefinitions.



(* -------------------------------------------------------------------------- *)

(* Instances of the above typeclasses are defined. They are grouped in sections
   depending on their meaning. *)


(* The following instances are about simplifying the goal using [simp]. *)
Section Simp.
  Context `{!osirisGS_gen hlc Σ}.

  Global Instance inst_TCsimp_change_goal {A} s E (m m': free A) φ Δ
         `{p: TCsimp A m m'}
    : TC_change_goal (WP m' @ s; E {{ v, φ v }}) (WP m @ s; E {{ v, φ v }}) Δ
  | 200 :=
    tac_change_goal Δ _ _ (wp_simp m m' s E φ p).
  Global Hint Mode inst_TCsimp_change_goal + + + + - + + +
    : typeclass_instances.

  Global Instance inst_TCsimp_eval {A}
         (η : env) (e : expr) (k : val → free A) (ko : () → free A)
    : TCsimp (Stop CEval (η, e) k ko) (try (eval η e) k ko).
  Proof. apply SimpEval. Qed.
  Global Hint Mode inst_TCsimp_eval + + + + + : typeclass_instances.

  Global Instance inst_TCsimp_loop {A}
         (η : env) (x : var) (i1 i2 : int) (e : expr)
         (k : val → free A) (ko : () → free A)
    : TCsimp (Stop CLoop (η, x, i1, i2, e) k ko) (try (loop η x i1 i2 e) k ko).
  Proof. apply SimpLoop. Qed.
  Global Hint Mode inst_TCsimp_loop + + + + + + + + : typeclass_instances.

  Global Instance inst_TCsimp_flip {A}
         (x : ()) (k : bool → free A) (ko : () → free A) (m : free A)
         (p: TCsimp (k false) m) (p': TCsimp (k true) m)
    : TCsimp (Stop CFlip x k ko) m.
  Proof. by apply SimpFlip. Qed.
  Global Hint Mode inst_TCsimp_loop + + + + + + - - : typeclass_instances.


  Global Instance inst_TCsimp_par_ret_ret {A A1 A2: Type}
         (a1 : A1) (a2 : A2) (k : A1 * A2 → free A)
    : TCsimp (Par (ret a1) (ret a2) k (λ _ : (), Next)) (k (a1, a2)).
  Proof. eapply SimpTransitive; eauto with simp. Qed.
  Global Hint Mode inst_TCsimp_par_ret_ret + + + + + +
    : typeclass_instances.

  Global Instance inst_TCsimp_par_ret_left {A A1 A2 : Type}
         (a1 : A1) (m2 : free A2) (k : A1 * A2 → free A) (ko : () → free A)
    : TCsimp (Par (ret a1) m2 k ko) (try m2 (λ v2 : A2, k (a1, v2)) ko).
  Proof. apply SimpParRetLeft. Qed.
  Global Hint Mode inst_TCsimp_par_ret_left + + + + + + +
    : typeclass_instances.

  Global Instance inst_TCsimp_par_ret_right {A A1 A2 : Type}
         (m1 : free A1) (a2 : A2) (k : A1 * A2 → free A) (ko : () → free A)
    : TCsimp (Par m1 (ret a2) k ko) (try m1 (λ v1 : A1, k (v1, a2)) ko).
  Proof. apply SimpParRetRight. Qed.
  Global Hint Mode inst_TCsimp_par_ret_left + + + + + + +
    : typeclass_instances.

  Global Instance inst_TCsimp_par {A A1 A2 : Type}
         (m1 m'1 : free A1) (m2 m'2 : free A2)
         (k : A1 * A2 → free A) (ko : () → free A)
         (p: TCsimp m1 m'1) (p': TCsimp m2 m'2)
    : TCsimp (Par m1 m2 k ko) (Par m'1 m'2 k ko).
  Proof. by apply SimpPar. Qed.
  Global Hint Mode inst_TCsimp_par + + + + - + - + + - -
    : typeclass_instances.

  Global Instance inst_TCsimp_reflexive {A} (m: free A)
    : TCsimp m m | 1000.
  Proof. apply SimpReflexive. Qed.
  Global Hint Mode inst_TCsimp_reflexive + +: typeclass_instances.

End Simp.



(* The following section defines useful instances of typeclasses defined above
   in order top take into account function specifications.

   Currently, the following instances allow for specifying unary and binary
   functions only, so hints are easily defined: The cost of looking for the
   specification of an i-ary function is
     → (100 - 10 * i) for the instance using instances of [Encode] ;
     → (100 - 10 * i + n) for instances which do not use [Encode] n-times ;
   This way, specifications of binary calls are applied first, if possible. *)
Section Specifications.
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

End Specifications.
