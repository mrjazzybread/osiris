From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.logic Require Import orders.

(* The symbols of the OCaml standard library are translated as
   [Stdlib.<symbol>].
   This file defines:
     1. symbols of [Stdlib], eg. (+), ... ;
     2. [Stdlib] as a module ;
     3.a. specifications for the symbols of the module ;
     3.b. a unified specification for the module ;
     4. a tactic to use automatically apply the aforementioned specs.

   After 3.b., the code is turned opaque to (1) better control its usage and (2)
   avoid it to be unfolded: some unfolding would lead to several duplications of
   continuations (ie. the rest of the code). *)

Local Notation VClo1 body :=
  (
    VClo EnvNil $
      AnonFun "x" $
      (body (EVar "x"))
  ).

Local Notation VClo2 body :=
  (
    VClo EnvNil $
      AnonFun "x" $
      EFun1Var "y" $
      (body (EVar "x") (EVar "y"))
  ).

Section StdLib__code.
  Context `{!osirisGS_gen hlc Σ}.

  Section Arithmetic_operations.
    Definition Stdlib__add : val :=
      VClo2 EIntAdd.
    Definition Stdlib__sub : val :=
      VClo2 EIntSub.
    Definition Stdlib__mul : val :=
      VClo2 EIntMul.
    Definition Stdlib__div : val :=
      VClo2 EIntDiv.
    Definition Stdlib__mod : val :=
      VClo2 EIntMod.
    Definition Stdlib__neg : val :=
      VClo1 EIntNeg.
  End Arithmetic_operations.

  Section Arithmetic_comparison.
    Definition Stdlib__eq : val :=
      VClo2 EOpEq.
    Definition Stdlib__ne : val :=
      VClo2 EOpNe.
    Definition Stdlib__lt : val :=
      VClo2 EOpLt.
    Definition Stdlib__le : val :=
      VClo2 EOpLe.
    Definition Stdlib__gt : val :=
      VClo2 EOpGt.
    Definition Stdlib__ge : val :=
      VClo2 EOpGe.
    Axiom Stdlib__compare : val.
  End Arithmetic_comparison.

  Section Stdlib__store.
    Definition Stdlib__ref : val :=
      VClo1 ERef.
    Definition Stdlib__load : val :=
      VClo1 ELoad.
    Definition Stdlib__store : val :=
      VClo2 EStore.
  End Stdlib__store.

  Section Stdlib__tuples.
    Definition Stdlib__fst : val :=
      VClo1 (λ (e : expr),
        ELet1 (PPair (PVar "x") PAny) e $
        EVar "x"
      ).
    Definition Stdlib__snd : val :=
      VClo1 (λ (e : expr),
        ELet1 (PPair PAny (PVar "y")) e $
        EVar "y"
      ).
  End Stdlib__tuples.

  Section Stdlib__bool.
    Definition Stdlib__not : val :=
      VClo1 EBoolNeg.
    (* Boolean conjunction and disjunction are not functions;
       they are primitive operations. *)
  End Stdlib__bool.

  (* Putting everything together. *)
  Definition Stdlib :=
    VStruct $
      EnvCons "-" Stdlib__sub $
      EnvCons "+" Stdlib__add $
      EnvCons "*" Stdlib__mul $
      EnvCons "~-" Stdlib__neg $
      EnvCons "=" Stdlib__eq $
      EnvCons "<>" Stdlib__ne $
      EnvCons "<" Stdlib__lt $
      EnvCons "<=" Stdlib__le $
      EnvCons ">" Stdlib__gt $
      EnvCons ">=" Stdlib__ge $
      EnvCons "compare" Stdlib__compare $
      EnvCons "ref" Stdlib__ref $
      EnvCons "!" Stdlib__load $
      EnvCons ":=" Stdlib__store $
      EnvCons "fst" Stdlib__fst $
      EnvCons "snd" Stdlib__snd $
      EnvCons "not" Stdlib__not $
      EnvNil.
End StdLib__code.

(* -------------------------------------------------------------------------- *)

(* Specification templates. *)

(* A specification for a pure function [decide] that decides a relation [R],
   subject to a precondition [P], producing a Boolean outcome. *)

(* This specification is nondeterministic: it uses [SIMP] and a relation [R]
   of type [A → A → Prop]. One could prefer a deterministic specification
   that uses [simp] and a function of type [A → A → bool]. TODO: try it. *)

Definition decide_spec `{Encode A}
  (decide : val) (P : A → Prop) (R : A → A → Prop)
:=
  ∀ (x : A),
    P x →
    SIMP (call decide #x) (λ v,
      ∀ (y : A),
      P y →
      SIMP (call v #y) (λ (b : bool),
        b ↔ R x y
      )
    ).

(* The above specification states that an application of [decide] to just
   one argument returns a closure. As a sanity check, we verify that this
   is stronger than the following statement, which describes an application
   of [decide] to two arguments. *)

Local Lemma decide_spec' `{Encode A}
  (decide : val) (P : A → Prop) (R : A → A → Prop)
:
  decide_spec decide P R →
  ∀ (x y : A), P x → P y →
  SIMP
    (bind (call decide #x) (λ v, call v #y))
    (λ (b : bool),
      b ↔ R x y
    ).
Proof.
  intros Hspec x y Hx Hy.
  eapply SIMP_bind; [ eauto | intros v; cbn; intros Hv ].
  eauto.
Qed.

(* A specification for a [compare] function that decides a preorder [le],
   producing an integer code that encodes a three-way outcome. *)

(* The double application [compare x y] returns a (representable) integer
   code [c] such that the sign of [c] encodes the three possible outcomes
   of the comparison between [x] and [y]. *)

(* TODO contrary to [decide], we do not allow a precondition [P]. *)

Definition compare_spec `{Encode A} (compare : val) (le : A → A → Prop) :=
  let lt := strict le in
  let eq := equivalent le in
  ∀ (x : A),
  SIMP (call compare #x) (λ v,
    ∀ (y : A),
    SIMP (call v #y) (λ (c : Z),
      representable c ∧
      (c < 0 ↔ lt x y) ∧
      (c = 0 ↔ eq x y) ∧
      (0 < c ↔ lt y x)
    )
  ).

(* -------------------------------------------------------------------------- *)

(* TODO specify every pure function using [SIMP], not [WP]. *)

(* The following specification lemmas are no longer used,
   since [simp] now steps into calls to concrete closures. *)

(* TODO The proofs of these lemmas should be one-liners.
        If they are not then our tactics need improvements. *)

Section Stdlib__specs.

Context `{!osirisGS_gen hlc Σ}.

Lemma Stdlib__eq_spec :
  decide_spec Stdlib__eq representable Logic.eq. (* same as Z.eq *)
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zeq_spec.
  tauto.
Qed.

Lemma Stdlib__ne_spec :
  decide_spec Stdlib__ne representable (λ x y, x ≠ y).
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zne_spec.
  tauto.
Qed.

Lemma Stdlib__lt_spec :
  decide_spec Stdlib__lt representable Z.lt.
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zlt_spec.
  tauto.
Qed.

Lemma Stdlib__le_spec :
  decide_spec Stdlib__le representable Z.le.
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zle_spec.
  tauto.
Qed.

Lemma Stdlib__gt_spec :
  decide_spec Stdlib__gt representable (λ x y, Z.lt y x).
                                       (* avoid [Z.gt] *)
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zlt_spec.
  tauto.
Qed.

Lemma Stdlib__ge_spec :
  decide_spec Stdlib__ge representable (λ x y, Z.le y x).
                                       (* avoid [Z.ge] *)
Proof.
  intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
  rewrite Zle_spec.
  tauto.
Qed.

Lemma Stdlib__ref__spec v s E :
  {{{ True }}}
    call Stdlib__ref v @ s; E
  {{{ l, RET #l ; l ↦ v }}}.
Proof.
  iIntros (φ) "_ Hpost".
  wp_enter. wp_simp.
  wp_alloc l "[Hl _]".
  iApply "Hpost". iFrame.
Qed.

Lemma Stdlib__load__spec l v s E :
  {{{ l ↦ v }}}
    call Stdlib__load #l @ s; E
  {{{ RET v ; l ↦ v }}}.
Proof.
  iIntros (φ) "Hl Hpost".
  wp_enter. wp_simp.
  wp_load "Hl".
  iApply "Hpost". iFrame.
Qed.

(* [Stdlib__store] is a curried binary function. The application to the
   first argument is pure, so its specification is expressed using SIMP. *)

Lemma Stdlib__store__spec l v v' s E :
  SIMP
    (call Stdlib__store #l)
    (λ c,
      {{{ l ↦ v }}}
        call c v' @ s; E
      {{{ RET #() ; l ↦ v' }}}
    ).
Proof.
  SIMP1.
  iIntros (φ) "Hl Hpost".
  wp_enter. wp_simp.
  wp_store "Hl".
  iApply "Hpost". iFrame.
Qed.

End Stdlib__specs.

(* -------------------------------------------------------------------------- *)

(* TODO WIP *)

(* Some pure functions in the standard library (e.g., the arithmetic operators
   and the comparison operators) can be given deterministic specifications in
   terms of [simp]. So, we seem to have three choices:
   - prove a spec in terms of [SIMP] and make it a lemma in a database;
   - prove a spec in terms of [simp] and make it a lemma in a database;
     (this approach does not work well for curried binary functions,
      as the intermediate value [v] must be existentially quantified)
   - let the user exploit the tactic [simp] at the call site,
     without stating/proving a lemma. *)

Local Lemma experiment_add :
  ∀ (x y : Z),
  simp (bind (call Stdlib__add #x) (λ v, call v #y)) (ret #(x + y)).
Proof.
  intros. simp.
    (* Even though [call] is opaque, the tactic [simp] is able to step
       into a call to a concrete closure. Here, it automatically steps
       into the two calls in succession. *)
Qed.

Local Lemma experiment_eq :
  ∀ (x y : Z), representable x → representable y →
  simp (bind (call Stdlib__eq #x) (λ v, call v #y)) (ret #(Z.eqb x y)).
Proof.
  intros. simp.
Qed.
