From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.logic Require Import orders.
From osiris.stdlib Require Import Externals.

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
    VClo [("Externals", Externals)] $
      AnonFun "x" $
      (body (EVar "x"))
  ).

Local Notation VClo2 body :=
  (
    VClo [("Externals", Externals)] $
      AnonFun "x" $
      EFun1Var "y" $
      (body (EVar "x") (EVar "y"))
  ).

Section StdLib__code.
  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)

  (* Arithmetic Operations. *)

  Definition Stdlib__add := VClo2 EIntAdd.
  Definition Stdlib__sub := VClo2 EIntSub.
  Definition Stdlib__mul := VClo2 EIntMul.
  Definition Stdlib__div := VClo2 EIntDiv.
  Definition Stdlib__neg := VClo1 EIntNeg.

  (* Arithmetic Comparisons. *)
  Definition Stdlib__lt : val := VClo2 EOpLt.
  Definition Stdlib__le : val := VClo2 EOpLe.
  Definition Stdlib__gt : val := VClo2 EOpGt.
  Definition Stdlib__ge : val := VClo2 EOpGe.

  (* Arithmetic part of the module. *)
  Definition Stdlib_arith_env : env :=
    [("+", Stdlib__add);
     ("-", Stdlib__sub);
     ("*", Stdlib__mul);
     ("/", Stdlib__div);
     ("~-", Stdlib__neg);
     ("<", Stdlib__lt);
     ("<=", Stdlib__le);
     (">=", Stdlib__ge);
     (">", Stdlib__gt)].

  (* ------------------------------------------------------------------------ *)

  (* Store-related functions. *)
  Definition Stdlib__ref : val := VClo1 ERef.
  Definition Stdlib__load : val := VClo1 ELoad.
  Definition Stdlib__store : val := VClo2 EStore.

  Definition Stdlib_store_env : env :=
    [("!", Stdlib__load);
     (":=", Stdlib__store);
     ("ref", Stdlib__ref)].

  (* ------------------------------------------------------------------------ *)

  (* Polymorphic Comparisons. *)
  Definition Stdlib__eq : val := VClo2 EOpEq.
  Definition Stdlib__ne : val := VClo2 EOpNe.
  Axiom Stdlib__compare : val.

  (* On Pairs. *)
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

  Definition Stdlib_misc_env : env :=
    [("=", Stdlib__eq);
     ("<>", Stdlib__ne);
     ("compare", Stdlib__compare);
     ("fst", Stdlib__fst);
     ("snd", Stdlib__snd)].

  (* ------------------------------------------------------------------------ *)

  (* Boolean Operations. *)
  Definition Stdlib__not : val := VClo1 EBoolNeg.
    (* Boolean conjunction and disjunction are not functions;
       they are primitive operations. *)

  Definition Stdlib_bool_env : env :=
    [("not", Stdlib__not)].

  (* Putting everything together. *)
  Definition Stdlib_env :=
    concat [Stdlib_arith_env;
            Stdlib_store_env;
            Stdlib_misc_env;
            Stdlib_bool_env].

  Definition Stdlib := VStruct Stdlib_env.
End StdLib__code.

Definition toplevel me (φ : env -> Prop) :=
  struct.module (("Stdlib", Stdlib) :: Stdlib_env) me φ.

(* -------------------------------------------------------------------------- *)

(* Specification templates. *)

(* A specification for a pure function [decide] that decides a relation [R],
   subject to a precondition [P], producing a Boolean outcome. *)

(* This specification is nondeterministic: it uses [pure] and a relation [R]
   of type [A → A → Prop]. One could prefer a deterministic specification
   that uses [simp] and a function of type [A → A → bool]. TODO: try it. *)

Definition decide_spec `{Encode A}
  (decide : val) (P : A → Prop) (R : A → A → Prop)
:=
  ∀ (x : A),
    P x →
    pure (call decide #x) (λ v,
      ∀ (y : A),
      P y →
      pure (call v #y) (λ (b : bool),
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
  pure
    (bind (call decide #x) (λ v, call v #y))
    (λ (b : bool),
      b ↔ R x y
    ).
Proof.
  intros Hspec x y Hx Hy.
  eapply pure_bind; [ eauto | intros v; cbn; intros Hv ].
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
  ∀ (x y : A),
  pure (call compare #x) (λ v,
      pure (call v #y) (λ (c : Z),
          representable c ∧
            (c < 0 ↔ lt x y) ∧
            (c = 0 ↔ eq x y) ∧
            (0 < c ↔ lt y x)
        )
    ).

(* -------------------------------------------------------------------------- *)

(* TODO specify every pure function using [pure], not [WP]. *)

(* The following specification lemmas are no longer used,
   since [simp] now steps into calls to concrete closures. *)

(* TODO The proofs of these lemmas should be one-liners.
        If they are not then our tactics need improvements. *)

Section Stdlib__specs.

Context `{!osirisGS Σ}.

Lemma Stdlib__eq_spec :
  decide_spec Stdlib__eq representable Logic.eq. (* same as Z.eq *)
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite eq_repr_repr; try assumption.
  rewrite Zeq_spec.
  tauto.
Qed.

Lemma Stdlib__ne_spec :
  decide_spec Stdlib__ne representable (λ x y, x ≠ y).
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite eq_repr_repr; try assumption.
  rewrite Zne_spec.
  tauto.
Qed.

Lemma Stdlib__lt_spec :
  decide_spec Stdlib__lt representable Z.lt.
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite lt_repr_repr; try assumption.
  rewrite Zlt_spec.
  tauto.
Qed.

Lemma Stdlib__le_spec :
  decide_spec Stdlib__le representable Z.le.
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite lt_repr_repr; try assumption.
  rewrite Zle_spec.
  tauto.
Qed.

Lemma Stdlib__gt_spec :
  decide_spec Stdlib__gt representable (λ x y, Z.lt y x).
                                       (* avoid [Z.gt] *)
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite lt_repr_repr; try assumption.
  rewrite Zlt_spec.
  tauto.
Qed.

Lemma Stdlib__ge_spec :
  decide_spec Stdlib__ge representable (λ x y, Z.le y x).
                                       (* avoid [Z.ge] *)
Proof.
  intros x Hx. pure_enter. intros y Hy. pure_enter.
  rewrite lt_repr_repr; try assumption.
  rewrite Zle_spec.
  tauto.
Qed.

Lemma Stdlib__ref__spec v :
  {{{ True }}}
    call Stdlib__ref v
  {{{ (l : loc), RET #l ; (l ↦ v : iPropI Σ) }}}.
Proof.
  iIntros (φ) "_ Hpost".
  wp_enter. wp_simp.
  wp_alloc l "[Hl _]".
  iApply "Hpost". iFrame.
Qed.

Lemma Stdlib__load__spec l v :
  {{{ l ↦ v }}}
    call Stdlib__load #l
  {{{ v, RET v ; l ↦ v }}}.
Proof.
  iIntros (φ) "Hl Hpost".
  wp_enter. wp_simp.
  wp_load "Hl".
  iApply "Hpost". iFrame.
Qed.

(* [Stdlib__store] is a curried binary function. The application to the
   first argument is pure, so its specification is expressed using pure. *)

Lemma Stdlib__store__spec (l : loc) (v v' : val) :
  pure
    (call Stdlib__store #l)
    (λ c,
      {{{ l ↦ v }}}
        call c v'
      {{{ (v : val), RET #tt; l ↦ v' }}}
    ).
Proof.
  pure1.
  iIntros (φ) "Hl Hpost".
  wp_enter. wp_simp.
  wp_store "Hl". cbn.
  by iSpecialize ("Hpost" $! (VArray nil) with "Hl").
Qed.

End Stdlib__specs.

(* -------------------------------------------------------------------------- *)

(* TODO WIP *)

(* Some pure functions in the standard library (e.g., the arithmetic operators
   and the comparison operators) can be given deterministic specifications in
   terms of [simp]. So, we seem to have three choices:
   - prove a spec in terms of [pure] and make it a lemma in a database;
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
