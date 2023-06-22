From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

(* TODO avoid needless sections and indentation *)

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.logic Require Import orders.

Local Transparent eval. (* TODO. *)

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
    Definition Stdlib__andb : val :=
      VClo2 EBoolConj.
    Definition Stdlib__orb : val :=
      VClo2 EBoolDisj.
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
      EnvCons "&&" Stdlib__andb $
      EnvCons "||" Stdlib__orb $
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

(* Some properties of integers that are needed below. *)

Local Lemma Zeq_spec (x y : Z) :
  (* Is_true *) (x =? y)%Z ↔ (x = y)%Z.
Proof.
  rewrite Is_true_true.
  rewrite Z.eqb_eq.
  tauto.
Qed.

Local Lemma Zlt_spec (x y : Z) :
  (* Is_true *) (x <? y)%Z ↔ (x < y)%Z.
Proof.
  rewrite Zlt_is_lt_bool.
  rewrite Is_true_true.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO specify every pure function using [SIMP], not [WP]. *)

Section Stdlib__specs.
  Context `{!osirisGS_gen hlc Σ}.

  Section Stdlib__spec__arith_comp.

    Lemma Stdlib__eq__spec s E :
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        representable i1 →
        representable i2 →
        ⊢ WP call Stdlib__eq v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 =? i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite eq_repr_repr.
    Qed.

    Lemma Stdlib__lt__spec s E :
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        representable i1 →
        representable i2 →
        ⊢ WP call Stdlib__lt v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 <? i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite lt_repr_repr.
    Qed.

    Lemma Stdlib__eq_spec :
      decide_spec Stdlib__eq representable Logic.eq. (* same as Z.eq *)
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->eq_repr_repr by assumption.
      rewrite Zeq_spec.
      tauto.
    Qed.

    Lemma Stdlib__ne_spec :
      decide_spec Stdlib__ne representable (λ x y, x ≠ y).
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->eq_repr_repr by assumption.
      rewrite <-Zeq_spec.
      rewrite Is_true_true negb_true -Is_true_false.
      tauto.
    Qed.

    Lemma Stdlib__lt_spec :
      decide_spec Stdlib__lt representable Z.lt.
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Zlt_spec.
      tauto.
    Qed.

    Lemma Stdlib__le_spec :
      decide_spec Stdlib__le representable Z.le.
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Is_true_true negb_true -Is_true_false.
      rewrite Zlt_spec.
      lia.
    Qed.

    Lemma Stdlib__gt_spec :
      decide_spec Stdlib__gt representable (λ x y, Z.lt y x).
                                           (* avoid [Z.gt] *)
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Zlt_spec.
      tauto.
    Qed.

    Lemma Stdlib__ge_spec :
      decide_spec Stdlib__ge representable (λ x y, Z.le y x).
                                           (* avoid [Z.ge] *)
    Proof.
      intros x Hx. SIMP_enter. intros y Hy. SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Is_true_true negb_true -Is_true_false.
      rewrite Zlt_spec.
      lia.
    Qed.

  End Stdlib__spec__arith_comp.



  Section Stdlib__spec__store.
    Lemma Stdlib__ref__spec v (s: stuckness) (E: coPset) :
      ⊢ WP call Stdlib__ref v @ s; E
           {{ λ vl, ∃ (l: loc), l ↦ v ∗ ⌜vl = VLoc l ⌝ }}.
    Proof.
      wp_call. wp_alloc l "[Hl _]".
      iExists l.
      iFrame.
      iPureIntro. reflexivity.
    Qed.

    Lemma Stdlib__load__spec vl l v s E :
      {{{ ⌜vl = VLoc l⌝ ∗ l ↦ v }}}
        call Stdlib__load vl @ s; E
      {{{ r, RET r; ⌜r = v⌝ ∗ l ↦ v }}}.
    Proof.
      iIntros (φ) "[->Hpre] Hφ".
      wp_call.
      wp_load "Hpre".
      wp_use "Hφ".
      iFrame.
      iPureIntro. reflexivity.
    Qed.

    Lemma Stdlib__store__spec vl l v v' s E :
      {{{ ⌜vl = VLoc l⌝ ∗ l ↦ v }}}
        call Stdlib__store vl @ s; E
      {{{ vstore, RET vstore;
                  WP call vstore v' @ s; E
                     {{ λ v, ⌜ v = VUnit ⌝ ∗
                             l ↦ v' }} }}}.
    Proof.
      iIntros (φ) "[-> Hl] Hφ".
      wp_call. iApply "Hφ". clear φ.
      wp_call.
      wp_store "Hl". by iSplit.
    Qed.
  End Stdlib__spec__store.


  (* Lemmas to better handle fully-applied functions of the standart library. *)
  Lemma Stdlib__load__spec_tac vl l v s E :
    ⊢ ∀ φ, ⌜ vl = VLoc l ⌝ -∗
    l ↦ v -∗
    (l ↦ v -∗ φ v) -∗ (* TODO: add a later to this premice (will require to change
              [wp_covariant]. *)
    WP call Stdlib__load vl @ s; E {{ λ v, φ v }}.
  Proof.
    iIntros(φ) "-> Hl Hv".
    iApply (wp_covariant with "[Hl]").
    { iApply (Stdlib__load__spec with "[$Hl]"); first done.
      iNext. iIntros. iAssumption. }
    iIntros (?) "[-> Hl]".
    iApply ("Hv" with "Hl").
  Qed.

  (* TODO: same as above: get a later in the premice. *)
  Lemma Stdlib__ref__spec_tac {A} v s E φ (k: free A) :
    ⊢ (∀ l vl, ⌜vl = VLoc l⌝ -∗ l ↦ v -∗ WP k @ s; E {{ φ }}) -∗
    WP call Stdlib__ref v {{ λ (vl: val), WP k @s; E {{ φ }} }}.
  Proof.
    iIntros "H".
    wp_use Stdlib__ref__spec.
    iIntros (vl)"(%l & Hl & ->)".
    by iApply "H".
  Qed.

  Lemma Stdlib__store__spec_tac l v v' φ s E :
    l ↦ v -∗
    ▷ (l ↦ v' -∗ φ VUnit) -∗
    WP call Stdlib__store (VLoc l) @ s; E
         {{ vpartial, WP call vpartial v' @ s; E {{ v, φ v }} }}.
  Proof.
    iIntros "Hl Hccl".
    iApply (Stdlib__store__spec with "[$Hl //]").
    iNext.
    iIntros (vstore) "Hstore".
    wp_use "Hstore".
    iIntros(?)"[-> Hl]".
    iApply ("Hccl" with "Hl").
  Qed.

End Stdlib__specs.

Global Hint Resolve
  Stdlib__eq_spec
  Stdlib__ne_spec
  Stdlib__lt_spec
  Stdlib__le_spec
  Stdlib__gt_spec
  Stdlib__ge_spec
: SIMP_specs.
(* TODO these specs are now unused, I think *)

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
