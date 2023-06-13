From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

(* TODO avoid needless sections and indentation *)

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.

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
      VClo1 (λ (e : expr),
        EIfThenElse e EFalse ETrue
      ).
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
  ∀ (x y : A), P x → P y →
  SIMP
    (bind (call decide #x) (λ v, call v #y))
    (λ (b : bool),
      b ↔ R x y
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
      intros x y ? ?.
      SIMP_enter.
      rewrite ->eq_repr_repr by assumption.
      rewrite Zeq_spec.
      tauto.
    Qed.

    Lemma Stdlib__ne_spec :
      decide_spec Stdlib__ne representable (λ x y, x ≠ y).
    Proof.
      intros x y ? ?.
      SIMP_enter.
      rewrite ->eq_repr_repr by assumption.
      rewrite <-Zeq_spec.
      rewrite Is_true_true negb_true -Is_true_false.
      tauto.
    Qed.

    Lemma Stdlib__lt_spec :
      decide_spec Stdlib__lt representable Z.lt.
    Proof.
      intros x y ? ?.
      SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Zlt_spec.
      tauto.
    Qed.

    Lemma Stdlib__le_spec :
      decide_spec Stdlib__le representable Z.le.
    Proof.
      intros x y ? ?.
      SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Is_true_true negb_true -Is_true_false.
      rewrite Zlt_spec.
      lia.
    Qed.

    Lemma Stdlib__gt_spec :
      decide_spec Stdlib__gt representable (λ x y, Z.lt y x).
                                           (* avoid [Z.gt] *)
    Proof.
      intros x y ? ?.
      SIMP_enter.
      rewrite ->lt_repr_repr by assumption.
      rewrite Zlt_spec.
      tauto.
    Qed.

    Lemma Stdlib__ge_spec :
      decide_spec Stdlib__ge representable (λ x y, Z.le y x).
                                           (* avoid [Z.ge] *)
    Proof.
      intros x y ? ?.
      SIMP_enter.
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
    iApply wp_covariant.
    { iApply Stdlib__ref__spec. }
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
    iApply (wp_covariant with "Hstore").
    iIntros(?)"[-> Hl]".
    iApply ("Hccl" with "Hl").
  Qed.



  (* ------------------------------------------------------------------------ *)
  (* Pure unary functions. *)

  Global Instance Stdlib__not__TCspec : pure_unary_spec Stdlib__not negb.
  Proof. iIntros ([] s E φ); iIntros "H"; wp_call; iAssumption. Qed.

  Global Instance Stdlib__neg__TCspec : pure_unary_spec Stdlib__neg Z.opp.
  Proof.
    iIntros (i s E φ); iIntros "H"; wp_call; rewrite neg_repr; iAssumption.
  Qed.

  Global Instance Stdlib__fst__TCspec `{Encode A} `{Encode B} :
    pure_unary_spec Stdlib__fst (@fst A B).
  Proof.
    iIntros([??]???); iIntros "?"; wp_call; wp_continue; iAssumption.
  Qed.

  Global Instance Stdlib__snd__TCspec `{Encode A} `{Encode B} :
    pure_unary_spec Stdlib__snd (@snd A B).
  Proof.
    iIntros([??]???); iIntros "?"; wp_call; wp_continue; iAssumption.
  Qed.



  (* ------------------------------------------------------------------------ *)
  (* Pure binary fully-applied functions. *)

  Global Instance Stdlib__add__TCspec :
    forall (i j : Z), pure_binary_spec Stdlib__add Z.add i j.
  Proof. iIntros (?????)"H"; wp_call. by rewrite add_repr_repr. Qed.

  Global Instance Stdlib__sub__TCspec :
    forall (i j : Z), pure_binary_spec Stdlib__sub Z.sub i j.
  Proof. iIntros (?????)"H"; wp_call. by rewrite sub_repr_repr. Qed.

  Global Instance Stdlib__mul__TCspec :
    forall (i j : Z), pure_binary_spec Stdlib__mul Z.mul i j.
  Proof. iIntros (?????)"H"; wp_call. by rewrite mul_repr_repr. Qed.



  (* ------------------------------------------------------------------------ *)
  (* Pure binary partially-applied functions. *)

  Global Instance Stdlib__add__TCspec_1:
    pure_binary_partial_spec Stdlib__add Z.add.
  Proof.
    iIntros (????)"H"; wp_call.
    iApply "H". iIntros; wp.
    by rewrite add_repr_repr.
  Qed.

  Global Instance Stdlib__mul__TCspec_1:
    pure_binary_partial_spec Stdlib__mul Z.mul.
  Proof.
    iIntros (????)"H"; wp_call.
    iApply "H". iIntros; wp.
    by rewrite mul_repr_repr.
  Qed.

End Stdlib__specs.
