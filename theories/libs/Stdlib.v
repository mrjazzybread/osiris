From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics notations specifications.

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

Section StdLib__code.
  Context `{!osirisGS_gen hlc Σ}.

  Section Arithmetic_operations.
    Definition Stdlib__add : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EIntAdd (EVar "x") (EVar "y").
    Definition Stdlib__sub : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EIntSub (EVar "x") (EVar "y").
    Definition Stdlib__mul : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EIntMul (EVar "x") (EVar "y").
    Definition Stdlib__div : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EIntDiv (EVar "x") (EVar "y").
    Definition Stdlib__mod : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EIntMod (EVar "x") (EVar "y").


    Definition Stdlib__neg : val :=
      VClo EnvNil $
           AnonFun "x" $
           EIntNeg (EVar "x").
  End Arithmetic_operations.



  Section Arithmetic_comparison.
    Definition Stdlib__eq : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EOpEq (EVar "x") (EVar "y").
    Definition Stdlib__lt : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EOpLt (EVar "x") (EVar "y").
    Definition Stdlib__ge : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EOpGe (EVar "x") (EVar "y").
    Definition Stdlib__gt : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EOpGt (EVar "x") (EVar "y").
  End Arithmetic_comparison.



  Section Stdlib__store.
    Definition Stdlib__ref : val :=
      VClo EnvNil $
           AnonFun "e" $
           ERef (EVar "e").

    Definition Stdlib__load : val :=
      VClo EnvNil $
           AnonFun "x" $
           ELoad (EVar "x").

    Definition Stdlib__store : val :=
      VClo EnvNil $
           AnonFun "x" $
           EAnonFun $ AnonFun "i" $
           EStore (EVar "x") (EVar "i").
  End Stdlib__store.



  Section Stdlib__tuples.
    Definition Stdlib__fst : val :=
      VClo EnvNil $
           AnonFun "x" $
           EMatch
           (EVar "x")
           (BrCons
              (Branch
                 (PTuple (PCons (PVar "l") (PCons (PVar "r") PNil)))
                 (EVar "l"))
              BrNil).

    Definition Stdlib__snd : val :=
      VClo EnvNil $
           AnonFun "x" $
           EMatch
           (EVar "x")
           (BrCons
              (Branch
                 (PTuple (PCons (PVar "l") (PCons (PVar "r") PNil)))
                 (EVar "r"))
              BrNil).
  End Stdlib__tuples.



  Section Stdlib__bool.
    Definition Stdlib__not : val :=
      VClo EnvNil $
           AnonFun "b" $
           EIfThenElse
           (EVar "b")
           (EBool false)
           (EBool true).
  End Stdlib__bool.



  (* Putting everything together. *)
  Definition Stdlib :=
    VStruct $
      EnvCons "-" Stdlib__sub $
      EnvCons "+" Stdlib__add $
      EnvCons "*" Stdlib__mul $
      EnvCons "~-" Stdlib__neg $
      EnvCons "=" Stdlib__eq $
      EnvCons "<" Stdlib__lt $
      EnvCons ">=" Stdlib__ge $
      EnvCons ">" Stdlib__gt $
      EnvCons "ref" Stdlib__ref $
      EnvCons "!" Stdlib__load $
      EnvCons ":=" Stdlib__store $
      EnvCons "fst" Stdlib__fst $
      EnvCons "snd" Stdlib__snd $
      EnvCons "not" Stdlib__not $
      EnvNil.
End StdLib__code.



Section Stdlib__specs.
  Context `{!osirisGS_gen hlc Σ}.


  Section Stdlib__spec__arithmetic.
    Lemma Stdlib__add__spec s E:
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        ⊢ WP call Stdlib__add v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 + i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite int.add_repr_repr.
    Qed.

    Lemma Stdlib__sub__spec s E:
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        ⊢ WP call Stdlib__sub v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 - i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite int.sub_repr_repr.
    Qed.

    Lemma Stdlib__mul__spec s E:
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        ⊢ WP call Stdlib__mul v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 * i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite int.mul_repr_repr.
    Qed.

    Lemma Stdlib__neg__spec s E:
      ∀ v1 (i1: Z),
        v1 = encode i1 →
        ⊢ WP call Stdlib__neg v1 @s; E
             {{ λ v, ⌜v = encode (- i1)%Z⌝ }}.
    Proof.
      intros. subst. wp.
      wp_call. iPureIntro.
      by rewrite int.neg_repr.
    Qed.
  End Stdlib__spec__arithmetic.



  Section Stdlib__spec__arith_comp.
    Lemma Stdlib__eq__spec s E :
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        (int.min_signed ≤ i1 ≤ int.max_signed)%Z →
        (int.min_signed ≤ i2 ≤ int.max_signed)%Z →
        ⊢ WP call Stdlib__eq v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 =? i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite int.eq_repr_repr.
    Qed.

    Lemma Stdlib__lt__spec s E :
      ∀ v1 v2 (i1 i2: Z),
        v1 = encode i1 →
        v2 = encode i2 →
        (int.min_signed ≤ i1 ≤ int.max_signed)%Z →
        (int.min_signed ≤ i2 ≤ int.max_signed)%Z →
        ⊢ WP call Stdlib__lt v1 @s; E
             {{ λ v, WP call v v2 @s; E
                        {{ λ v, ⌜v = encode (i1 <? i2)%Z⌝ }} }}.
    Proof.
      intros. subst. wp.
      wp_call.
      by rewrite int.lt_repr_repr.
    Qed.
  End Stdlib__spec__arith_comp.



  Section Stdlib__spec__store.
    Lemma Stdlib__ref__spec v (s: stuckness) (E: coPset) :
      ⊢ WP call Stdlib__ref v @ s; E
           {{ λ vl, ∃ (ℓ: loc), ℓ ↦ v ∗ ⌜vl = VLoc ℓ ⌝ }}.
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
      iIntros (ϕ) "[-> Hℓ] Hϕ".
      wp_call. iApply "Hϕ". clear ϕ.
      wp_call.
      wp_store "Hℓ". by iSplit.
    Qed.
  End Stdlib__spec__store.



  Section Stdlib__spec__tuples.
    Lemma Stdlib__fst__spec v1 v2 s E :
      {{{ ⌜ True ⌝ }}}
        call Stdlib__fst (VTuple (VCons v1 (VCons v2 VNil))) @ s; E
      {{{ v, RET v; ⌜ v = v1 ⌝ }}}.
    Proof.
      iIntros (ϕ)"_ Hϕ".
      wp_call.
      wp_continue.
      by iApply "Hϕ".
    Qed.

    Lemma Stdlib__snd__spec v1 v2 s E :
      {{{ ⌜ True ⌝ }}}
        call Stdlib__snd (VTuple (VCons v1 (VCons v2 VNil))) @ s; E
     {{{ v, RET v; ⌜ v = v2 ⌝ }}}.
    Proof.
      iIntros (ϕ)"_ Hϕ".
      wp_call.
      wp_continue.
      by iApply "Hϕ".
    Qed.
  End Stdlib__spec__tuples.


  (* Lemmas to better handle fully-applied functions of the standart library. *)
  Lemma Stdlib__load__spec_tac vl ℓ v s E :
    ⊢ ∀ ϕ, ⌜ vl = VLoc ℓ ⌝ -∗
    ℓ ↦ v -∗
    (ℓ ↦ v -∗ ϕ v) -∗ (* TODO: add a later to this premice (will require to change
              [wp_covariant]. *)
    WP call Stdlib__load vl @ s; E {{ λ v, ϕ v }}.
  Proof.
    iIntros(ϕ) "-> Hℓ Hv".
    iApply (wp_covariant with "[Hℓ]").
    { iApply (Stdlib__load__spec with "[$Hℓ]"); first done.
      iNext. iIntros. iAssumption. }
    iIntros (?) "[-> Hℓ]".
    iApply ("Hv" with "Hℓ").
  Qed.

  (* TODO: same as above: get a later in the premice. *)
  Lemma Stdlib__ref__spec_tac {A} v s E ϕ (k: free A) :
    ⊢ (∀ ℓ vl, ⌜vl = VLoc ℓ⌝ -∗ ℓ ↦ v -∗ WP k @ s; E {{ ϕ }}) -∗
    WP call Stdlib__ref v {{ λ (vl: val), WP k @s; E {{ ϕ }} }}.
  Proof.
    iIntros "H".
    iApply wp_covariant.
    { iApply Stdlib__ref__spec. }
    iIntros (vl)"(%ℓ & Hℓ & ->)".
    by iApply "H".
  Qed.

  Lemma Stdlib__store__spec_tac ℓ v v' ϕ s E :
    ℓ ↦ v -∗
    ▷ (ℓ ↦ v' -∗ ϕ VUnit) -∗
    WP call Stdlib__store (VLoc ℓ) @ s; E
         {{ vpartial, WP call vpartial v' @ s; E {{ v, ϕ v }} }}.
  Proof.
    iIntros "Hℓ Hccl".
    iApply (Stdlib__store__spec with "[$Hℓ //]").
    iNext.
    iIntros (vstore) "Hstore".
    iApply (wp_covariant with "Hstore").
    iIntros(?)"[-> Hℓ]".
    iApply ("Hccl" with "Hℓ").
  Qed.

  Lemma Stdlib__fst__spec_tac s E v v1 v2 ϕ :
    v = VTuple (VCons v1 (VCons v2 VNil)) →
    ▷ ϕ v1 -∗
    WP call Stdlib__fst v @ s; E {{ ϕ }}.
  Proof.
    iIntros (->) "Hϕ".
    iApply ((Stdlib__fst__spec v1 v2 s E ϕ) with "[//]").
    iNext. iIntros (?->).
    iAssumption.
  Qed.

  Lemma Stdlib__snd__spec_tac s E v v1 v2 ϕ :
    v = VTuple (VCons v1 (VCons v2 VNil)) →
    ▷ ϕ v2 -∗
    WP call Stdlib__snd v @ s; E {{ ϕ }}.
  Proof.
    iIntros (->)"Hϕ".
    iApply ((Stdlib__snd__spec v1 v2 s E ϕ) with "[//]").
    iNext. iIntros (?->).
    iAssumption.
  Qed.



  Global Instance Stdlib__not__spec : pure_unary_spec Stdlib__not negb.
  Proof. iIntros ([] s E φ); iIntros "H"; wp_call; iAssumption. Qed.

  Global Instance Stdlib__neg__spec' : pure_unary_spec Stdlib__neg Z.opp.
  Proof.
    iIntros (i s E φ); iIntros "H"; wp_call; rewrite int.neg_repr; iAssumption.
  Qed.

End Stdlib__specs.

Global Opaque Stdlib__not.
Global Opaque Stdlib__neg.
Global Opaque Stdlib__mul.
Global Opaque Stdlib__add.
Global Opaque Stdlib__add.
Global Opaque Stdlib__ref.
Global Opaque Stdlib__load.
Global Opaque Stdlib__store.
Global Opaque Stdlib__fst.
Global Opaque Stdlib__snd.



(* -------------------------------------------------------------------------- *)

(* The rest of the file defines a tactic to automatically reduce calls to
   functions of the standard library. *)

Lemma binop `{!osirisGS_gen hlc Σ} s E :
  ∀ op (f: Z → Z → val) (i1 i2: Z) φ,
    let v1 := encode i1 in
    let v2 := encode i2 in
    (⊢ WP call op v1 @ s; E
          {{ λ vpartial, WP call vpartial v2 @ s; E
                            {{ λ res, ⌜ res  = f i1 i2 ⌝ }} }}) →
    φ (f i1 i2) -∗
    WP call op v1 @ s; E {{ λ vpartial,
                           WP call vpartial v2 @ s; E
                              {{ φ }} }}.
Proof.
  iIntros (op f i1 i2 φ v1 v2 op_spec) "Hφ".
  iPoseProof op_spec as "Hop_spec".
  iApply (wp_covariant with "Hop_spec").
  iIntros (v) "Hv".
  iApply (wp_covariant with "Hv").
  iIntros (?->).
  iExact "Hφ".
Qed.





(* Shadow the standart [wp] tactic to automatically deal with operations. *)
Ltac wp :=
  iStartProof; cbn;
  repeat
    lazymatch goal with
    | |- environments.envs_entails _ (▷ _) => iNext
    | |- environments.envs_entails
          _
          (wp _ _ (call Stdlib__neg _) _) => apply tc_change_goal
    | |- environments.envs_entails
          _
          (wp _ _ (call Stdlib__not _) _) => apply tc_change_goal
    | |- environments.envs_entails
          ?Δ
          (wp ?s ?E (call Stdlib__fst ?v) ?φ) =>
        apply (tac_change_goal
                  Δ _ _
                  (Stdlib__fst__spec_tac _ _ _ _ _ _ eq_refl));
        iNext; wp_continue
    | |- environments.envs_entails
          ?Δ
          (wp ?s ?E (call Stdlib__snd ?v) ?φ) =>
        apply (tac_change_goal
                  Δ _ _
                  (Stdlib__snd__spec_tac _ _ _ _ _ _ eq_refl));
        iNext; wp_continue
    | |- environments.envs_entails
          _
          (wp _ _ (call Stdlib__mul ?v1)
              (λ vpartial, wp _ _ (call vpartial ?v2) ?φ )) =>
        apply (tac_change_goal
                  _ _ _
                  (binop
                     _ _ _ (fun i1 i2 => encode (i1 * i2)%Z) _ _ _
                     (Stdlib__mul__spec _ _ _ _ _ _ eq_refl eq_refl)))
    | |- environments.envs_entails
          _
          (wp _ _ (call Stdlib__sub ?v1)
              (λ vpartial, wp _ _ (call vpartial ?v2) ?φ )) =>
        apply (tac_change_goal
                  _ _ _
                  (binop
                     _ _ _ (fun i1 i2 => encode (i1 - i2)%Z) _ _ _
                     (Stdlib__sub__spec _ _ _ _ _ _ eq_refl eq_refl)))
    | |- environments.envs_entails
          _
          (wp _ _ (call Stdlib__add ?v1)
              (λ vpartial, wp _ _ (call vpartial ?v2) ?φ )) =>
        apply (tac_change_goal
                  _ _ _
                  (binop
                     _ _ _ (fun i1 i2 => encode (i1 + i2)%Z) _ _ _
                     (Stdlib__add__spec _ _ _ _ _ _ eq_refl eq_refl)))
    | _ => wp_step
    end.
