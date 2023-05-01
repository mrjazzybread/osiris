From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

Require Import base lang sugar locations free eval step wp wp_tactics encode notations.

Section StdLib.
  Context `{!osirisGS_gen hlc Σ}.

  (* About integers. *)
  Definition Stdlib__add : val :=
    VClo EnvNil $
      AnonFun "x" $
      EFun "y" $
      EIntAdd (EVar "x") (EVar "y").

  (* About references. *)
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
      EFun "i" $
      EStore (EVar "x") (EVar "i").



  (* Putting everything together. *)
  Definition Stdlib :=
    VStruct $
      EnvCons "+" Stdlib__add $
      EnvCons "ref" Stdlib__ref $
      EnvCons "!" Stdlib__load $
      EnvCons ":=" Stdlib__store $
      EnvNil.



  (* Specifications : integers. *)
  Lemma Stdlib__add__spec s E:
    ∀ v1 v2 i1 i2,
    v1 = VInt (int.repr i1) →
    v2 = VInt (int.repr i2) →
    ⊢ WP call Stdlib__add v1 @s; E
         {{ λ v, WP call v v2 @s; E {{ λ v, ⌜v = VInt (int.repr (i1 + i2))⌝ }} }}.
  Proof.
    intros. subst. wp.
    wp_call.
    by rewrite int.add_repr_repr.
  Qed.


  (* Specifications : store. *)
  Lemma Stdlib__ref__spec v (s: stuckness) (E: coPset) :
    ⊢ WP call Stdlib__ref v @ s; E
           {{ λ vl, ∃ (ℓ: loc), ℓ ↦ v ∗ ⌜vl = VLoc ℓ ⌝ }}.
  Proof.
    wp_call. wp_ref l "[Hl _]".
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


  Opaque Stdlib__add.
  Opaque Stdlib__ref.
  Opaque Stdlib__load.
  Opaque Stdlib__store.
End StdLib.
