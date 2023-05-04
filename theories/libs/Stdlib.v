From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang encode.
From osiris.semantics Require Import sugar locations free eval step notations.
From osiris.weakestpre Require Import wp wp_tactics notations.

Section StdLib.
  Context `{!osirisGS_gen hlc Σ}.

  (* About integers. *)
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
      EAnonFun $ AnonFun "i" $
      EStore (EVar "x") (EVar "i").


  (* About tuples *)
  Definition Stdlib__fst : val :=
    VClo EnvNil $
      AnonFun "x" $
      EMatch
        (EVar "x")
        (BrCons
           (Branch (PTuple (PCons (PVar "l") (PCons (PVar "r") PNil))) (EVar "l"))
        BrNil).

  Definition Stdlib__snd : val :=
    VClo EnvNil $
      AnonFun "x" $
      EMatch
        (EVar "x")
        (BrCons
           (Branch (PTuple (PCons (PVar "l") (PCons (PVar "r") PNil))) (EVar "r"))
        BrNil).



  (* Putting everything together. *)
  Definition Stdlib :=
    VStruct $
      EnvCons "-" Stdlib__sub $
      EnvCons "+" Stdlib__add $
      EnvCons "ref" Stdlib__ref $
      EnvCons "!" Stdlib__load $
      EnvCons ":=" Stdlib__store $
      EnvCons "fst" Stdlib__fst $
      EnvCons "snd" Stdlib__snd $
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

  Lemma Stdlib__sub__spec s E:
    ∀ v1 v2 i1 i2,
    v1 = VInt (int.repr i1) →
    v2 = VInt (int.repr i2) →
    ⊢ WP call Stdlib__sub v1 @s; E
         {{ λ v, WP call v v2 @s; E {{ λ v, ⌜v = VInt (int.repr (i1 - i2))⌝ }} }}.
  Proof.
    intros. subst. wp.
    wp_call.
    by rewrite int.sub_repr_repr.
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


  Lemma Stdlib__fst__spec v1 v2 s E :
    {{{ ⌜ True ⌝ }}}
      call Stdlib__fst (VTuple (VCons v1 (VCons v2 VNil))) @ s; E
    {{{ v, RET v; ⌜ v = v1 ⌝ }}}.
  Proof.
    iIntros (ϕ)"_ Hϕ".
    wp_call.
    by iApply "Hϕ".
  Qed.

  Lemma Stdlib__snd__spec v1 v2 s E :
    {{{ ⌜ True ⌝ }}}
      call Stdlib__snd (VTuple (VCons v1 (VCons v2 VNil))) @ s; E
    {{{ v, RET v; ⌜ v = v2 ⌝ }}}.
  Proof.
    iIntros (ϕ)"_ Hϕ".
    wp_call.
    by iApply "Hϕ".
  Qed.

  Opaque Stdlib__sub.
  Opaque Stdlib__add.
  Opaque Stdlib__ref.
  Opaque Stdlib__load.
  Opaque Stdlib__store.
  Opaque Stdlib__fst.
  Opaque Stdlib__snd.
End StdLib.

Section Stdlib_Lemmas.
  Context `{!osirisGS_gen hlc Σ}.

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
    ⌜ v = VTuple (VCons v1 (VCons v2 VNil)) ⌝ -∗
    ▷ ϕ v1 -∗
    WP call Stdlib__fst v @ s; E {{ ϕ }}.
  Proof.
    iIntros "-> Hϕ".
    iApply ((Stdlib__fst__spec v1 v2 s E ϕ) with "[//]").
    iNext. iIntros (?->).
    iAssumption.
  Qed.

  Lemma Stdlib__snd__spec_tac s E v v1 v2 ϕ :
    ⌜ v = VTuple (VCons v1 (VCons v2 VNil)) ⌝ -∗
    ▷ ϕ v2 -∗
    WP call Stdlib__snd v @ s; E {{ ϕ }}.
  Proof.
    iIntros "-> Hϕ".
    iApply ((Stdlib__snd__spec v1 v2 s E ϕ) with "[//]").
    iNext. iIntros (?->).
    iAssumption.
  Qed.

End Stdlib_Lemmas.

(* TODO:
Section Stdlib_tactics.
  Context `{!osirisGS_gen hlc Σ}.
End Stdlib_tactics. *)
