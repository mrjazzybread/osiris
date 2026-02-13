From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris.lang Require Import type_nel encode int notations.
From osiris.program_logic Require Import program_logic.
From osiris.logic Require Import list_z.

Local Notation VEta1 body :=
  (
    VClo [] $
         AnonFun "x" $
         body (EPath [ "x" ])
  ).
Local Notation VEta2 body :=
  (
    VClo [] $
         AnonFun "x" $
         EAnonFun (AnonFun "y"
         (body (EPath [ "x" ]) (EPath [ "y" ])))
  ).
Local Notation VEta3 body :=
  (
    VClo [] $
         AnonFun "x" $
         EAnonFun (AnonFun "y" $
         EAnonFun (AnonFun "z" $
                     (body (EPath [ "x" ]) (EPath [ "y" ]) (EPath [ "z" ]))))
  ).
Local Notation dummy := (VClo [] $ AnonFun "_" EUnsupported).

Section ExternalsDef.

  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Content of Externals used in [stdlib/int.ml]. *)

  Definition Externals__negint : val := VEta1 EIntNeg.
  Definition Externals__addint : val := VEta2 EIntAdd.

  Lemma add_spec :
    ⊢ iSpec τ[Z;Z] Externals__addint (λ i j (m : microvx), imp m {{ λ (n : Z), ⌜(n = i + j)%Z⌝ }}).
  Proof.
    rewrite iSpec_equation_2.
    iIntros (i).
    iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (j). iApply imp_please. iNext.
    iApply imp_EIntAdd.
    - instantiate (1:=(λ n', ⌜n' = i⌝)%I).
      iApply imp_EPath; auto.
    - instantiate (1:=(λ n', ⌜n' = j⌝)%I).
      iApply imp_EPath; auto.
    - iIntros "!>" (??) "-> ->". done.
  Qed.

  Definition Externals__subint : val := VEta2 EIntSub.

  Lemma sub_spec :
    ⊢ iSpec τ[Z;Z] Externals__subint (λ i j (m : microvx), imp m {{ λ (n : Z), ⌜(n = i - j)%Z⌝ }}).
  Proof.
    rewrite iSpec_equation_2.
    iIntros (i).
    iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (j). iApply imp_please. iNext.
    iApply imp_EIntSub.
    - instantiate (1:=(λ n', ⌜n' = i⌝)%I).
      iApply imp_EPath; auto.
    - instantiate (1:=(λ n', ⌜n' = j⌝)%I).
      iApply imp_EPath; auto.
    - iIntros "!>" (??) "-> ->". done.
  Qed.

  Definition Externals__mulint : val := VEta2 EIntMul.
  Definition Externals__divint : val := VEta2 EIntDiv.
  Definition Externals__modint : val := VEta2 EIntMod.
  Definition Externals__succint : val :=
    VEta1 (fun x => EIntAdd x (EInt 1)).
  Definition Externals__predint : val :=
    VEta1 (fun x => EIntSub x (EInt 1)).

  Definition Externals__lessthan : val := VEta2 EOpLt.
  Definition Externals__greaterthan : val := VEta2 EOpGt.
  Definition Externals__lessequal : val := VEta2 EOpLe.
  Definition Externals__greaterequal : val := VEta2 EOpGe.

  (* The following names are used in [stdlib/int.ml], but they are not supported
     yet: - %andint
          - %orint
          - %xorint
          - %lslint
          - %asrint
          - %lsrint
          - %floatofint
          - %intoffloat
          - caml_format_int
          - caml_hash *)

  (* ------------------------------------------------------------------------ *)

  (* On Booleans. *)

  Definition Externals__boolnot : val := VEta1 EBoolNeg.

  (* ------------------------------------------------------------------------ *)

  Definition Externals__revapply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "y") (EVar "x").

  Definition Externals__apply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "x") (EVar "y").

  Definition Externals__identity : val :=
    VClo [] $
         AnonFun "x" $ EVar "x".

  Definition Externals__ignore : val :=
    VClo [] $ AnonFun "_" $ EUnit.

  (* Comparison. *)
  Definition Externals__eq : val := VEta2 EOpEq.
  Definition Externals__ne : val := VEta2 EOpNe.

  (* ------------------------------------------------------------------------ *)

  (* On constructed types. *)

  Definition Externals__field0 : val :=
    VEta1 (λ (e : expr),
             ELet1 (PPair (PVar "x") PAny) e $
                   EVar "x").

  Definition Externals__field1 : val :=
    VEta1 (λ (e : expr),
             ELet1 (PPair PAny (PVar "x")) e $
                   EVar "x").

  (* ------------------------------------------------------------------------ *)
  (* Content of Externals used in [stdlib/array.ml]. *)

  Definition Externals__array_length : val := VEta1 EArrayLength.

  Lemma array_length_spec :
    ⊢ iSpec τ[array] Externals__array_length (λ a m, ∀ n, isArray a n -∗ imp m {{ λ n', ⌜n' = n⌝ }}).
  Proof.
    rewrite iSpec_equation_1.
    iIntros (a n) "#Harr".
    iApply imp_please. iNext.
    iApply imp_EArrayLength. iApply imp_EPath; auto.
  Qed.

  Definition Externals__array_get : val := VEta2 EArrayGet.

  Lemma array_get_spec :
    ⊢ iSpec τ[array;Z] Externals__array_get
        (λ a i m,
           ∀ (A : Type) (_ : Encode A) (_ : Inhabited A) n dq j (xs : list A),
           isArray a n -∗
           ▷ isSlice dq a j xs -∗
           ⌜j ≤ i⌝ -∗
           ⌜i - j < length xs⌝ -∗
           imp m {{ λ (v : A), ⌜v = xs !!! (i - j)⌝ ∗ isSlice dq a j xs }}).
  Proof.
    rewrite iSpec_equation_2.
    iIntros (a). iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (i A HencA HinhA n dq j xs) "#Harr Hslice %Hle %Hlt".
    iApply imp_please. iNext.
    iApply (imp_EArrayGet with "[] [] [] Harr Hslice").
    - iPureIntro; eassumption.
    - iPureIntro; assumption.
    - auto.
    - iApply imp_EPath; auto.
    - iApply imp_EPath; auto.
  Qed.

  Definition Externals__array_set : val := VEta3 EArraySet.

  Lemma array_set_spec `{Encode A}:
    ⊢ iSpec τ[array;Z;A] Externals__array_set
        (λ a i x m,
           ∀ n j (xs : list A) Φ,
           isArray a n -∗
           ▷ isSlice (DfracOwn 1) a j xs -∗
           Φ x -∗
           ⌜j ≤ i⌝ -∗
           ⌜i - j < length xs⌝ -∗
           imp m {{ λ (_ : unit), ∃ x, Φ x ∗ isSlice (DfracOwn 1) a j (<[i - j:=x]> xs) }}).
  Proof.
    rewrite iSpec_equation_2.
    iIntros (a). iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (i x n j xs Φ) "#Harr Hslice HΦ %Hle %Hlt".
    iApply imp_please. iNext.
    iApply (imp_EArraySet with "[] [] Harr Hslice").
    - iPureIntro; eassumption.
    - iPureIntro; assumption.
    - iApply imp_EPath; auto.
    - iApply imp_EPath; auto.
    - iApply imp_EPath; auto.
  Qed.

  Definition Externals__array_make : val := VEta2 EArrayMake.

  Lemma array_make_spec `{Encode A} :
    ⊢ iSpec τ[Z; A] Externals__array_make
        (λ n x m,
           ∀ Φ, ⌜0 ≤ n ≤ max_array⌝ -∗
                Φ x -∗
                imp m {{ λ a, ∃ x, Φ x ∗ ownArray a (replicate n x) }}).
  Proof.
    rewrite iSpec_equation_2.
    iIntros (n). iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (x Φ) "%hbounds HΦ".
    iApply imp_please; iNext.
    iApply imp_EArrayMake.
    - iPureIntro; assumption.
    - iApply imp_EPath; auto.
    - iApply imp_EPath; auto.
  Qed.

End ExternalsDef.
