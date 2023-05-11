From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics tactics specifications.



(* This file is not yet finished. It aims to help understand what are the main
   difficulties associated to extending the approach of
   [theoories/weakestpre/specifications.v] to n-ary functions.

   The main elements discussed are:
   - reification of Coq types,
   - representation of the arrity of a function,
   - how to write specifications in this setup.

   Future ideas to discuss are:
   - how to prove the admitted inversion lemma,
   - how to reason on total applications,
   - how to reason on partial applications,
   - how to extend this approach to impure functions (•).
                (•) Especially : is it possible to get a
                    spec of type
                    [(A1 → Prop) → ... → (An → Prop) → iProp Σ → val → iProp Σ].
                    where:
                    - [Ai → Prop] is a pure condition on the arguments
                      (eg. their representability for integers),
                    - the first [iProp Σ] represents the resources needed at the
                      last aplpication.

   (+ an example would be nice.) *)



Section PureEncoder.
  (* The type of an n-ary function is of the form [A1 → ... → An → A0]. *)
  Inductive ntype : nat → Type :=
  | tyO: forall (T: Type), Encode T → ntype O
  | tyS: forall (T: Type) {n: nat} (nty: ntype n), Encode T → ntype (S n).

  (* Function to expand a compacted type. *)
  Fixpoint tycast n (ty: ntype n) : Type :=
    match ty with
    | tyO T _ => T
    | @tyS T n nty _ => T → (tycast n nty)
    end.


  (* Predicate to ensure that a n-ary function is of the expected type. *)
  Inductive nfun :
    forall (n: nat) (ty: ntype n), (tycast n ty) → Type :=
  | fnO: forall (T: Type) (t: T) {e},
      nfun O (tyO T e) t
  | fnS: forall n (T1: Type) ty (f: T1 → (tycast n ty)) {e}
      (h: forall t, nfun n ty (f t)),
      nfun (S n) (tyS T1 ty e) f.

  Lemma fnS_inv n ty T1 e f:
    nfun (S n) (tyS T1 ty e) f →
    forall t, nfun n ty (f t).
  Proof.
  (* The [inversion] tactic does not provide the requierd elements to move
     forward. *)
  Admitted.


  (* [nat] *)
  Compute (tycast O (tyO nat _)).
  (* [Z → nat → nat] *)
  Compute (tycast 2 (tyS Z (tyS nat (tyO nat _) _) _)).



  (* The following defines a function [f] and its type.
     They are used later as examples. *)
  Definition f_ty : Type := Z → nat → bool → bool → nat → nat.
  Definition reset n b := match b with
                         | true => O
                         | false => n
                         end.
  Definition f : f_ty :=
    fun _ => fun n => fun b1 => fun b2 => fun m =>
      (reset n b1) + (reset m b2).



  (* ------------------------------------------------------------------------ *)
  (* Step 1: fine a representation of [f_ty]. *)

  Class TCtest n (ty: ntype n) (T: Type) :=
    ok: tycast n ty = T.

  (* I volontarily restrict base types.
     Doing it here rather that in the definition of [ntype] lets adding new base
     types simply by adding instances to a typaclass, rather that altering
     definitions. *)
  Global Instance tc_test_O_nat:
    TCtest O (tyO nat Encode_nat) nat.
  Proof. reflexivity. Qed.
  Global Instance tc_test_O_bool:
    TCtest O (tyO bool Encode_bool) bool.
  Proof. reflexivity. Qed.
  Global Instance tc_test_O_val:
    TCtest O (tyO val Encode_val) val.
  Proof. reflexivity. Qed.

  (* Inductive cases. Once again, I only declare the instances I want to use. *)
  Global Instance tc_test_S_nat (T: Type) n `{!TCtest n ty T} :
    TCtest (S n) (tyS nat ty _) (nat → T).
  Proof.
    unfold TCtest.
    simpl. rewrite TCtest0. reflexivity. Qed.
  Global Instance tc_test_S_Z (T: Type) n `{!TCtest n ty T} :
    TCtest (S n) (tyS Z ty _) (Z → T).
  Proof.
    unfold TCtest.
    simpl. rewrite TCtest0. reflexivity. Qed.
  Global Instance tc_test_S_bool (T: Type) n `{!TCtest n ty T} :
    TCtest (S n) (tyS bool ty _) (bool → T).
  Proof.
    unfold TCtest.
    simpl. rewrite TCtest0. reflexivity. Qed.



  (* Actual computation; achieved throught a TC-guided proof-search. *)
  Definition tmp : { ty | tycast 5 ty = f_ty }.
  Proof. eexists _. apply ok. Defined.
  Definition m_ty : ntype 5 := proj1_sig tmp.

  Print m_ty.
  Compute (tycast 5 m_ty).



  Definition tmp' : { ty | tycast 2 ty = (nat → nat → nat) }.
  Proof. eexists _. apply ok. Defined.
  Definition m_addN : ntype 2 := proj1_sig tmp'.

  Compute (tycast 2 m_addN).



  (* ------------------------------------------------------------------------ *)
  (* Step 2: Prove that a dunction can be applied at least [n] times and has the
     correct type. *)

  Lemma addN_binary :
    nfun 2 m_addN Nat.add.
  Proof.
    repeat (apply fnS || intros).
    apply fnO.
  Qed.

  Lemma f_5ary :
    nfun 5 m_ty f.
  Proof.
    repeat (apply fnS || intros); apply fnO.
  Qed.



  (* ------------------------------------------------------------------------ *)
  (* Step 3: write the definition of what having some (pure for now) n-ary model
     means. *)

  (* TODO: replace the body of the [Fipoint] by a proper [match] *)
  Fixpoint specification_meaning  `{!osirisGS_gen hlc Σ} {n} ty
           (f: val) ff (P: nfun n ty ff) : iProp Σ.
  Proof.
    destruct ty as [T e | T n' ty' e ] eqn:E.
    - (* tyO T e => *)
      exact (⌜ f = e.(encode) ff ⌝%I).
    - (* tyS T ty e => *)
      assert (forall (t: T), nfun n' ty' (ff t)) as H.
      { by apply fnS_inv. }
      exact (
          (∀ s E t,
              let v := e.(encode) t in
              WP call f v @ s; E
                 {{ λ res, specification_meaning _ _ _ n' ty' res (ff t) (H _) }})%I).
  Defined.



  (* ------------------------------------------------------------------------ *)
  (* Examples on pure functions. *)

  (* TODO! *)



  (* ------------------------------------------------------------------------ *)
  (* Extensions to non-pure functions. *)

  (* TODO! *)



  (* ------------------------------------------------------------------------ *)
  (* Examples on on-pure functions. *)

  (* TODO! *)
End PureEncoder.
