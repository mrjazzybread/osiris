From Coq.Logic Require Import FunctionalExtensionality PropExtensionality.
From ExtLib.Structures Require Export Monads MonadLaws.
From stdpp Require Import base.

(* ------------------------------------------------------------------------ *)

(* The specification monad. *)

Definition spec A :=
  (A → Prop) → Prop.

(* ------------------------------------------------------------------------ *)

(* The monadic combinators. *)

Definition spec_ret {A} : A → spec A :=
  λ (a : A) (φ : A → Prop),
    φ a.

Definition spec_bind {A B} (m : spec A) (f : A → spec B) : spec B :=
  λ (φ : B → Prop),
    m (λ a, f a φ).

Global Instance spec_monad :
  Monad spec.
Proof.
  constructor.
  exact @spec_ret.
  exact @spec_bind.
Defined.

Global Instance spec_monad_laws :
  MonadLaws spec_monad.
Proof.
  constructor; intros; extensionality φ; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The hard failure combinator, whose precondition is [False]. *)

Definition spec_fail {A} : spec A :=
  λ (φ : A → Prop),
    False.

Global Instance spec_monad_zero :
  MonadZero spec.
Proof.
  constructor.
  exact @spec_fail.
Defined.

Global Instance spec_monad_zero_laws :
  MonadZeroLaws spec_monad spec_monad_zero.
Proof.
  constructor; intros; extensionality φ; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The greatest fixed point combinator. *)

Section Fix.

Context {T A : Type}.
Variable ff  : (T → spec A) → (T → spec A).

Implicit Type t : T.
Implicit Type φ : A → Prop.
Implicit Type p : T → spec A.

Definition leq p1 p2 :=
  ∀ t φ, p1 t φ → p2 t φ.

Local Infix "≼" := leq (at level 70, no associativity).

Definition monotone ff :=
  ∀ p1 p2, p1 ≼ p2 → ff p1 ≼ ff p2.

Definition spec_mfix : T → spec A :=
  λ t φ, ∃ p, p t φ ∧ p ≼ ff p.

Variable monotone_ff :
  monotone ff.

Lemma deconstruction :
  spec_mfix ≼ ff spec_mfix.
Proof.
  intros t φ.
  intros (p & ptφ & propagation).
  eapply (monotone_ff p).
  { intros t' φ'. unfold spec_mfix. eauto. }
  { eauto. }
Qed.

Lemma deconstruction_expanded t φ :
  spec_mfix t φ → ff spec_mfix t φ.
Proof.
  eauto using deconstruction.
Qed.

Lemma construction :
  ff spec_mfix ≼ spec_mfix.
Proof.
  intros t φ.
  intros Hff.
  (* We have just one witness at hand. *)
  eexists. split; [ eauto |].
  (* Miracle! The goal now looks like [deconstruction]. *)
  clear t Hff φ.
  eauto using monotone_ff, deconstruction.
Qed.

Lemma construction_expanded t φ :
  ff spec_mfix t φ → spec_mfix t φ.
Proof.
  eauto using construction.
Qed.

Lemma fixed_point :
  spec_mfix = ff spec_mfix.
Proof.
  extensionality t. extensionality φ.
  apply propositional_extensionality.
  split; eauto using construction, deconstruction.
Qed.

End Fix.

Opaque spec_mfix.

(* ------------------------------------------------------------------------ *)
