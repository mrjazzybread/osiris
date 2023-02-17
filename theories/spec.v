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

(* Let us view implication as an ordering [p1 ≼ p2]. *)

Definition leq p1 p2 :=
  ∀ t φ, p1 t φ → p2 t φ.

Local Infix "≼" := leq (at level 70, no associativity).

(* The greatest fixed point is constructed as follows. The existential
   quantifier can be read here as an infinite union. The greatest fixed
   point is the union of all post fixed points, where we say that [p] is
   a post fixed point if [p ≼ ff p] holds. *)

Definition spec_mfix : T → spec A :=
  λ t φ, ∃ p, p t φ ∧ p ≼ ff p.

(* By definition, [mspec_fix] is greater than any post fixed point.
   So, if it is a fixed point (which we will prove below), then it
   must be the greatest fixed point. This is the coinduction principle. *)

Lemma spec_coinduction p :
  p ≼ ff p →
  p ≼ spec_mfix.
Proof.
  intros post t φ ptφ. unfold spec_mfix. eauto.
Qed.

(* The transformer [ff] must be monotone. *)

Definition monotone ff :=
  ∀ p1 p2, p1 ≼ p2 → ff p1 ≼ ff p2.

Variable monotone_ff :
  monotone ff.

(* [spec_mfix] is itself a post fixed point. *)

Lemma deconstruction :
  spec_mfix ≼ ff spec_mfix.
Proof.
  intros t φ.
  intros (p & ptφ & propagation).
  eapply (monotone_ff p).
  { eauto using spec_coinduction. }
  { eauto. }
Qed.

Lemma deconstruction_expanded t φ :
  spec_mfix t φ → ff spec_mfix t φ.
Proof.
  eauto using deconstruction.
Qed.

(* [spec_mfix] is also a pre fixed point. *)

Lemma construction :
  ff spec_mfix ≼ spec_mfix.
Proof.
  intros t φ.
  intros Hff.
  (* We have just one witness at hand, namely [ff mspec_fix]. *)
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

(* Therefore, [spec_mfix] is a fixed point. *)

Lemma fixed_point :
  spec_mfix = ff spec_mfix.
Proof.
  extensionality t. extensionality φ.
  apply propositional_extensionality.
  split; eauto using construction, deconstruction.
Qed.

End Fix.

Opaque spec_mfix.

Global Instance spec_monad_fix :
  MonadFix spec.
Proof.
  constructor.
  exact @spec_mfix.
Defined.

Global Instance spec_monad_fix_laws :
  MonadFixLaws spec_monad_fix.
Print MonadFixLaws.
Proof.
  pose (mleq := (λ (A : Type) (_ : relation A), @eq (spec A))).
  eapply (Build_MonadFixLaws _ mleq).
  unfold respectful.
  unfold mleq.
  unfold mfix; simpl.
  intros T A ff t t' ?. subst t'.
  rewrite <- fixed_point. 2: admit. (* problem! *)
  reflexivity.
Abort.

(* ------------------------------------------------------------------------ *)
