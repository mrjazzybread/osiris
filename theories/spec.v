From Coq.Logic Require Import FunctionalExtensionality PropExtensionality.
From stdpp Require Import base.
Require Import monads.

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

Global Instance spec_monad : Monad spec :=
  { ret := @spec_ret; bind := @spec_bind }.

Arguments spec_monad /.

Global Instance eq1_spec : Eq1 spec :=
  λ (A : Type), @eq (spec A).

Arguments eq1_spec /.

Global Instance spec_monad_laws :
  MonadLaws _.
Proof.
  constructor; intros; simpl; extensionality φ; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The hard failure combinator, whose precondition is [False]. *)

Definition spec_fail {A} : spec A :=
  λ (φ : A → Prop),
    False.

Global Instance spec_monad_zero : MonadZero spec :=
  { mzero := @spec_fail }.

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

Definition spec_mleq (m1 m2 : spec A) :=
  ∀ φ, m1 φ → m2 φ.

Definition leq p1 p2 :=
  ∀ t, spec_mleq (p1 t) (p2 t).

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
  { eapply propagation. exact ptφ. }
Qed.

Lemma deconstruction_expanded t φ :
  spec_mfix t φ → ff spec_mfix t φ.
Proof.
  intros. eapply deconstruction. eauto.
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
  intros. eapply construction. eauto.
Qed.

(* Therefore, [spec_mfix] is a fixed point. *)

Lemma fixed_point_expanded t :
  spec_mfix t = ff spec_mfix t.
Proof.
  extensionality φ.
  apply propositional_extensionality.
  split; eauto using construction_expanded, deconstruction_expanded.
Qed.

Lemma fixed_point :
  spec_mfix = ff spec_mfix.
Proof.
  extensionality t. eapply fixed_point_expanded.
Qed.

End Fix.

Opaque spec_mfix.

Global Instance spec_monad_fix : MonadFix spec :=
  { mfix := @spec_mfix }.

Global Instance spec_monad_fix_laws :
  MonadFixLaws spec_monad_fix.
Proof.
  eapply (@Build_MonadFixLaws _ _ (@spec_mleq));
  unfold spec_mleq;
  unfold mfix; simpl;
  eauto using fixed_point.
Defined.

Global Instance spec_monad_fix_coinduction :
  MonadFixCoinduction spec_monad_fix spec_monad_fix_laws.
Proof.
  constructor. unfold mleq; simpl.
  intros. eapply spec_coinduction. eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* An iteration combinator [iter] can be derived from [mfix]. *)

Section Iter.

Context {R I : Type}.
Context (body : I → spec (I + R)).

Definition spec_iter_body (self : I → spec R) : I → spec R :=
  λ (i : I),
    (* Evaluate [body] out of the state [i]. *)
    bind (body i) (λ (signal : I + R),
      match signal with
      | inl i =>
          (* If the body yields a new state [i], continue. *)
          self i
      | inr r =>
          (* If the body yields a result [r], return this result. *)
          ret r
      end).

Definition spec_iter : I → spec R :=
  spec_mfix spec_iter_body.

(* TODO move *)
Lemma spec_mleq_reflexive {A} (m : spec A) :
  spec_mleq m m.
Proof.
  unfold spec_mleq. eauto.
Qed.

(* TODO prove and move *)
Lemma spec_mleq_bind {A B} (m1 m2 : spec A) (f1 f2 : A → spec B) :
  spec_mleq m1 m2 →
  (∀ a, spec_mleq (f1 a) (f2 a)) →
  spec_mleq (spec_bind m1 f1) (spec_bind m2 f2).
Proof.
Admitted.

Lemma monotone_spec_iter_body :
  monotone spec_iter_body.
Proof.
  unfold monotone, leq. intros self1 self2 ?.
  unfold spec_iter_body.
  intros i.
  eapply spec_mleq_bind.
  { eapply spec_mleq_reflexive. }
  intros signal. destruct signal.
  { eauto. }
  { eapply spec_mleq_reflexive. }
Qed.

End Iter.

Global Instance monaditer_spec : MonadIter spec :=
  { iter := @spec_iter }.

Global Instance monadskip_spec : MonadSkip spec :=
  { skip := (λ {A} (m : spec A), m) }.

Global Instance monaditerlaws_spec :
  MonadIterLaws _ _ _.
Proof.
  constructor.
  unfold iter, monaditer_spec.
  unfold skip, monadskip_spec.
  simpl.
  unfold spec_iter.
  intros.
  rewrite fixed_point_expanded; [ | eapply monotone_spec_iter_body ].
  unfold spec_iter_body at 1.
  reflexivity.
Qed.
