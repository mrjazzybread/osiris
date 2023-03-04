From Coq.Logic Require Import FunctionalExtensionality PropExtensionality.
From Coq.Logic Require Import ProofIrrelevance ProofIrrelevanceFacts.
Module P := ProofIrrelevanceTheory(ProofIrrelevance).
From stdpp Require Import base.
Require Import monads.

Set Warnings "-notation-overridden".

(* ------------------------------------------------------------------------ *)

(* The specification monad. *)

(* A "computation" in this monad is not executable; it is a specification.

   An inhabitant of the type type [(A → Prop) → Prop] can be understood as a
   predicate transformer that maps a postcondition of type [A → Prop] to a
   precondition of type [Prop]. It can also be understood as a set of
   postconditions. *)

(* We restrict our attention to specifications [m] that are upward-closed,
   that is, such that [m φ] implies [m φ'] when [φ] implies [φ'].

   The need for this property shows up in the proof of [spec_leq_bind]. To
   argue that [bind] is monotone in its second argument, we need the first
   argument (a specification) to be upward-closed. *)

Definition spec A :=
  { m : (A → Prop) → Prop
  | ∀ (φ φ' : A → Prop), (∀ a, φ a → φ' a) → m φ → m φ' }.

(* ------------------------------------------------------------------------ *)

(* An important notation. *)

(* [m ∋ φ] means that the specification [m], viewed as a set of
   postconditions, contains the postcondition [φ].

   It can also be read as stating that [m], viewed as a computation,
   admits the postcondition [φ]. Thus, it is like a [wp] judgement
   in Iris. *)

Notation "m ∋ φ" :=
  (proj1_sig m φ) (at level 70).

(* ------------------------------------------------------------------------ *)

(* The consequence rule. *)

(* The judgement [m ∋ φ] is covariant in [φ]. *)

Lemma exploit_upward_closed {A} (m : spec A) :
  ∀ (φ φ' : A → Prop), (∀ a, φ a → φ' a) → m ∋ φ → m ∋ φ'.
Proof.
  destruct m as (m & Hm). simpl. exact Hm.
Qed.

(* A bidirectional version of the previous lemma. *)

Lemma descend_post {A} (m : spec A) (φ φ' : A → Prop) :
  (∀ a, φ a ↔ φ' a) →
  m ∋ φ ↔ m ∋ φ'.
Proof.
  intros H. split; intros Hm.
  { eapply exploit_upward_closed; [ | eapply Hm ].
    intros a. specialize (H a). tauto. }
  { eapply exploit_upward_closed; [ | eapply Hm ].
    intros a. specialize (H a). tauto. }
Qed.

(* Auxiliary lemmas. *)

Local Lemma descend_forall {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) →
  (∀ a, P a) ↔ (∀ a, Q a).
Proof.
  firstorder.
Qed.

Local Lemma descend_exists {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) →
  (∃ a, P a) ↔ (∃ a, Q a).
Proof.
  firstorder.
Qed.

(* ------------------------------------------------------------------------ *)

(* Equality of specifications. *)

(* To prove that two specifications are equal, it suffices to prove that
   they have the same inhabitants. *)

Lemma prove_spec_eq {A} (m1 m2 : spec A) :
  (∀ φ, (m1 ∋ φ) = (m2 ∋ φ)) →
  m1 = m2.
Proof.
  destruct m1 as (m1 & Hm1).
  destruct m2 as (m2 & Hm2).
  simpl. intros.
  apply P.subset_eq_compat. (* This is proof irrelevance. *)
  extensionality φ. eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The monadic combinators. *)

Program Definition spec_ret {A} : A → spec A :=
  λ (a : A) (φ : A → Prop), φ a.
Next Obligation.
  intros. simpl. eauto.
Defined.

Program Definition spec_bind {A B} (m : spec A) (f : A → spec B) : spec B :=
  λ (φ : B → Prop), m ∋ (λ a, f a ∋ φ).
Next Obligation.
  intros. simpl.
  destruct m as (m & Hm). simpl.
  intros φ φ' Hφφ'.
  intros H.
  eapply Hm; [ clear H Hm | eapply H ].
  eauto using exploit_upward_closed.
Defined.

Global Instance spec_monad : Monad spec :=
  { ret := @spec_ret; bind := @spec_bind }.

Global Instance spec_monad_laws :
  MonadLaws _.
Proof.
  constructor; intros; simpl;
  eapply prove_spec_eq;
  unfold spec_bind, spec_ret; simpl;
  reflexivity.
Qed.

Lemma unfold_spec_ret {A} (a : A) (φ : A → Prop) :
  (ret a ∋ φ) = φ a.
Proof.
  reflexivity.
Qed.

Lemma unfold_spec_bind {A B} (m : spec A) (f : A → spec B) (φ : B → Prop) :
  (bind m f ∋ φ) = (m ∋ (λ a, f a ∋ φ)).
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The hard failure combinator, whose precondition is [False]. *)

Program Definition spec_fail {A} : spec A :=
  λ (φ : A → Prop), False.
Next Obligation.
  intros. simpl. tauto.
Qed.

Global Instance spec_monad_zero : MonadZero spec :=
  { mzero := @spec_fail }.

Global Instance spec_monad_zero_laws :
  MonadZeroLaws spec_monad spec_monad_zero.
Proof.
  constructor; intros; simpl;
  eapply prove_spec_eq;
  unfold spec_bind, spec_fail; simpl;
  reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* A partial order on specifications. *)

Definition spec_leq {A} (m1 m2 : spec A) :=
  ∀ φ, m1 ∋ φ → m2 ∋ φ.

Definition pointwise_spec_leq {T A} (f1 f2 : T → spec A) :=
  ∀ t, spec_leq (f1 t) (f2 t).

Module Notations.
  Infix "≤" := spec_leq (at level 70, no associativity).
  Infix "≼" := pointwise_spec_leq (at level 70, no associativity).
End Notations.

Import Notations.

(* This is a partial order. *)

Global Instance preorder_spec_leq {A} : PreOrder (@spec_leq A).
Proof.
  constructor.
  { intros m. unfold spec_leq. eauto. }
  { intros m1 m2 m3. unfold spec_leq. eauto. }
Qed.

Lemma spec_leq_antisymmetric {A} (m1 m2 : spec A) :
  m1 ≤ m2 → m2 ≤ m1 → m1 = m2.
Proof.
  unfold spec_leq.
  intros. eapply prove_spec_eq. intros.
  apply propositional_extensionality.
  split; eauto.
Qed.

(* [bind] is covariant in both positions. *)

(* The fact that [m1] is upward-closed is exploited. *)

Lemma spec_leq_bind {A B} (m1 m2 : spec A) (f1 f2 : A → spec B) :
  m1 ≤ m2 →
  f1 ≼ f2 →
  spec_bind m1 f1 ≤ spec_bind m2 f2.
Proof.
  unfold pointwise_spec_leq.
  unfold spec_leq, spec_bind. simpl.
  intros Hmm Hff φ Hm1.
  eapply Hmm; clear Hmm.
  eapply exploit_upward_closed; [ clear Hm1 | eapply Hm1 ].
  simpl. eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* A dummy [skip] combinator. *)

Global Instance monadskip_spec : MonadSkip spec :=
  { skip := (λ {A} (m : spec A), m) }.

Global Instance monadskiplaws_spec :
  MonadSkipLaws _ _.
Proof.
  constructor.
  { unfold skip, monadskip_spec. reflexivity. }
Qed.

Lemma unfold_skip {A} (m : spec A) (φ : A → Prop) :
  skip m ∋ φ ↔
  m ∋ φ.
Proof.
  tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The greatest fixed point combinator. *)

Section Fix.

Context {T A : Type}.
Variable ff  : (T → spec A) → (T → spec A).

Implicit Type t : T.
Implicit Type φ : A → Prop.
Implicit Type p : T → spec A.

(* The greatest fixed point is constructed as follows. The existential
   quantifier can be read here as an infinite union. The greatest fixed
   point is the union of all post fixed points, where we say that [p] is
   a post fixed point if [p ≼ ff p] holds. *)

Program Definition spec_mfix (t : T) : spec A :=
  λ φ,
    ∃ p,
      p t ∋ φ  ∧
      p ≼ ff p .
Next Obligation.
  intros t φ φ' Hφφ'.
  intros (p & ? & ?).
  eauto using exploit_upward_closed.
Defined.

(* By definition, [mspec_fix] is greater than any post fixed point.
   So, if it is a fixed point (which we will prove below), then it
   must be the greatest fixed point. This is the coinduction principle. *)

Lemma spec_coinduction p :
  p ≼ ff p →
  p ≼ spec_mfix.
Proof.
  intros post t φ ptφ. unfold spec_mfix. simpl.
  eauto.
Qed.

(* The transformer [ff] must be monotone. *)

Variable monotone_ff :
  ∀ p1 p2, p1 ≼ p2 → ff p1 ≼ ff p2.

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
  spec_mfix t ∋ φ → ff spec_mfix t ∋ φ.
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
  ff spec_mfix t ∋ φ → spec_mfix t ∋ φ.
Proof.
  intros. eapply construction. eauto.
Qed.

(* Therefore, [spec_mfix] is a fixed point. *)

Lemma fixed_point_expanded t :
  spec_mfix t = ff spec_mfix t.
Proof.
  eapply spec_leq_antisymmetric;
  eauto using construction, deconstruction.
Qed.

Lemma fixed_point :
  spec_mfix = ff spec_mfix.
Proof.
  extensionality t. eapply fixed_point_expanded.
Qed.

End Fix.

Global Instance spec_monad_fix : MonadFix spec :=
  { mfix := @spec_mfix }.

Global Instance spec_monad_fix_laws :
  MonadFixLaws spec_monad_fix.
Proof.
  eapply (@Build_MonadFixLaws _ _ (@spec_leq));
  unfold spec_leq;
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

Lemma monotone_spec_iter_body :
  ∀ p1 p2, p1 ≼ p2 → spec_iter_body p1 ≼ spec_iter_body p2.
Proof.
  intros. intro i.
  unfold spec_iter_body.
  eapply spec_leq_bind.
  { reflexivity. }
  intro signal. destruct signal.
  { eauto. }
  { reflexivity. }
Qed.

(* A first reformulation of the definition of [spec_iter]. *)

Lemma unfold_spec_iter_preliminary (i : I) (φ : R → Prop) :
  spec_iter i ∋ φ =
  ∃ (p : I → spec R),
    p i ∋ φ ∧
    p ≼ spec_iter_body p.
Proof.
  reflexivity.
Qed.

(* A reformulation of the postcondition of the loop body. *)

Definition spec_iter_body_post (self : I → spec R) (φ : R → Prop) :=
  λ (signal : I + R),
    match signal with
    | inl i =>
        (* If the body yields a new state [i], continue. *)
        self i ∋ φ
    | inr r =>
        (* If the body yields a result [r], return this result. *)
        φ r
    end.

Lemma monotone_spec_iter_body_post
  (self1 self2 : I → spec R) :
  self1 ≼ self2 →
  (* The following three lines could be written:
       spec_iter_body_post self1 ≼ spec_iter_body_post self2
     if [spec_iter_body_post self] had type [spec (I + R)];
                            but it has type [(I + R) → Prop]. *)
  ∀ (φ : R → Prop) (signal : I + R),
  spec_iter_body_post self1 φ signal →
  spec_iter_body_post self2 φ signal.
Proof.
  unfold pointwise_spec_leq, spec_leq.
  intros Hself φ signal.
  unfold spec_iter_body_post.
  destruct signal; eauto.
Qed.

(* A reformulation of the definition of [spec_iter_body]. *)

Lemma unfold_spec_iter_body
  (self : I → spec R)
  (i : I) (φ : R → Prop) :
  spec_iter_body self i ∋ φ ↔
  body i ∋ (spec_iter_body_post self φ).
Proof.
  unfold spec_iter_body. simpl.
  apply descend_post. intros [|]; simpl spec_iter_body_post; tauto.
Qed.

(* A reformulation of the inequality [p ≼ spec_iter_body p]. *)

Lemma unfold_post_fixed_point (p : I → spec R) :
  (p ≼ spec_iter_body p) =
    ∀ i φ,
      p i ∋ φ →
      body i ∋ spec_iter_body_post p φ.
Proof.
  unfold spec_iter_body.
  unfold pointwise_spec_leq.
  unfold spec_leq.
  unfold bind. simpl.
  unfold spec_ret.
  apply propositional_extensionality.
  apply descend_forall; intros i.
  apply descend_forall; intros φ.
  apply descend_forall. intros piφ.
  apply descend_post. intros [ j | r ]; simpl; tauto.
Qed.

(* A second reformulation of the definition of [spec_iter]. *)

(* This is essentially Hoare's reasoning rule for [while] loops. *)

Lemma unfold_spec_iter (i : I) (φ : R → Prop) :
  spec_iter i ∋ φ =
  ∃ (p : I → spec R),
    p i ∋ φ ∧
    ∀ i φ,
      p i ∋ φ →
      body i ∋ spec_iter_body_post p φ.
Proof.
  rewrite unfold_spec_iter_preliminary.
  apply propositional_extensionality.
  apply descend_exists; intros p.
  rewrite unfold_post_fixed_point.
  reflexivity.
Qed.

End Iter.

Global Instance monaditer_spec : MonadIter spec :=
  { iter := @spec_iter }.

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

Global Opaque spec_mfix.
Global Opaque spec_iter.
