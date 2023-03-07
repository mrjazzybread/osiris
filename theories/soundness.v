From Coq.Logic Require Import FunctionalExtensionality.
From ITree Require Import ITree Eqit Exception.
Require Import lang monads free eval handle div spec wp.

(* This file establishes that the [spec] monad offers a sound abstract
   interpretation of the [div] monad. *)

(* -------------------------------------------------------------------------- *)

(* A computation [m] is safe with respect to a postcondition [φ] if
   1- [m] does not fail; and 2- if [m] produces a value [v] then [φ v]
   holds. This is a partial correctness interpretation: divergence is
   permitted. *)

(* We first define what it means to be safe for [n] steps. *)

Fixpoint initially_safe {A} (n : nat) (m : div A) (φ : A → Prop) : Prop :=
  match n, observe m with
  | 0, _ =>
      (* Every computation is safe for zero steps. *)
      True
  | _, RetF v =>
      (* The computation produces a value [v]. *)
      φ v
  | S n, TauF m =>
      (* The computation performs a step and continues. *)
      initially_safe n m φ
  | _, VisF _tt _k =>
      (* The computation fails. *)
      False
  end.

(* A paraphrase lemma. *)

Lemma unfold_initially_safe_S {A} (n : nat) (m : div A) (φ : A → Prop) :
  initially_safe (S n) m φ =
  match observe m with
  | RetF v =>
      φ v
  | TauF m =>
      initially_safe n m φ
  | VisF _tt _k =>
      False
  end.
Proof.
  reflexivity.
Qed.

(* If, for every [n], a computation is safe for [n] steps,
   then this computation is safe. *)

Definition safe {A} (m : div A) (φ : A → Prop) :=
  ∀ n, initially_safe n m φ.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [initially_safe (S n) m φ] under a hypothesis about
   the observable behavior of the computation [m]. *)

Lemma invert_initially_safe_RetF {A} {n} {m : div A} {a} (φ : A → Prop) :
  initially_safe (S n) m φ →
  observe m = RetF a →
  φ a.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

Lemma invert_initially_safe_TauF {A} {n} {m m' : div A} {φ : A → Prop} :
  initially_safe (S n) m φ →
  observe m = TauF m' →
  initially_safe n m' φ.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

Lemma invert_initially_safe_VisF {A X} {n} {m : div A} {e} {k : X → div A} {φ : A → Prop} :
  initially_safe (S n) m φ →
  observe m = VisF e k →
  False.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [safe m φ] under a hypothesis about the observable
   behavior of the computation [m]. *)

Lemma invert_safe_RetF {A} {m : div A} {a} (φ : A → Prop) :
  safe m φ →
  observe m = RetF a →
  φ a.
Proof.
  unfold safe. intros Hsafe Hm. specialize (Hsafe 1).
  eauto using (invert_initially_safe_RetF φ).
Qed.

Lemma invert_safe_TauF {A} {m m' : div A} {φ : A → Prop} :
  safe m φ →
  observe m = TauF m' →
  safe m' φ.
Proof.
  unfold safe. eauto using invert_initially_safe_TauF.
Qed.

Lemma invert_safe_VisF {A X} {m : div A} {e} {k : X → div A} {φ : A → Prop} :
  safe m φ →
  observe m = VisF e k →
  False.
Proof.
  unfold safe. intros Hsafe Hm. specialize (Hsafe 1).
  eauto using invert_initially_safe_VisF.
Qed.

(* -------------------------------------------------------------------------- *)

(* An alternative definition of [safe] as a coinductive predicate can be
   given. This definition is technically not needed, but we offer it and
   prove its equivalence, as a sanity check. *)

CoInductive alt_safe {A} : div A → (A → Prop) → Prop :=
  | AltSafeRetF :
      ∀ m v (φ : A → Prop),
      observe m = RetF v →
      φ v →
      alt_safe m φ
  | AltSafeTauF :
      ∀ m m' (φ : A → Prop),
      observe m = TauF m' →
      alt_safe m' φ →
      alt_safe m φ
.

(* The following lemmas prove that [safe] and [alt_safe] are equivalent. *)

Lemma safe_implies_alt_safe {A} (φ : A → Prop) :
  ∀ m,
  safe m φ →
  alt_safe m φ.
Proof.
  cofix CIH.
  intro m; case_eq (observe m); [ clear CIH | | clear CIH ].
  { eauto using (invert_safe_RetF φ), AltSafeRetF. }
  { intros; eapply AltSafeTauF; eauto using invert_safe_TauF. }
  { intros. elimtype False. eauto using invert_safe_VisF. }
Qed.

Lemma alt_safe_implies_initially_safe {A} (φ : A → Prop) :
  ∀ n m,
  alt_safe m φ →
  initially_safe n m φ.
Proof.
  induction n; simpl; [ tauto |].
  intros m Hsafe.
  destruct Hsafe;
  match goal with Hm: observe m = _ |- _ => rewrite Hm end;
  eauto.
Qed.

Lemma alt_safe_implies_safe {A} (φ : A → Prop) :
  ∀ m, alt_safe m φ → safe m φ.
Proof.
  unfold safe. eauto using alt_safe_implies_initially_safe.
Qed.

Lemma alt_safe_iff_safe {A} (φ : A → Prop) :
  ∀ m, alt_safe m φ ↔ safe m φ.
Proof.
  split; eauto using safe_implies_alt_safe, alt_safe_implies_safe.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [n1 ≤ n2] holds, then a computation that is safe for [n2] steps is
   also safe for [n1] steps. *)

Lemma initially_safe_monotonic {A} (φ : A → Prop) :
  ∀ n1 n2 m,
  initially_safe n2 m φ →
  n1 ≤ n2 →
  initially_safe n1 m φ.
Proof.
  induction n1; simpl; intros n2 m Hsafe Hleq; [ tauto |].
  destruct n2 as [| n2 ]; [ lia |].
  simpl in Hsafe.
  destruct (observe m); eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [φ] entails [φ'], then a computation that is safe with respect to [φ]
   is also safe with respect to [φ']. *)

Lemma initially_safe_covariant {A} (φ φ' : A → Prop) :
  (∀ a, φ a → φ' a) →
  ∀ n m,
  initially_safe n m φ →
  initially_safe n m φ'.
Proof.
  induction n; simpl; intros; [ tauto |].
  destruct (observe m); eauto.
Qed.

Lemma safe_covariant {A} (m : div A) (φ φ' : A → Prop) :
  (∀ a, φ a → φ' a) →
  safe m φ → safe m φ'.
Proof.
  unfold safe. eauto using initially_safe_covariant.
Qed.

(* -------------------------------------------------------------------------- *)

(* Because [safe m] is covariant in [φ], it can be viewed as an inhabitant
   of the [spec] monad. In other words, [safety] can be viewed as function
   of type [div A → spec A]. *)

(* Later on in this file, we prove that [safety] commutes with all of the
   monadic combinators: it is a monad morphism. *)

Program Definition safety {A} (m : div A) : spec A :=
  safe m.
Next Obligation.
  simpl. eauto using safe_covariant.
Qed.

Lemma unfold_safety {A} (m : div A) (φ : A → Prop) :
  safety m ∋ φ ↔ safe m φ.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas characterize the interaction of [safe] with
   [ret], [skip], and [mzero]. *)

Lemma safe_ret {A} (a : A) (φ : A → Prop) :
  safe (ret a) φ ↔
  φ a.
Proof.
  split.
  { intros Hsafe. specialize (invert_safe_RetF _ Hsafe eq_refl). tauto. }
  { intros ? [| n]; simpl; tauto. }
Qed.

Lemma safe_skip {A} (m : div A) (φ : A → Prop) :
  safe (skip m) φ ↔ safe m φ.
Proof.
  unfold safe. split; intros Hsafe n.
  { specialize (Hsafe (S n)). simpl in Hsafe. tauto. }
  { destruct n as [| n ]; simpl; eauto. }
Qed.

Lemma safe_mzero {A} (φ : A → Prop) :
  safe mzero φ ↔
  False.
Proof.
  split.
  { intros Hsafe. specialize (invert_safe_VisF Hsafe eq_refl). tauto. }
  { tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [safety] commutes with [ret], [skip], and [mzero]. *)

Lemma safety_ret {A} (a : A) :
  safety (ret a) = (ret a).
Proof.
  intros. eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  rewrite safe_ret.
  tauto.
Qed.

Lemma safety_skip {A} (m : div A) :
  safety (skip m) = safety m.
Proof.
  eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  apply safe_skip.
Qed.

Lemma safety_mzero {A} :
  safety (mzero : div A) = (mzero : spec A).
Proof.
  eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  apply safe_mzero.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas describe the interaction of safety and [bind],
   and culminate in a proof that [safety] commutes with [bind]. *)

(* If [m1] is safe for [n1] steps and (then, for every result [a])
      [m2 a] is safe for [n2] steps
   then [bind m1 m2] is safe for [min n1 n2] steps.

   In other words,
   if [m1] is safe for [n] steps and (then, for every result [a])
      [m2 a] is safe for [n] steps
   then [bind m1 m2] is safe for [n] steps.

   One cannot expect to obtain safety for [n1+n2] steps. To see this,
   consider the case where [n1] is zero. With no hypothesis at all
   about [m1], one would have to prove that [m2 a] is safe for [n2]
   steps. *)

Lemma initially_safe_bind_aux_1 {A B} (m2 : A → div B) :
  ∀ n (m1 : div A) (φ : B → Prop),
  initially_safe n m1 (λ a, initially_safe n (m2 a) φ) →
  initially_safe n (bind m1 m2) φ.
Proof.
  induction n; [tauto |]. intros m1 φ Hsafe.

  (* Expose two occurrences of [observe m1]. *)
  rewrite unfold_bind.
  rewrite unfold_initially_safe_S in Hsafe.
  (* Proceed by cases on [m1]. Three cases arise. *)
  destruct (observe m1); [ clear IHn | | clear IHn ].

  (* Case: [m1] is [ret _]. *)
  { tauto. }

  (* Case: [m1] is [skip m'1]. *)
  { (* The goal is to prove that [bind m'1 m2] is safe for [n] steps. *)
    simpl.
    (* This follows from the induction hypothesis and from the fact that
       [initially_safe] is covariant in its postcondition and monotonic
       in its step index. *)
    eapply IHn; clear IHn.
    eapply initially_safe_covariant; [| exact Hsafe ]; clear Hsafe.
    intros a Hm2a.
    eapply initially_safe_monotonic; [ exact Hm2a |].
    lia. }

  (* Case: [m1] fails. *)
  { (* The goal is to show that this cannot happen. *)
    simpl. tauto. }

Qed.

(* Conversely, if [bind m1 m2] is safe for [n1 + n2] steps
   then [m1] is safe for [n1] steps and (then, for every result [a])
        [m2 a] is safe for [n2] steps. *)

Lemma initially_safe_bind_aux_2 {A B} (m2 : A → div B) :
  ∀ n1 n2 (m1 : div A)  (φ : B → Prop),
  initially_safe (n1 + n2) (bind m1 m2) φ →
  initially_safe n1 m1 (λ a, initially_safe n2 (m2 a) φ).
Proof.
  induction n1; intros n2 m1 φ; [ simpl; tauto |].

  (* Expose two occurrences of [observe m1]. *)
  rewrite unfold_bind.
  rewrite unfold_initially_safe_S.
  (* Proceed by cases on [m1]. Three cases arise. *)
  destruct (observe m1); [ clear IHn1 | | clear IHn1 ].

  (* Case: [m1] is [ret a]. *)
  { eauto using initially_safe_monotonic with lia. }

  (* Case: [m1] is [skip m'1]. *)
  { simpl. intros Hsafe. apply IHn1. exact Hsafe. }

  (* Case: [m1] fails. *)
  { intros Hsafe. eauto using invert_initially_safe_VisF. }

Qed.

(* The intersection rule of Hoare logic: if for every [x] the computation
   [m] admits the postcondition [φ x], then [m] admits the postcondition
   [∀ x, φ x]. *)

Lemma initially_safe_intersection {A X} {_ : Inhabited X} (φ : X → A → Prop) :
  ∀ n m,
  (∀ x, initially_safe n m (φ x)) →
  initially_safe n m (λ a, ∀ x, φ x a).
Proof.
  induction n; [ simpl; tauto |]; intros m Hsafe.

  (* Expose two occurrences of [observe m]. *)
  rewrite unfold_initially_safe_S.
  unfold initially_safe in Hsafe; fold @initially_safe in Hsafe.
    (* this should be: rewrite unfold_initially_safe_S in Hsafe. *)
  (* Proceed by cases on [m]. Three cases arise. *)
  destruct (observe m); [ clear IHn | | clear IHn ].

  (* Case: [m] is [ret a]. *)
  { exact Hsafe. }
  (* Case: [m] is [skip m']. *)
  { eapply IHn. exact Hsafe. }
  (* Case: [m1] fails. *)
  (* The fact that the type [X] is inhabited is exploited. *)
  { specialize (Hsafe inhabitant). tauto. }

Qed.

(* A sequence [bind m1 m2] is safe if and only if
   [m1] is safe and (then, for every result [a])
   [m2 a] is safe. *)

Lemma safe_bind {A B} (m1 : div A) (m2 : A → div B) (φ : B → Prop) :
  safe (bind m1 m2) φ ↔ safe m1 (λ a, safe (m2 a) φ).
Proof.
  unfold safe.
  split; intros Hsafe.
  (* This implication corresponds to the completeness of the program logic.
     It is interesting to note that the intersection rule is used here. *)
  { intros n1.
    eapply initially_safe_intersection. intros n2.
    eapply initially_safe_bind_aux_2.
    eapply Hsafe. }
  (* This implication corresponds to the soundness of the program logic. *)
  { intros n.
    eapply initially_safe_bind_aux_1.
    eapply initially_safe_covariant; [| eauto ]; intros a Hm2a.
    eapply Hm2a. }
Qed.

(* [safety] commutes with [bind]. *)

Lemma safety_bind {A B} (m1 : div A) (m2 : A → div B) :
  safety (bind m1 m2) = bind (safety m1) (λ a, safety (m2 a)).
Proof.
  eapply prove_spec_eq_ext. intros φ. rewrite unfold_safety. apply safe_bind.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas describe the interaction of safety and [iter],
   and culminate in a proof that [safety] commutes with [iter]. *)

(* If the specification [safety ∘ body], iterated out of the state [i],
   guarantees the postcondition [φ], then the computation [body], executed
   out of the state [i], is safe with respect to [φ]. *)

(* We first state this property in a manner that allows induction over [n],
   then reformulate it without reference to step indices. *)

Lemma initially_safe_iter_aux_1 {I A} (body : I → div (I + A)) :
  ∀ n i φ,
  iter (safety ∘ body) i ∋ φ →
  initially_safe n (iter body i) φ.
Proof.
  (* Reason by induction over [n]. *)
  induction n; [ simpl; tauto |].
  intros i φ Hbody.
  (* Unfold [iter] in the goal. *)
  erewrite unfold_iter by typeclasses eauto.
  (* Exploit the commutation of [initially_safe] and [bind]. *)
  eapply initially_safe_bind_aux_1.
  (* Unfold [iter] and [bind] in the hypothesis. *)
  erewrite unfold_iter in Hbody by typeclasses eauto.
  simpl in Hbody.
  (* Specialize the hypothesis for the desired step index.
     The hypothesis now resembles the goal; there remains
     to compare the postconditions. *)
  specialize (Hbody (S n)).
  eapply initially_safe_covariant; [| exact Hbody]. clear i Hbody.
  (* We must study two cases: continuing and finishing. *)
  intros [ i | a ]; simpl.
  (* Case: the loop body wants to continue. *)
  { rewrite unfold_skip. eapply IHn. }
  (* Case: the loop body is done. *)
  { tauto. }
Qed.

Lemma safe_iter_aux_1 {I A} (body : I → div (I + A)) :
  ∀ i φ,
  iter (safety ∘ body) i ∋ φ →
  safe (iter body i) φ.
Proof.
  unfold safe. eauto using initially_safe_iter_aux_1.
Qed.

(* If the computation [iter body i] is safe with respect to [φ] then the
   computation [body i] is safe with respect to the postcondition
   [spec_iter_body_post invariant φ], where the loop invariant is defined as
   [safety ∘ iter body]. This means that the loop body must either ask to
   continue with a new state that satisfies the loop invariant or ask to
   terminate with a value that satisfies [φ]. *)

(* We first state this property in a manner that allows induction over [n],
   then reformulate it without reference to step indices. *)

Lemma initially_safe_iter_aux_2 {I A} (body : I → div (I + A)) :
  let invariant := safety ∘ iter body in
  ∀ n i φ,
  safe (iter body i) φ →
  initially_safe n (body i) (spec_iter_body_post invariant φ).
Proof.
  (* Reason by induction over [n]. *)
  induction n; [ simpl; tauto |].
  intros i φ Hsafe.
  (* Unfold [iter] and [bind] in the hypothesis. *)
  erewrite unfold_iter in Hsafe by typeclasses eauto.
  rewrite safe_bind in Hsafe.
  (* Specialize the hypothesis for the desired step index.
     The hypothesis now resembles the goal; there remains
     to compare the postconditions. *)
  specialize (Hsafe (S n)).
  eapply initially_safe_covariant; [| exact Hsafe]; clear i Hsafe.
  (* We must study two cases: continuing and finishing. *)
  intros [i | a] Hsafe; simpl.
  { rewrite safe_skip in Hsafe. tauto. }
  { rewrite safe_ret in Hsafe. tauto. }
Qed.

Lemma safe_iter_aux_2 {I A} (body : I → div (I + A)) :
  let invariant := safety ∘ iter body in
  ∀ i φ,
  safe (iter body i) φ →
  safe (body i) (spec_iter_body_post invariant φ).
Proof.
  unfold safe at 2. eauto using initially_safe_iter_aux_2.
Qed.

(* The invariant [safety ∘ iter body] is preserved by one iteration of
   the loop body [safety ∘ body]. *)

Section ImportNotations.

Set Warnings "-notation-overridden".
Import spec.Notations.

Local Lemma preservation {I A} (body : I → div (I + A)) :
  let invariant := safety ∘ iter body in
  invariant ≼ spec_iter_body (safety ∘ body) invariant.
Proof.
  (* Unfold definitions. *)
  intros. subst invariant.
  intros i. simpl.
  intros φ. rewrite unfold_safety.
  rewrite unfold_spec_iter_body. simpl.
  (* We find that the above abstract statement is just a reformulation
     of [safe_iter_aux_2]. *)
  apply safe_iter_aux_2.
Qed.

(* [safety] commutes with [iter]. *)

Lemma safety_iter {I A} (body : I → div (I + A)) (i : I) :
  safety (iter body i) = iter (safety ∘ body) i.
Proof.
  (* Unfold definitions. *)
  eapply prove_spec_eq_ext. intros φ.
  rewrite unfold_safety.
  split.
  (* This implication corresponds to the completeness of the program logic.
     To establish the goal [iter (safety ∘ body) i ∋ φ], by definition of
     [iter], we must exhibit a loop invariant. Fortunately, we do have a
     loop invariant: it is the safety of [iter body]. *)
  { intros Hsafe.
    erewrite unfold_spec_iter_preliminary by typeclasses eauto.
    set (invariant := safety ∘ iter body).
    exists invariant.
    split.
    { simpl. exact Hsafe. }
    { apply preservation. }
  }
  (* This implication corresponds to the soundness of the program logic. *)
  { eauto using safe_iter_aux_1. }
Qed.

End ImportNotations.

(* -------------------------------------------------------------------------- *)

(* Because we have established that [safety] commutes with every combinator
   -- [ret], [skip], [mzero], [bind], [iter] -- it is now easy to establish
   that [safety] commutes with [handle], which is defined in terms of these
   combinators. *)

(* This is a fundamental property, for at least two reasons.

   First, this implies that the program logic is sound and complete.
   Executing the computation [handle m] in the divergence monad and
   requiring this computation to be safe is the same as computing the
   precondition [handle m] in the specification monad and requiring this
   precondition to hold.

   Second, this implies that every equality law that holds in the monad
   [div A] holds also in the monad [spec A].

   In particular, the commutation of [handle] and [bind], which we have
   established (via co-inductive equational reasoning) in the divergence
   monad, holds also in the specification monad. This means that the Bind
   rule of the program logic is sound and complete. (See handle_spec.v.) *)

Lemma safety_handle {A} (m : free A) :
  safety (handle m) = handle m.
Proof.
  unfold handle.
  rewrite safety_iter.
  f_equal; clear m.
  (* The goal is now [safety ∘ handle_body = handle_body]. *)
  extensionality m. simpl.
  unfold handle_body.
  destruct m.
  (* Case: returning a value. *)
  { rewrite safety_ret. reflexivity. }
  (* Case: hard failure. *)
  { rewrite safety_mzero. reflexivity. }
  (* Case: soft failure. *)
  { rewrite safety_mzero. reflexivity. }
  (* Case: recursive evaluation request. *)
  { destruct req. rewrite safety_ret. reflexivity. }
Qed.

(* As an immediate corollary, [safety] commutes with [run]. *)

Lemma safety_run η e :
  safety (run η e) = run η e.
Proof.
  unfold run. apply safety_handle.
Qed.

(* -------------------------------------------------------------------------- *)

(* The final soundness and completeness statement follows. The assertion
   [wp η e φ] of the program logic is equivalent to the property that the
   computation [run η e] is safe with respect to [φ]. *)

Lemma soundness_and_completeness η e φ :
  wp η e φ ↔
  safe (run η e) φ.
Proof.
  unfold wp. rewrite <- safety_run. rewrite unfold_safety. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

Global Opaque handle.
