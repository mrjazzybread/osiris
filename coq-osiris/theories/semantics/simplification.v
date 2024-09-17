From Coq.Logic Require Import FunctionalExtensionality.
From stdpp Require Import relations.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.
Local Open Scope nat_scope.

(* This file defines a simplification relation: [simp m m'] means that [m]
   can be simplified to [m']. Simplification is pure: it does not involve
   the heap and does not make irreversible non-deterministic choices. This
   is expressed by a commutation diagram between the relations [step] and
   [simp].

   [simp] is nevertheless a non-deterministic relation: there can be several
   ways of simplifying a computation. We prove a confluence property, which
   is limited to final results.

   When [simp m m'] holds, we expect [WP m' φ] to imply [WP m φ]. This means
   that one can prove a safety property of the simpler program [m'] and
   transport this property back to [m].

   A simplification step is not necessarily a reduction step: that is,
   [simp] is not a subrelation of [step].

   The simplification relation serves two distinct (yet related) purposes:

   - It can be used to simplify a program while proving that this program
     satisfies a specification of the form of [WP m φ]. This simplification
     process can be transparently performed by the tactics that we define.

   - It can be used to write specifications for pure programs. Indeed, if a
     program is pure (that is, does not involve divergence, non-determinism,
     or mutable state) then it should have a specification of the form [∃ a,
     simp m (ret a) ∧ φ a]. See [pure] for specifications allowing
     non-determinism. *)

(* -------------------------------------------------------------------------- *)

(* The relation [simp m m'] is inductively defined as follows. *)

(* [SimpEval] and [SimpLoop] allow certain [Stop] events to be replaced with
   their meaning.

   [SimpFlipAgree] requires that the computations [continue k true] and
   [continue k false] can both be simplified to a common computation [m]. Thus,
   this rule is applicable only in the special case where the final outcome of
   the computation is independent of the coin flip. This is useful; e.g., it
   allows OCaml's [assert] construct to be regarded as pure.

   [SimpParRetLeft] and [SimpParRetRight] simplify a [par] construct
   where at least one side is [ret _].

   [SimpPar] allows simplification to take place under a [Par] constructor.

   [SimpParThrowAgree] combines simplifications to the same exception on both
   sides of a [Par] constructor

   [SimpPerform] allows simplification in the continuation of [perform e].
   This is the only rule that allows simplification in a continuation, under
   a binder. This rule is not expected to be useful to the end user;
   however, it is required in the proof of the main commutative diagram; see
   the lemma [simplify_step_diagram].

   [SimpReflexive] and [SimpTransitive] make simplification reflexive and
   transitive by definition. *)

(* Simplification under [Handle] is not permitted. Perhaps it could be
   easily allowed (we have not tried). We do not anticipate a need for this
   rule, so we are waiting until the need arises. *)

Inductive simp {A E : Type} : micro A E → micro A E → Prop :=
| SimpEval:
    ∀ η e k,
    simp
      (Stop CEval (η, e) k)
      (try2 (eval η e) k)
| SimpLoop :
    ∀ η x i1 i2 e k,
    simp
      (Stop CLoop (η, x, i1, i2, e) k)
      (try2 (loop η x i1 i2 e) k)
| SimpFlipAgree :
    ∀ m x k,
    simp (continue k true) m →
    simp (continue k false) m →
    simp
      (Stop CFlip x k)
      m
| SimpParRetLeft:
    ∀ {A1 A2 E'} a1 m2 (k : outcome2 (A1 * A2) E' → _),
    simp
      (Par (Ret a1) m2 k)
      (try2 m2 (join1 a1 k))
| SimpParRetRight:
    ∀ {A1 A2 E'} m1 a2 (k : outcome2 (A1 * A2) E' → _),
    simp
      (Par m1 (Ret a2) k)
      (try2 m1 (join2 a2 k))
| SimpPar:
    ∀ {A1 A2 E'} m1 m'1 m2 m'2 (k : outcome2 (A1 * A2) E' → _),
    simp m1 m'1 →
    simp m2 m'2 →
    simp (Par m1 m2 k) (Par m'1 m'2 k)
| SimpParThrowAgree:
    ∀ {A1 A2 E'} e m1 m2 (k : outcome2 (A1 * A2) E' → _),
    simp m1 (Throw e) →
    simp m2 (Throw e) →
    simp (Par m1 m2 k) (k (O2Throw e))
| SimpPerform:
     ∀ e k k',
     (∀ o, simp (k o) (k' o)) →
     simp
       (Stop CPerform e k)
       (Stop CPerform e k')
| SimpHandleRet:
     ∀ m v k,
     simp m (Ret v) ->
     simp
       (Handle m k)
       (continue k v)
| SimpHandleThrow:
     ∀ m e k,
     simp m (Throw e) ->
     simp
       (Handle m k)
       (discontinue k e)
| SimpReflexive:
    ∀ m,
    simp m m
| SimpTransitive:
    ∀ m1 m2 m3,
    simp m1 m2 →
    simp m2 m3 →
    simp m1 m3
.

Global Hint Constructors simp : simp.


(* -------------------------------------------------------------------------- *)

(* More (derived) construction rules for [simp]. *)

(* The following two auxiliary lemmas can be useful when a constructor cannot
   be applied directly. *)

Lemma simp_up_to_eq_left {A E} {m1 m1' m2 : micro A E} :
  simp m1' m2 →
  m1 = m1' →
  simp m1 m2.
Proof.
  congruence.
Qed.

Lemma simp_up_to_eq_right {A E} {m1 m2 m2' : micro A E} :
  simp m1 m2 →
  m2 = m2' →
  simp m1 m2'.
Proof.
  congruence.
Qed.

(* A consequence rule. *)

Lemma simp_consequence {A E} (m : micro A E) a' a :
  simp m (ret a') →
  a = a' →
  simp m (ret a).
Proof.
  intros. subst. eauto.
Qed.

(* Derived constructors. *)

Lemma SimpParRetRet {A1 A2 A E E'}
  a1 a2 (k : outcome2 (A1 * A2) E' → micro A E)
:
  simp
    (Par (Ret a1) (Ret a2) k)
    (continue k (a1, a2)).
Proof.
  eauto using simp_up_to_eq_right with simp try_ret.
Qed.

Lemma simp_par {A E A1 A2 E'} m1 m2 m
  (k : outcome2 (A1 * A2) E → micro A E') a1 a2 :
  simp m1 (ret a1) ->
  simp m2 (ret a2) ->
  simp (continue k (a1, a2)) m ->
  simp (Par m1 m2 k) m.
Proof.
  intros. eauto with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define a 3-argument relation [simplify n m m'] where the natural
   integer [n] measures a certain notion of the cost of the simplification
   path from [m] to [m'].

   The main two commutative diagrams, namely [simplify_step_diagram] and
   [simplify_confluent], control the manner in which [n] decreases or is
   preserved.

   In [simplify_step_diagram], the fact that [n] cannot increase means that
   one [step] of computation cannot create simplification work. Intuitively,
   this is true because [step] does not duplicate computations.

   In [simplify_confluent], a similar intuition holds. One step of
   simplification cannot create more simplification work, because
   simplification does not duplicate computations. *)

(* Assigning a cost of 1 to [SimplifyTransitive] is not required in the proof
   of [simplify_step_diagram], but appears to be necessary in the proof of
   [invert_stack_try2_ret]. *)

(* In the proof of [simplify_step_diagram], in the cases [SimplifyParRetLeft]
   and [SimplifyParRetRight], we find that the cost of these rules, when used
   naked, must be *greater* than the cost of the same rules, when used under
   [SimplifyPerform]. This leads us to assign cost 2 to [SimplifyParRet*] and
   cost 1 to [SimplifyPerform], *regardless of the cost* of the simplification
   step that is performed inside. Then, the proof of [simplify_step_diagram]
   goes through. However, because the cost of the premise in [SimplifyPerform]
   is not bounded, we lose the proof of confluence of [simplify], which used
   to exist. Fortunately, the confluence of [simplify] is not needed anywhere.
   We are still able to prove that [simplify], restricted to final results, is
   confluent. This is good enough. *)

(* It is worth noting that the lemma [wp_simp] needs only the weak commutative
   diagram [simp_step_diagram], where the index [n] is not controlled. Indeed,
   the proof of [wp_simp] is by Löb induction, so only a finite number of
   [step]s into the future are of interest. Therefore, even if the cost of the
   [simp] path is not under control, once the end of the future is reached, we
   do not care any more. *)

(* End users need not know about the relation [simplify]. *)

Inductive simplify {A E : Type} : nat → micro A E → micro A E → Prop :=
| SimplifyEval:
    ∀ p η e k,
    p = (η, e) →
    simplify 1
      (Stop CEval p k)
      (try2 (eval η e) k)
| SimplifyLoop :
    ∀ p η x i1 i2 e k,
    p = (η, x, i1, i2, e) →
    simplify 1
      (Stop CLoop p k)
      (try2 (loop η x i1 i2 e) k)
| SimplifyFlipAgree :
    ∀ n1 n2 m x k,
    simplify n1 (continue k true) m →
    simplify n2 (continue k false) m →
    simplify (n1 + n2 + 1)
      (Stop CFlip x k)
      m
(* The following two rules have cost 2. *)
| SimplifyParRetLeft:
    ∀ {A1 A2 E'} a1 m2 (k : outcome2 (A1 * A2) E' → _),
    simplify 2
      (Par (Ret a1) m2 k)
      (try2 m2 (join1 a1 k))
| SimplifyParRetRight:
    ∀ {A1 A2 E'} m1 a2 (k : outcome2 (A1 * A2) E' → _),
    simplify 2
      (Par m1 (Ret a2) k)
      (try2 m1 (join2 a2 k))
| SimplifyPar:
    ∀ {A1 A2 E'} n1 n2 m1 m'1 m2 m'2 (k : outcome2 (A1 * A2) E' → _),
    simplify n1 m1 m'1 →
    simplify n2 m2 m'2 →
    simplify (n1 + n2 + 1) (Par m1 m2 k) (Par m'1 m'2 k)
| SimplifyParThrowAgree:
    ∀ {A1 A2 E'} n1 n2 e m1 m2 (k : outcome2 (A1 * A2) E' → _),
    simplify n1 m1 (Throw e) →
    simplify n2 m2 (Throw e) →
    simplify (n1 + n2 + 1) (Par m1 m2 k) (discontinue k e)
(* The following rule has cost 1, regardless of the cost of its premise. *)
| SimplifyPerform:
     ∀ e k k',
     (∀ o, simp (k o) (k' o)) →
     simplify 1
       (Stop CPerform e k)
       (Stop CPerform e k')
| SimplifyHandleRet:
     ∀ v n m k,
     simplify n m (Ret v) ->
     simplify (S n)
       (Handle m k)
       (continue k v)
| SimplifyHandleThrow:
     ∀ v n m k,
     simplify n m (Throw v) ->
     simplify (S n)
       (Handle m k)
       (discontinue k v)
| SimplifyReflexive:
    ∀ m,
    simplify 0 m m
| SimplifyTransitive:
    ∀ n1 n2 m1 m2 m3,
    simplify n1 m1 m2 →
    simplify n2 m2 m3 →
    simplify (n1 + n2 + 1) m1 m3
.

Global Hint Constructors simplify : simplify.

(* For some mysterious reason, [eauto] can prove the following lemmas if we
   explicitly state them, but cannot prove them if it encounters them as
   subgoals in a larger proof. *)

Lemma SimplifyPerformParRetLeft
  {A E A1 A2 E'} e a1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  simplify 1
    (Stop CPerform e (λ o, Par (Ret a1) (m2 o) k))
    (Stop CPerform e (λ o, try2 (m2 o) (join1 a1 k))).
Proof.
  eauto with simplify simp.
Qed.

Lemma SimplifyPerformParRetRight
  {A E A1 A2 E'} e m1 a2 (k : outcome2 (A1 * A2) E' → micro A E) :
  simplify 1
    (Stop CPerform e (λ o, Par (m1 o) (Ret a2) k))
    (Stop CPerform e (λ o, try2 (m1 o) (join2 a2 k))).
Proof.
  eauto with simplify simp.
Qed.

Lemma SimplifyPerformParLeft
  {A E A1 A2 E'} e m1 m'1 m2 m'2 (k : outcome2 (A1 * A2) E' → micro A E) :
  (∀ o, simp (m1 o) (m'1 o)) →
  simp m2 m'2 →
  simplify 1
    (Stop CPerform e (λ o, Par (m1 o) m2 k))
    (Stop CPerform e (λ o, Par (m'1 o) m'2 k)).
Proof.
  eauto with simplify simp.
Qed.

Lemma SimplifyPerformParRight
  {A E A1 A2 E'} e m1 m'1 m2 m'2 (k : outcome2 (A1 * A2) E' → micro A E) :
  simp m1 m'1 →
  (∀ o, simp (m2 o) (m'2 o)) →
  simplify 1
    (Stop CPerform e (λ o, Par m1 (m2 o) k))
    (Stop CPerform e (λ o, Par m'1 (m'2 o) k)).
Proof.
  eauto with simplify simp.
Qed.

Global Hint Resolve
  SimplifyPerformParRetLeft SimplifyPerformParRetRight
  SimplifyPerformParLeft SimplifyPerformParRight
: simplify.

(* -------------------------------------------------------------------------- *)

(* [simplify 0 m1 m2] implies [m1 = m2]. *)

Lemma invert_simplify_zero {A E} {m1 m2 : micro A E} :
  simplify 0 m1 m2 →
  m1 = m2.
Proof.
  intros h; dependent induction h; eauto with lia f_equal.
Qed.

(* -------------------------------------------------------------------------- *)

(* [simplify _ m m'] and [simp m m'] are equivalent. *)

(* [simplify n m1 m2] implies [simp m1 m2]. *)

Lemma simplify_simp {A E} n (m1 m2 : micro A E) :
  simplify n m1 m2 →
  simp m1 m2.
Proof.
  induction 1; intros; subst; eauto with simp.
Qed.

Local Hint Resolve simplify_simp : simp.

(* [simp m1 m2] implies [simplify n m1 m2] for some [n]. *)

Lemma simp_simplify {A E} {m1 m2 : micro A E} :
  simp m1 m2 →
  ∃ n,
  simplify n m1 m2.
Proof.
  induction 1;
  repeat match goal with h: ∃ n, _ |- _ => destruct h end;
  eauto with simplify.
Qed.

(* -------------------------------------------------------------------------- *)

(* Simplification is compatible with [try2]. *)

Lemma simp_try2 {A B E' E} m1 m2 (k : outcome2 A E' → micro B E) :
  simp m1 m2 →
  simp (try2 m1 k) (try2 m2 k).
Proof.
  induction 1; simpl;
  rewrite ?try2_try2, ?pftry2_join1, ?pftry2_join2, ?try2_continue,
    ?try2_discontinue;
  econstructor; eauto.
  apply (SimpParThrowAgree e m1 m2); auto. constructor.
Qed.

Lemma prove_simp_try2 {A B E' E} m a (k : outcome2 A E' -> micro B E) m' :
  simp m (ret a) ->
  simp (continue k a) m' ->
  simp (try2 m k) m'.
Proof.
  intros.
  eapply SimpTransitive. { eapply simp_try2; eauto. }
  assumption.
Qed.

Lemma simplify_try2 {A B E' E} n m1 m2 (k : outcome2 A E' → micro B E) :
  simplify n m1 m2 →
  simplify n (try2 m1 k) (try2 m2 k).
Proof.
  induction 1; simpl;
  rewrite ?try2_try2, ?pftry2_join1, ?pftry2_join2, ?try2_continue,
    ?try2_discontinue;
  econstructor; eauto using simp_try2.
Qed.

(* Simplification is compatible with [try]. *)

Lemma simp_try {A B E' E} m1 m2 (f : A → micro B E) (h : E' → _) :
  simp m1 m2 →
  simp (try m1 f h) (try m2 f h).
Proof.
  eapply simp_try2.
Qed.

(* The Try rule. *)

Lemma prove_simp_try {A B E' E m m' a} {f : A → micro B E} (h : E' → _) :
  simp m (ret a) →
  simp (f a) m' →
  simp (try m f h) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.

(* The Try rule when the computation fails. *)

Lemma prove_simp_try_throw {A B E' E m m'} e {f : A → micro B E} (h : E' -> micro B E) :
  simp m (throw e) →
  simp (h e) m' →
  simp (try m f h) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.


(* Simplification is compatible with [bind]. *)

Lemma simp_bind {A B E} m1 m2 (f : A → micro B E) :
  simp m1 m2 →
  simp (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simp_try.
Qed.

(* The Bind rule. *)

Lemma prove_simp_bind {A B E m m' a} {f : A → micro B E} :
  simp m (ret a) →
  simp (f a) m' →
  simp (bind m f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* Inversion lemmas and tactics. *)

(* [ret _] cannot be simplified. *)

Lemma destruct_simplify_ret {A E} n a1 (m2 : micro A E) :
  simplify n (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_ret {A E} a1 (m2 : micro A E) :
  simp (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [crash] cannot be simplified. *)

Lemma destruct_simplify_crash {A E} n (m2 : micro A E) :
  simplify n crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_crash {A E} (m2 : micro A E) :
  simp crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [Throw _] cannot be simplified. *)

Lemma destruct_simplify_throw {A E} n e (m2 : micro A E) :
  simplify n (throw e) m2 →
  m2 = throw e.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_throw {A E} e (m2 : micro A E) :
  simp (throw e) m2 →
  m2 = throw e.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [perform e k] can be simplified
   by performing simplification inside [k].
   No other simplification is possible. *)

Lemma destruct_simplify_perform {A E} n e k (m' : micro A E) :
  simplify n (Stop CPerform e k) m' →
  ∃ k',
  m' = Stop CPerform e k' ∧
  ∀ o, simp (k o) (k' o).
Proof.
  intros h; dependent induction h; eauto with simp.
  (* SimplifyTransitive *)
  { destruct (IHh1 _ _ eq_refl) as (k1 & ? & ?). subst.
    destruct (IHh2 _ _ eq_refl) as (k2 & ? & ?). subst.
    eauto with simp. }
Qed.

Lemma destruct_simp_perform {A E} e k (m' : micro A E) :
  simp (Stop CPerform e k) m' →
  ∃ k',
  m' = Stop CPerform e k' ∧
  ∀ o, simp (k o) (k' o).
Proof.
  intros (n & ?)%simp_simplify. eauto using destruct_simplify_perform.
Qed.

(* These tactics apply the above lemmas, if possible. *)

Ltac clarify_simplify :=
  repeat match goal with
  | h: simplify _ (ret _) ?m |- _ => apply destruct_simplify_ret in h
  | h: simplify _ crash ?m |- _ => apply destruct_simplify_crash in h
  | h: simplify _ (throw _) ?m |- _ => apply destruct_simplify_throw in h
  | h: simplify _ (Stop CPerform _ _) ?m' |- _ =>
      apply destruct_simplify_perform in h;
      destruct h as (? & ? & ?)
  end; simplify_eq.

Ltac clarify_simp :=
  repeat match goal with
  | h: simp (ret _) ?m |- _ => apply destruct_simp_ret in h
  | h: simp crash ?m |- _ => apply destruct_simp_crash in h
  | h: simp (throw _) ?m |- _ => apply destruct_simp_throw in h
  | h: simp (Stop CPerform _ _) ?m' |- _ =>
      apply destruct_simp_perform in h;
      destruct h as (? & ? & ?)
  end; simplify_eq.

(* -------------------------------------------------------------------------- *)

(* A category of final terms, which cannot be simplified
   and cannot step. *)

Definition final {A E} (m : micro A E) :=
  match m with
  | Ret _ | Throw _ | Crash => True
  | _                       => False
  end.

Lemma destruct_simplify_final {A E n} {m1 m2 : micro A E} :
  simplify n m1 m2 →
  final m1 →
  m2 = m1.
Proof.
  intros. destruct m1; clarify_simplify; tauto.
Qed.

Lemma destruct_step_final {A E} σ1 σ2 (m1 m2 : micro A E) :
  step (σ1, m1) (σ2, m2) →
  final m1 →
  False.
Proof.
  intros. destruct m1; destruct_step; tauto.
Qed.

Ltac destruct_simplify_final :=
  match goal with h1: simplify _ ?m1 ?m2, h2: final ?m1 |- _ =>
    pose proof (destruct_simplify_final h1 h2); subst m2
  end.

Ltac prove_final :=
  first [ exact I | eauto ].

(* -------------------------------------------------------------------------- *)

(* Destruction lemmas and tactic. *)

(* In principle, we should be able to use [dependent destruction h] directly
   in the definition of the tactic [destruct_steps]. The two lemmas below
   would then not be necessary. However, attempting to do this fails. The
   lemmas are accepted, but Coq 8.16.1 signals a Universe Inconsistency when
   this file is later loaded. *)

Lemma invert_steps_0 {A E} {c c' : config A E} :
  steps 0 c c' →
  c' = c.
Proof.
  inversion 1; eauto.
Qed.

Local Ltac destruct_steps :=
  repeat match goal with
  | h: steps 0 _ _ |- _ => apply invert_steps_0 in h; simplify_eq
  | h: steps 1 _ _ |- _ => apply nsteps_once_inv in h
end.

(* -------------------------------------------------------------------------- *)

(* [steps n] is compatible with a [Par] context. *)

Local Lemma steps_step_par_left
  {A1 A2 A E' E} n σ σ' m1 m'1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  steps n (σ, m1) (σ', m'1) →
  steps n (σ, Par m1 m2 k) (σ', Par m'1 m2 k).
Proof.
  (* Massage the goal: *)
  remember (σ, m1) as c. remember (σ', m'1) as c'. intro h.
  revert c c' h σ m1 σ' m'1 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config; econstructor.
  eapply StepParLeft; eassumption.
  eapply IHh; reflexivity.
Qed.

Local Lemma steps_step_par_right
  {A1 A2 A E' E} n σ σ' m1 m2 m'2 (k : outcome2 (A1 * A2) E' → micro A E) :
  steps n (σ, m2) (σ', m'2) →
  steps n (σ, Par m1 m2 k) (σ', Par m1 m'2 k).
Proof.
  (* Massage the goal: *)
  remember (σ, m2) as c. remember (σ', m'2) as c'. intro h.
  revert c c' h σ m2 σ' m'2 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config; econstructor.
  eapply StepParRight; eassumption.
  eapply IHh; reflexivity.
Qed.

Local Hint Resolve
  steps_step_par_left
  steps_step_par_right
: step.

(* -------------------------------------------------------------------------- *)

(* The following commutation diagram claims that if out of [(σ, m1)] there
   is both a simplification step and a reduction step, then this diagram can
   be closed via at most one reduction step.

   More precisely, the diagram is closed using [i] reduction steps, where
   [i] is either 0 or 1. Furthermore:

   - If [i] is 0 then the diagram guarantees [n' < n], that is, the diagram
     is closed using a simplification step that is shorter than the original
     simplification step. Intuitively, this means that the original
     reduction and simplification steps both go in the same direction. This
     guarantee is later necessary to prove the lemma [wp_simplify].

   - If [i] is 1 then the diagram guarantees [n' ≤ n]. This guarantee is
     necessary for the inductive proof of the diagram to go through; indeed,
     it is exploited in the case of [SimplifyTransitive]. It is not needed
     in the proof of [wp_simplify].

   Intuitively, this simulation diagram that applying a simplification step
   never causes the loss of a reduction step. In other words, applying a
   simplification step does not eliminate any permitted behavior. *)

Lemma simplify_step_diagram {A E n} {m1 m2 : micro A E} :
  (* If there is a simplification step of size [n]: *)
  simplify n m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the diagram can be closed using *)
  ∃ m'2 i n',
  (* [i] reduction steps *)
  steps i (σ, m2) (σ', m'2) ∧
  (* and a simplication step of size [n'] *)
  simplify n' m'1 m'2 ∧
  (* where [i] and [n'] satisfy the following constraint: *)
  (i = 0 ∧ n' < n  ∨  i = 1 ∧ n' ≤ n).
Local Ltac search :=
  do 3 eexists;
  eauto 8 using step_try2, simplify_try2 with steps step simplify simp lia.
Local Ltac use_ih :=
  match goal with
  Hstep: step (_, ?m) _,
  IH: ∀ _ _ _, step (_, ?m) _ → _ |- _ =>
    specialize (IH _ _ _ Hstep);
    destruct IH as (? & ? & ? & ? & ? & ?)
  end.
Ltac destruct_simplify_step_diagram :=
  match goal with h: _ ∨ _ |- _ => destruct h as [ (? & ?) | (? & ?) ] end;
  subst; destruct_steps.
Proof.
  (* A model of a beautiful proof. *)
  induction 1; intros.
  (* SimplifyEval *)
  { destruct_step. search. }
  (* SimplifyLoop *)
  { destruct_step. search. }
  (* SimplifyFlipAgree *)
  { destruct_step. destruct b; search. }
  (* SimplifyParRetLeft *)
  (* This case is the reason why [SimplifyPerform] is needed. *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyParRetRight *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyPar *)
  { destruct_step; clarify_simplify; try solve [ search | use_ih; search ]. }
  (* SimplifyParThrowAgree *)
  { destruct_step; clarify_simplify; try solve [ search ];
      use_ih; destruct_simplify_step_diagram; try solve [ search ]; inversion H2. }
  (* SimplifyPerform *)
  { destruct_step. }
  (* SimplifyHandleRet *)
  { destruct_step; clarify_simplify; try solve [ search | use_ih; search ].
    use_ih. destruct_simplify_step_diagram; try solve [ search ].
    inversion H1. }
  (* SimplifyHandleThrow *)
  { destruct_step; clarify_simplify; try solve [ search | use_ih; search ].
    use_ih. destruct_simplify_step_diagram; try solve [ search ].
    inversion H1. }
  (* SimplifyReflexive *)
  { search. }
  (* SimplifyTransitive *)
  { use_ih; destruct_simplify_step_diagram; [| use_ih ]; search. }
Qed.

(* In the special case where [m2] is final, the previous
   diagram can be simplified, because [m2] cannot step. *)

Lemma simplify_final_step_diagram {A E n} {m1 m2 : micro A E} {σ σ' m'1} :
  (* If there is a simplification step of [m1] to [m2], *)
  simplify n m1 m2 →
  (* if there is also a reduction step out of [m1], *)
  step (σ, m1) (σ', m'1) →
  (* and if [m2] is final, *)
  final m2 →
  (* then this reduction step must take us closer to [m2]. *)
  ∃ n',
  σ' = σ ∧
  simplify n' m'1 m2 ∧
  n' < n.
Proof.
  intros Hsimp Hstep Hfinal.
  destruct (simplify_step_diagram Hsimp Hstep) as (? & ? & ? & ? & ? & ?).
  destruct_simplify_step_diagram.
  { eauto. }
  { exfalso; eauto using destruct_step_final. }
Qed.

Ltac simplify_final_step_diagram :=
  match goal with
  Hsimp: simplify _ ?m1 ?m2,
  Hstep: step (_, ?m1) _
  |- _ =>
    let n' := fresh "n'" in
    destruct (simplify_final_step_diagram Hsimp Hstep)
      as (n' & -> & ? & ?);
      [ prove_final |]
  end.

(* -------------------------------------------------------------------------- *)

(* If there is a simplification path from [m1] to [m2],
   where [m2] is final,
   then there must be a reduction path from [m1] to [m2]. *)

Local Hint Constructors rtc : rtc.

Lemma simplify_final_implies_rtc_step :
  ∀ {n A E} {m1 m2 : micro A E},
  simplify n m1 m2 →
  final m2 →
  ∀ σ,
  rtc step (σ, m1) (σ, m2).
Proof.
  induction n using (well_founded_induction lt_wf).
  (* Reformulate the induction hypothesis. *)
  assert (IH:
    ∀ n' {A E} σ (m1 m2 : micro A E),
    simplify n' m1 m2 →
    final m2 →
    n' < n →
    rtc step (σ, m1) (σ, m2)
  ) by eauto; clear H.
  intros A E m1 m2 Hsimp Hfinal σ.
  (* Reason by cases on [m1]. *)
  triplicity σ m1 Hm1.
  (* Case: [m1] is [ret _]. *)
  { clarify_simplify. eauto with rtc. }
  (* Case: [m1] can step. *)
  { destruct Hm1 as ((σ' & m'1) & Hstep).
    simplify_final_step_diagram.
    (* IH is used. *)
    eauto with rtc. }
  (* Case: [m1] is stuck. *)
  { apply only_crash_and_throw_and_perform_are_stuck in Hm1.
    destruct Hm1 as [| [(e & ?) | (e & k & ?)]]; subst m1; simpl in Hfinal;
    clarify_simplify; solve [ eauto with rtc | tauto ]. }
Qed.

(* If there is a simplification step of [m1] to [m'1]
   and a reduction path of [m1] to [m2],
   where [m'1] and [m2] are final,
   then the two paths must lead to the same end result. *)

Lemma simplify_final_rtc_step_diagram
  {A E n} {m1 m'1 m2 : micro A E} {σ σ'} :
  simplify n m1 m'1 →
  rtc step (σ, m1) (σ', m2) →
  final m'1 →
  final m2 →
  σ' = σ ∧ m2 = m'1.
Proof.
  (* Reformulate the statement. *)
  cut (
    ∀ (c1 c2 : config A E),
    rtc step c1 c2 →
    ∀ σ σ' m1 m'1 m2 n,
    simplify n m1 m'1 →
    final m'1 →
    final m2 →
    c1 = (σ, m1) →
    c2 = (σ', m2) →
    σ' = σ ∧ m2 = m'1
  ). eauto. clear n m1 m'1 m2 σ σ'.
  (* Reason by induction on the reduction path. *)
  induction 1; intros; simplify_eq; clarify_simplify; destruct_config.
  (* The base case is immediate. *)
  { destruct_simplify_final. eauto. }
  (* In the other case, we are looking at a reduction step. We then
     exploit the fact that each reduction step must take us closer
     to [m'1], which is the target of the simplification path. *)
  simplify_final_step_diagram.
  eauto.
Qed.

(* The relation [simplify _], restricted to final results, is confluent.
   That is, simplification cannot lead to two distinct final results. *)

Lemma simplify_final_confluent {A E} {m m1 m2 : micro A E} {n1 n2} :
  simplify n1 m m1 →
  simplify n2 m m2 →
  final m1 →
  final m2 →
  m1 = m2.
Proof.
  intros Hsimp1 Hsimp2 Hfinal1 Hfinal2.
  pose proof (simplify_final_implies_rtc_step Hsimp1 Hfinal1 ∅) as Hpath.
  pose proof (simplify_final_rtc_step_diagram Hsimp2 Hpath Hfinal2 Hfinal1)
    as (_ & ?).
  eauto.
Qed.

Lemma simp_final_confluent {A E} {m m1 m2 : micro A E} :
  simp m m1 →
  simp m m2 →
  final m1 →
  final m2 →
  m1 = m2.
Proof.
  intros (n1 & H1)%simp_simplify (n2 & H2)%simp_simplify.
  eauto using simplify_final_confluent.
Qed.

Ltac simp_final_confluent :=
  match goal with
  | h1: simp ?m ?m1, h2: simp ?m ?m2 |- _ =>
      assert (m1 = m2); [
        eapply (simp_final_confluent h1 h2); prove_final
      | simplify_eq ]
  end.
(* -------------------------------------------------------------------------- *)

(* The following are (weakened) reformulations of the previous two lemmas
   in terms of [simp]. *)

Lemma simp_step_diagram {A E} {m1 m2 : micro A E} :
  (* If there is a simplification step: *)
  simp m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the diagram can be closed using *)
  ∃ m'2 i,
  (* [i] reduction steps *)
  steps i (σ, m2) (σ', m'2) ∧
  (* and a simplication step *)
  simp m'1 m'2 ∧
  (* where [i] is at most 1. *)
  (i = 0 ∨ i = 1).
Local Ltac simp_search :=
  do 2 eexists;
  eauto 8 using step_try2, simp_try2 with steps step simp lia.
Local Ltac simp_use_ih :=
  match goal with
  Hstep: step (_, ?m) _,
  IH: ∀ _ _ _, step (_, ?m) _ → _ |- _ =>
    specialize (IH _ _ _ Hstep);
    destruct IH as (? & ? & ? & ? & ?)
  end.
Ltac destruct_simp_step_diagram :=
  match goal with h: _ ∨ _ |- _ => destruct h as [ ? | ? ] end;
  subst; destruct_steps.
Proof.
  (* A model of a beautiful proof. *)
  induction 1; intros.
  (* SimpEval *)
  { destruct_step. simp_search. }
  (* SimpLoop *)
  { destruct_step. simp_search. }
  (* SimpFlipAgree *)
  { destruct_step; destruct b; simp_search. }
  (* SimpParRetLeft *)
  (* This case is the reason why [SimpPerform] is needed. *)
   { destruct_step; try solve [destruct_step]; clarify_simp; simp_search.
    split.
    - eauto 8 using step_try2, simp_try2 with steps step simp lia.
    - split; last lia.
      eapply SimpTransitive.
      + eapply SimpPerform.
        intros; eapply SimpParRetLeft.
      + cbn. auto with simp. }
  (* SimpParRetRight *)
  { destruct_step; try solve [destruct_step]; clarify_simp; simp_search.
    split.
    - eauto 8 using step_try2, simp_try2 with steps step simp lia.
    - split; last lia.
      eapply SimpTransitive.
      + eapply SimpPerform.
        intros; eapply SimpParRetRight.
      + cbn. auto with simp. }
  (* SimpPar *)
  { destruct_step; clarify_simp; try solve [ simp_search | simp_use_ih; simp_search ]. }
  (* SimpParThrowAgree *)
  { destruct_step; clarify_simp; try solve [ simp_search ];
      simp_use_ih; inversion H2; subst; try solve [ simp_search ]; inversion H5. }
  (* SimpPerform *)
  { destruct_step. }
  (* SimpHandleRet *)
  { destruct_step; clarify_simp; try solve [ simp_search | simp_use_ih; simp_search ].
    simp_use_ih. destruct H3; subst; cycle 1.
    { inversion H1. subst. inversion H4. }
    inversion H1; subst.
    simp_search. }
  (* SimpHandleThrow *)
  { destruct_step; clarify_simp; try solve [ simp_search | simp_use_ih; simp_search ].
    simp_use_ih. destruct H3; subst; cycle 1.
    { inversion H1. subst. inversion H4. }
    inversion H1; subst.
    simp_search. }
  (* SimpReflexive *)
  { simp_search. }
  (* SimpTransitive *)
  { simp_use_ih.
    destruct_simp_step_diagram; [| simp_use_ih ]; simp_search. }
Qed.

Ltac simp_step_diagram :=
  match goal with
  Hsimp: simp ?m1 _,
  Hstep: step (_, ?m1) _
  |- _ =>
    let Hstep' := fresh in
    let Hsimp' := fresh in
    let Hcases := fresh in
    pose proof (simp_step_diagram Hsimp Hstep)
      as (? & ? & Hstep' & Hsimp' & Hcases);
    clear Hsimp Hstep;
    rename Hsimp' into Hsimp;
    rename Hstep' into Hstep;
    destruct Hcases;
    subst; destruct_steps
  end.

Lemma simp_final_step_diagram {A E} {m1 m2 : micro A E} {σ σ' m'1} :
  (* If there is a simplification step of [m1] to [m2], *)
  simp m1 m2 →
  (* if there is also a reduction step out of [m1], *)
  step (σ, m1) (σ', m'1) →
  (* and if [m2] is final, *)
  final m2 →
  (* then this reduction step does not prevent us from reaching [m2]. *)
  σ' = σ ∧
    simp m'1 m2.
Proof.
  intros Hsimp Hstep Hfinal.
  destruct (simp_step_diagram Hsimp Hstep) as (? & ? & ? & ? & ?).
  destruct_simp_step_diagram.
  { eauto. }
  { exfalso; eauto using destruct_step_final. }
Qed.

Lemma simp_perform_step_diagram {A E} {m : micro A E} {σ σ' m'} v k:
  (* If there is a simplification step of [m] to a perform, *)
  simp m (Stop CPerform v k) →
  (* if there is also a reduction step out of [m], *)
  step (σ, m) (σ', m') →
  (* then this reduction step does not prevent us from reaching the perform. *)
  σ' = σ ∧
    simp m' (Stop CPerform v k).
Proof.
  intros Hsimp Hstep.
  simp_step_diagram; eauto.
  inversion Hstep.
Qed.

Ltac simp_final_step_diagram :=
  match goal with
    Hsimp: simp ?m1 ?m2,
      Hstep: step (_, ?m1) _
    |- _ =>
      destruct (simp_final_step_diagram Hsimp Hstep)
      as (-> & ?);
      [ prove_final |]
  end.

(* If there is a simplification path from [m1] to [m2],
   where [m2] is final,
   then there must be a reduction path from [m1] to [m2]. *)

Local Hint Constructors rtc : rtc.

(* -------------------------------------------------------------------------- *)

(* The following lemmas transport information in the reverse direction
   along the simplification relation. If [simplify _ m1 m2] holds, then
   information about [m2] can be transported to [m1]. *)

(* If [m1] can be simplified into [m2],
   and if [m2] can step,
   then [m1] can step. *)

Lemma invert_simp_can_step {A E} (m1 m2 : micro A E) σ :
  simp m1 m2 →
  can_step (σ, m2) →
  can_step (σ, m1).
Proof.
  (* Every term can step except [ret _], [throw _], [crash], and [perform _].
     So, all cases except these 4 cases are immediate. Furthermore, out of
     these four cases, the first three are also immediate, because [ret _],
     [throw _], and [crash] cannot be simplified. *)
  induction 1; eauto with step.
  (* So, only [perform _] remains. This case is also immediate, because
     [perform _] cannot step. *)
  intros. destruct_can_step. destruct_step.
Qed.

(* If [m1] can be simplified into a final result [m2] then
   either [m1] is [m2]
   or [m1] can step. *)

Lemma invert_simp_final {A E} {m1 m2 : micro A E} σ :
  simp m1 m2 →
  final m2 →
  m1 = m2 ∨
    can_step (σ, m1).
Proof.
  (* The only terms that cannot step are the final terms, and these
     terms cannot be simplified, so the result is almost immediate. *)
  intro h; dependent induction h; intros Hfinal; simpl in *;
    eauto with step.
  (* Only [SimpTransitive] requires some work. *)
  destruct (IHh2 Hfinal); clear IHh2; [ subst |].
  { destruct (IHh1 Hfinal); eauto. }
  { eauto using invert_simp_can_step. }
Qed.

(* If [m] can be simplified into a [Stop CPerform v k] then
   either [m] is a [Stop CPerform v k'] where k' can be simplified to k or
   or [m] can step. *)

Lemma invert_simp_perform {A E} {m : micro A E} σ v k :
  simp m (Stop CPerform v k) →
  match m with
  | Stop CPerform v' k' => v = v' /\ (forall o, simp (k' o) (k o))
  | _ => False
  end ∨
    can_step (σ, m).
Proof.
  intro h; dependent induction h; simpl in *;
    eauto with step.
  { left; split; eauto; constructor. }
  (* Only [SimpTransitive] requires some work. *)
  destruct (IHh2 _ _ eq_refl); clear IHh2; [ subst |].
  { destruct m2; try done. destruct c; try done. destruct H; subst.
    destruct (IHh1  _ _ eq_refl); eauto.
    left; auto.
    destruct m1; try done. destruct c; try done.
    destruct H; subst; split; eauto.
    intros; eapply SimpTransitive; eauto. }
  { eauto using invert_simp_can_step. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Potentially useful type class instances. *)

(* Instantiating [Reflexive] allows to use [reflexivity] to prove
   [simp ?m ?m]. *)
Global Instance TC_reflexivity_simp {A E} : Reflexive (@simp A E) :=
  SimpReflexive.

(* Instantiating [Transitive] allows to use [transitivity] (as well as
   [etransitivity] to prove [simp ?m ?m']. *)
Global Instance TC_transitivity_simp {A E} : Transitive (@simp A E) :=
  SimpTransitive.
