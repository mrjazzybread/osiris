From Coq Require Import FunctionalExtensionality.
From osiris Require Import base lang syntax.
From osiris.semantics Require Import code eval step.

(** [may] simplification relation *)

(* The [may] relation performs simplifications on pure subprograms, to be able
to have a pure reasoning mode simpler than the full separation logic framework.
In this way it is similar to the [simp] relation, but [may] allows
non-deterministic choices. The price to pay is the quantification over all
possible [may] paths.

The idea is that if you prove that some desired property holds for all final
states after pure reductions, then the corresponding wp holds for [m]; that's
the role of the [pure_wp] predicate, named as such as it is a kind of pure WP
definition for the [may] relation. In fact the [may] relation could be called
[pure_step] but it is not exactly that for now.

List of results to establish for a useful [pure_wp] relation:

- pure_wp_bind: [pure_wp m φ ψ] and [∀ a, φ a → pure_wp (k a) φ' ψ] imply
  [pure_wp (bind m k) φ' ψ]

- pure_wp_ewp: [pure_wp m φ ψ] implies [ewp m (ilift ⌜φ⌝ ⌜ψ⌝)]

- hoare reasoning on [pure_wp] (TODO) : see results about [pure] in
  [proofmode/simp_eval]) but this time more results can be included, allowing
  exceptions.

Compared to the [simp] relation, [may] is able to bypass some steps, for example
[Par m1 (throw e) k] is simplified into [k (Throw e)], which is one example of
non-determinism, since [m1] could throw a different exception.

Other differences with [simp]:

- [may] is not reflexive, otherwise the main construct of the [pure_wp]
  predicate would has its conclusion as a premise. For the same reason, one
  should not directly include [simp] in [may] (maybe [simplify (S _)] could be
  fine).

- transitivity is not included, which makes the relation simpler to reason
  about. Transitivity is necessary for [simp] to be able to ignore intermediate
  steps in case of temporary nondeterminism, for example in the different
  components of a [Choose].

- if [m] has side-effects, even under nested [Par]s, it can reach [crash] in
  some number of [may] steps, so that [pure_wp] computations are guaranteed to
  be pure. *)

Inductive may {A E} : micro A E → micro A E → Prop :=
| MayEval η e k:
  may
    (Stop CEval (η, e) k)
    (try2 (eval η e) k)
| MayLoop η x i1 i2 e k :
  may
    (Stop CLoop (η, x, i1, i2, e) k)
    (try2 (loop η x i1 i2 e) k)
| MayAlloc v k :
  may
    (Stop CAlloc v k)
    crash
| MayLoad lv k :
  may
    (Stop CLoad lv k)
    crash
| MayStore l k :
  may
    (Stop CStore l k)
    crash
| MayResume lo k :
  may
    (Stop CResume lo k)
    crash
| MayInstall t k :
  may
    (Stop CInstall t k)
    crash
| MayPerform e k :
  may
    (Stop CPerform e k)
    crash
| MayChooseLeft {B E'} m1 m2 (k : outcome2 B E' → _) :
  may
    (Choose m1 m2 k)
    (try2 m1 k)
| MayChooseRight {B E'} m1 m2 (k : outcome2 B E' → _) :
  may
    (Choose m1 m2 k)
    (try2 m2 k)
| MayParCrashLeft {A1 A2 E'} m2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par crash m2 k)
    crash
| MayParCrashRight {A1 A2 E'} m1 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par m1 crash k)
    crash
| MayParRetRet {A1 A2 E'} a1 a2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par (Ret a1) (Ret a2) k)
    (continue k (a1, a2))
| MayParThrowLeft {A1 A2 E'} e1 m2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par (Throw e1) m2 k)
    (k (O2Throw e1))
| MayParThrowRight {A1 A2 E'} m1 e2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par m1 (Throw e2) k)
    (k (O2Throw e2))
(* Two constructors for [Par]. Requiring both sides to simplify might complexify
   proofs, since the relation is not reflexive. *)
| MayParLeft {A1 A2 E'} m1 m'1 m2 (k : outcome2 (A1 * A2) E' → _) :
  may m1 m'1 →
  may (Par m1 m2 k) (Par m'1 m2 k)
| MayParRight {A1 A2 E'} m1 m2 m'2 (k : outcome2 (A1 * A2) E' → _) :
  may m2 m'2 →
  may (Par m1 m2 k) (Par m1 m'2 k)
(* For the same reason [may] does not need transitivity, the constructors for
   [Handle] are slightly simpler than for [simp] as there is no need to resolve
   temporary nondeterminism *)
| MayHandleRet v h :
  may
    (Handle (Ret v) h)
    (continue h v)
| MayHandleThrow e h :
  may
    (Handle (Throw e) h)
    (discontinue h e)
| MayHandlePerform e h k :
  may
    (Handle (Stop CPerform e k) h)
    crash
| MayHandleCrash h :
  may
    (Handle crash h)
    crash
| MayHandle m m' h :
  may m m' →
  may
    (Handle m h)
    (Handle m' h).

Global Hint Constructors may : may.


(* The following statements, that one may expect, do not hold.

may m m' → ∀ σ, step (σ, m) (σ, m')

may m m' → ∀ σ, ∃ m'', step (σ, m) (σ, m'')

First, because [may] takes a shortcut as soon as [ret] or [throw] is present in
a [Par], with with no corresponding [step] constructor. (To circumvent this
problem, a simulation statement might be established.)

Second, because [Par (Ret _) (Stop CStore _ _) _] can only [step] to a different
store when the initial store fits. For this, we could forbid all impurities
syntactically by requiring some [immediately_pure] predicate a every step in the
definition of [pure_wp], but we choose here to make impurities reduce to
[crash]. *)


(* Computations are either final or may reduce *)

Lemma may_cases {A E} (m : micro A E) :
  m = crash ∨ (∃ a, m = ret a) ∨ (∃ e, m = throw e) ∨ (∃ m', may m m').
Proof.
  induction m; eauto with may;
    firstorder; subst; eauto 10 with may.
  destruct c; eauto with may.
  - destruct x; eauto with may.
  - destruct x as [[[[]]]]; eauto with may.
Qed.


(** Compatibility of [may] with [bind] *)

Lemma may_try2 {A B E E'} (m m' : micro A E) (f : outcome2 A E → micro B E') :
  may m m' → may (try2 m f) (try2 m' f).
Proof.
  induction 1; eauto; try solve [ inversion 1 ]; simpl;
    try constructor; auto;
    rewrite try2_try2, ?pftry2_join1, ?pftry2_join2;
    constructor.
Qed.

Lemma may_bind {A B E} (m m' : micro A E) (k : A → micro B E) :
  may m m' → may (bind m k) (bind m' k).
Proof.
  rewrite !bind_as_try2. eapply may_try2.
Qed.


(** Inversion lemmas *)

(* The first inversion lemmas are simple but useful since because of dependent
   equality [inversion] is tedious to use by itself. We use the classical
   property [inj_pair2], which is a consequence of the axiom of the excluded
   middle. *)

Ltac eq_dep_inj :=
  repeat match goal with
    | H : existT ?A ?x = existT ?A ?y |- _ =>
        apply Classical_Prop.EqdepTheory.inj_pair2 in H
    end.

Lemma Stop_inj {A E X Y E'} (c : C.code X Y E') x1 x2 (k1 k2 : _ → micro A E) :
  Stop c x1 k1 = Stop c x2 k2 → x1 = x2 ∧ k1 = k2.
Proof.
  injection 1 as Ecfg Ek.
  by eq_dep_inj.
Qed.

Lemma invert_may_crash A E (m : micro A E) : may crash m → False.
Proof.
  inversion 1.
Qed.

Lemma invert_may_ret A E a (m : micro A E) : may (ret a) m → False.
Proof.
  inversion 1.
Qed.

Lemma invert_may_throw {A E} e (m : micro A E) : may (throw e) m → False.
Proof.
  inversion 1.
Qed.

Lemma invert_may_eval {A E} (m' : micro A E) ηe k:
  may (Stop CEval ηe k) m' → m' = try2 (eval (fst ηe) (snd ηe)) k.
Proof.
  remember (Stop _ _ _); intros M; revert ηe k Heqm.
  inversion M; subst; intros (η_, e_) k_ Heq; try solve [inversion Heq].
  apply Stop_inj in Heq. by destruct Heq as [[=<-<-] <-].
Qed.

Lemma invert_may_loop {A E} (m' : micro A E) t k:
  may (Stop CLoop t k) m' →
  match t with (η, x, i1, i2, e) => m' = try2 (loop η x i1 i2 e) k end.
Proof.
  remember (Stop _ _ _); intros M; revert t k Heqm.
  inversion M; subst; intros [[[[]]]] k_ Heq; try solve [inversion Heq].
  apply Stop_inj in Heq. destruct Heq as [[=] <-]. congruence.
Qed.

Lemma invert_may_par {A1 A2 E A E'} (k : outcome2 (A1 * A2) E → micro A E') m1 m2 m' :
  may (Par m1 m2 k) m' →
  (∃ a1 a2, m1 = ret a1 ∧ m2 = ret a2 ∧ m' = continue k (a1, a2)) ∨
  (∃ m1', may m1 m1' ∧ m' = Par m1' m2 k) ∨
  (∃ m2', may m2 m2' ∧ m' = Par m1 m2' k) ∨
  (∃ e1, m1 = throw e1 ∧ m' = k (O2Throw e1)) ∨
  (∃ e2, m2 = throw e2 ∧ m' = k (O2Throw e2)) ∨
  ((m1 = crash ∨ m2 = crash) ∧ m' = crash).
Proof.
  inversion 1; subst; eq_dep_inj; subst; eauto 15.
Qed.

Lemma invert_may_choose {A E B E'} (k : outcome2 B E' → micro A E) m1 m2 m' :
  may (Choose m1 m2 k) m' →
  m' = try2 m1 k ∨ m' = try2 m2 k.
Proof.
  inversion 1; subst; eq_dep_inj; subst; eauto 15.
Qed.

Lemma invert_may_try2 {A B E E'} (m : micro A E') (f : outcome2 A E' → micro B E) (m1 : micro B E) :
  may (try2 m f) m1 →
  (∃ m', may m m' ∧ m1 = try2 m' f) ∨
  (∃ a, m = ret a ∧ may (f (O2Ret a)) m1) ∨
  (∃ e, m = throw e ∧ may (f (O2Throw e)) m1).
Proof.
  revert m1; induction m; intros m'.
  - firstorder.
  - firstorder.
  - inversion 1.
  - inversion 1; subst; now repeat econstructor.
  - intros M.
    destruct c; try solve [inversion M; subst; eq_dep_inj; subst; eauto with may].
    + (* Stop CEval *)
      left. simpl in M.
      apply invert_may_eval in M. subst.
      destruct x as (η, e).
      repeat econstructor.
      by rewrite try2_try2.
    + (* Stop CLoop *)
      left. simpl in M; apply invert_may_loop in M; subst.
      destruct x as [[[[]]]].
      repeat econstructor. subst.
      by rewrite try2_try2.
  - (* Par: all [may] shortcuts commute with [bind] *)
    simpl; intros M. left.
    apply invert_may_par in M.
    firstorder; subst.
    all: try solve [repeat (econstructor; eauto)]; repeat econstructor.
    all: rewrite ?try2_try2, ?pftry2_join1, ?pftry2_join2; auto.
  - (* Choose *)
    simpl. intros [-> | ->]%invert_may_choose; left; eexists; split.
    1: apply MayChooseLeft.
    2: apply MayChooseRight.
    1,2 : rewrite ?try2_try2; auto.
Qed.

Lemma invert_may_bind {A B E} (m : micro A E) (k : A → micro B E) (m1 : micro B E) :
  may (bind m k) m1 →
  (∃ m', may m m' ∧ m1 = bind m' k) ∨
  (∃ a, m = ret a ∧ may (k a) m1) ∨
  m1 = crash.
Proof.
  rewrite bind_as_try2.
  intros [(m' & Hm & ->)|[(a & -> & Ha)|(e & -> & He)]]%invert_may_try2.
  - rewrite <-bind_as_try2; firstorder.
  - firstorder.
  - inversion He.
Qed.


Global Hint Resolve invert_may_ret invert_may_throw invert_may_crash
  invert_may_eval invert_may_par invert_may_choose
  invert_may_try2 invert_may_bind
  : invert_may.


(** The [pure_wp] predicate *)

(* [pure_wp m φ ψ] states that [m] is either a value satisfying [φ], a raised
exception satisfying [ψ], or can only do pure [may] reduction steps to states
[m'] also satisfying [pure_wp m' φ ψ]. It is somewhat a terminating and pure
version of the standard WP. *)

Inductive pure_wp {A E} : micro A E → (A → Prop) → (E → Prop) → Prop :=
  | pure_wp_ret (φ : A → Prop) ψ a : φ a → pure_wp (ret a) φ ψ
  | pure_wp_throw φ (ψ : E → Prop) e : ψ e → pure_wp (throw e) φ ψ
  | pure_wp_may φ ψ m :
    (∃ m', may m m') →
    (∀ m', may m m' → pure_wp m' φ ψ) →
    pure_wp m φ ψ.

Global Hint Constructors pure_wp : pure_wp.


(* [pure_wp] is preserved by [may] steps *)

Lemma pure_wp_may_forward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
  pure_wp m φ ψ → may m m' → pure_wp m' φ ψ.
Proof.
  induction 1; auto; inversion 1.
Qed.


(** Inversion lemmas *)

Lemma invert_pure_wp_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) :
  pure_wp crash φ ψ → False.
Proof.
  inversion 1; subst. firstorder eauto with invert_may.
Qed.

Lemma invert_pure_wp_ret {A E : Type} (φ : A → Prop) (ψ : E → Prop) a :
  pure_wp (ret a) φ ψ → φ a.
Proof.
  intros S; remember (ret a) as m; revert a Heqm.
  induction S; try congruence. intros ? ->. exfalso. firstorder eauto with invert_may.
Qed.

Lemma invert_pure_wp_throw {A E : Type} (φ : A → Prop) (ψ : E → Prop) e :
  pure_wp (throw e) φ ψ → ψ e.
Proof.
  intros S; remember (throw e) as m; revert e Heqm.
  induction S; try congruence. intros ? ->. exfalso. firstorder eauto with invert_may.
Qed.

Lemma invert_pure_wp_may_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) m :
  may m crash → pure_wp m φ ψ → False.
Proof.
  eauto using invert_pure_wp_crash, pure_wp_may_forward.
Qed.

Lemma invert_pure_wp_may_may_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
  may m m' → may m' crash → pure_wp m φ ψ → False.
Proof.
  eauto using invert_pure_wp_crash, pure_wp_may_forward.
Qed.

Lemma invert_pure_wp_stop {A E X Y E'} (φ : A → Prop) (ψ : E → Prop) (c : code X Y E') (x : X) k :
  pure_wp (Stop c x k) φ ψ → match c with CEval | CLoop => True | _ => False end.
Proof.
  intros S. inversion S; subst.
  destruct H as (m', Hm'). assert (Wm' : pure_wp m' φ ψ) by eauto.
  destruct c; inversion Hm'; eq_dep_inj; subst; auto;
    eapply invert_pure_wp_may_crash; eauto.
Qed.


(** [pure_wp] is preserved by binds *)

Lemma pure_wp_try2 {A' A E E'} (φ : A → Prop) (ψ : E → Prop) (φ' : A' → Prop) (ψ' : E' → Prop) m f :
  pure_wp m φ ψ →
  (∀ a, φ a → pure_wp (f (O2Ret a)) φ' ψ') →
  (∀ e, ψ e → pure_wp (f (O2Throw e)) φ' ψ') →
  pure_wp (try2 m f) φ' ψ'.
Proof.
  induction 1 as [ Ha | e | φ ψ m Hex Hm IHm]; intros Hv He; simpl; eauto.
  assert (Sm : pure_wp m φ ψ) by now econstructor.
  constructor.
  - destruct Hex as (m', Hm'). eexists. by apply may_try2.
  - intros m1 [(m' & Hm' & ->) | [(a & -> & Hm1) | (e & -> & Hm1)]]%invert_may_try2; eauto.
    eapply pure_wp_may_forward; eauto. apply invert_pure_wp_ret in Sm; auto.
    eapply pure_wp_may_forward; eauto. apply invert_pure_wp_throw in Sm; auto.
Qed.

Lemma pure_wp_bind {A' A E} (φ : A → Prop) (ψ : E → Prop) (φ' : A' → Prop) m k :
  pure_wp m φ ψ →
  (∀ a, φ a → pure_wp (k a) φ' ψ) →
  pure_wp (bind m k) φ' ψ.
Proof.
  rewrite bind_as_try2. intros. eapply pure_wp_try2; eauto.
  by constructor.
Qed.


(** Local [is_pure] predicate *)

(* This local definition of [is_pure] is defined as [pure_wp] with trivial
postconditions. It is useful to state inversion lemmas about [pure_wp] when the
types change, since new φ/ψ predicates must change too. Another name for it
could be [safe] or [purely_safe], since it is a WP with trivial postconditions.

It is not intended to be used outside this file and is only used in the proof of
[pure_wp_preservation].

Using a [pure_wp] definition with an [immediately_pure] predicate mentioned
above would mean we do not need the invertion lemmas and [is_pure_step_may]
would only have [immediately_pure m] as precondition. *)

Section is_pure.

  Local Definition is_pure {A E} (m : micro A E) := pure_wp m (λ _, True) (λ _, True).

  Lemma pure_wp_is_pure {A E : Type} {φ ψ} (m : micro A E) :
    pure_wp m φ ψ → is_pure m.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Lemma invert_is_pure_try2 {A1 E1 B E'} (m : micro A1 E1) (k : _ → micro B E') :
    is_pure (try2 m k) → is_pure m.
  Proof.
    remember (try2 m k) as mt; intros PS; revert m Heqmt.
    induction PS as [ |  | φ ψ m Hex HF IH]; intros m1 Hm1;
      (* if [try2 m k] is [ret] or [throw] then [m] is, as well, so is safe *)
      try solve [ destruct m1; try discriminate; by constructor ].
    (* otherwise [m] reduces to some [m'], and all such [m'] are safe  *)
    subst.
    (* from the fact that [try2 m1 k] reduce to [m']: *)
    destruct Hex as (m', [(m1' & Hm1 & ->) | ?]%invert_may_try2).
    - (* either [m1] reduces to [m1'] and [m' = try2 m1' k], conclude by IH *)
      constructor; eauto. intros m2 Hm2.
      eapply IH; eauto. by apply may_try2.
    - (* or [m1] is [ret] or [throw] and so is safe *)
      by hnf; firstorder (subst; eauto with pure_wp).
  Qed.

  Lemma invert_is_pure_par {A E A1 A2 E'} m1 m2 (k :  outcome2 (A1 * A2) E' → micro A E) :
    is_pure (Par m1 m2 k) → is_pure m1 ∧ is_pure m2.
  Proof.
    remember (Par m1 m2 k) as m; intros PS; revert m1 m2 Heqm.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
    split.
    - destruct (may_cases m1) as [-> | [ | [ | Hm1 ]]].
      now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
      now firstorder (subst; econstructor; eauto).
      now firstorder (subst; econstructor; eauto).
      constructor; auto. intros m1' Hm1'.
      eapply IH; eauto with may.
    - destruct (may_cases m2) as [-> | [ | [ | Hm1 ]]].
      now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
      now firstorder (subst; econstructor; eauto).
      now firstorder (subst; econstructor; eauto).
      constructor; auto. intros m1' Hm1'.
      eapply IH; eauto with may.
  Qed.

  Lemma invert_is_pure_handle {A E} m (h : _ → micro A E) :
    is_pure (Handle m h) → is_pure m.
  Proof.
    remember (Handle m h) as m1; intros PS; revert m Heqm1.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m_ ->.
    destruct (may_cases m_) as [-> | [ | [ | Hm1 ]]].
    now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
    now firstorder (subst; econstructor; eauto).
    now firstorder (subst; econstructor; eauto).
    constructor; auto. intros m1' Hm1'.
    apply (IH _ ltac:(eauto with may) _ eq_refl).
  Qed.

  (* Steps from pure computations necessarily are [may] and preserve the store *)
  Lemma is_pure_step_may {A E : Type} (m : micro A E) {σ m' σ'} :
    is_pure m → step (σ, m) (σ', m') → may m m' ∧ σ' = σ.
  Proof.
    intros Hm Hstep. revert Hm.
    (* this dep. induction uses the [eq_rect_eq] axiom. If problematic, can be
       removed by generalizing (σ, m) and (σ', m') *)
    dependent induction Hstep; intros Hm.

    (* Simple pure steps result in goals of the form [σ' = σ' ∧ may m1 m2] that
       correspond to a single [may] constructor: *)
    all: try solve [auto with may].

    (* Contradiction if [pure_wp m _ _] and [m] reduces to [crash] *)
    all: try solve [by eapply invert_pure_wp_may_crash in Hm; eauto with may].
    (* same if [m] reduces to [crash] in two steps*)
    all: try solve [by eapply invert_pure_wp_may_may_crash in Hm; eauto with may].

    (* Remains to prove the three recursive cases of [step] *)
    - (* [handle] *)
      inversion Hm as [ | | ? ? ? (m', Hm') Hfo]; subst.
      inversion Hm'; subst; try by inversion Hstep.
      destruct (IHHstep _ _ _ _ JMeq_refl JMeq_refl). 
      eapply invert_is_pure_handle in Hm; apply Hm.
      auto with may.
    - (* [Par] left *)
      destruct (IHHstep _ _ _ _ JMeq_refl JMeq_refl).
      eapply invert_is_pure_par in Hm; apply Hm.
      eauto with may.
    - (* [Par] right *)
      destruct (IHHstep _ _ _ _ JMeq_refl JMeq_refl).
      eapply invert_is_pure_par in Hm; apply Hm.
      eauto with may.
  Qed.

End is_pure.


(** [pure_wp] : progress and preservation *)

Lemma pure_wp_progress {A E : Type} {φ : A → Prop} {ψ : E → Prop} m :
  pure_wp m φ ψ → (∃ a, m = ret a) ∨ (∃ e, m = throw e) ∨ ∀ σ, can_step (σ, m).
Proof.
  intros Hm.
  destruct m; eauto.
  - by apply invert_pure_wp_crash in Hm.
  - eauto using can_step_handle.
  - right; right; intros.
    apply can_step_stop.
    apply invert_pure_wp_stop in Hm.
    destruct c; auto.
  - eauto using can_step_par.
  - eauto using can_step_choose.
Qed.

Lemma pure_wp_preservation {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
  pure_wp m φ ψ → step (σ, m) (σ', m') → pure_wp m' φ ψ ∧ σ' = σ.
Proof.
  intros Hm Hstep.
  destruct (is_pure_step_may _ (pure_wp_is_pure _ Hm) Hstep).
  eauto using pure_wp_may_forward.
Qed.


(** Encode compatibility *)

Definition encode_pred `{Encode A} (φ : A → Prop) := λ v, ∃ a, v = #a ∧ φ a.

Definition pure_wp_encode `{Encode A} {E} (m : micro val E) (φ : A → Prop) (ψ : E → Prop) :=
  pure_wp m (encode_pred φ) ψ.


(** Hoare reasoning rules *)

Lemma pure_wp_seq φ ψ η e1 e2 :
  pure_wp (eval η e1) (λ _, pure_wp (eval η e2) φ ψ) ψ →
  pure_wp (eval η (ESeq e1 e2)) φ ψ.
Proof.
  eauto using pure_wp_bind.
Qed.

Lemma pure_wp_as_bool m φ ψ :
  pure_wp_encode m φ ψ →
  pure_wp (as_bool m) φ ψ.
Proof.
  intro H.
  eapply pure_wp_bind. apply H.
  intros [] ([] & E & Hb); discriminate || rewrite E; by constructor.
Qed.

Lemma pure_wp_ifthenelse_bool η e e1 e2 φ φb ψ :
  pure_wp_encode (eval η e) φb ψ →
  (φb true  → pure_wp (eval η e1) φ ψ) →
  (φb false → pure_wp (eval η e2) φ ψ) →
  pure_wp (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  simpl.
  intros Hb Ht Hf.
  eapply pure_wp_bind. apply pure_wp_as_bool. apply Hb.
  intros []; auto.
Qed.


(* TODO later, move the following to [program_logic] *)

(** [pure_wp] implies [ewp] *)

From iris.proofmode Require Import proofmode.
From osiris.program_logic Require Import ewp tactics.
Import ewp_rules_tactics.

Lemma pure_wp_ewp `{!osirisGS Σ} {A E} E' Ψ (φ : A → Prop) (ψ : E → Prop) m :
  pure_wp m φ ψ →
  ⊢ EWP m @ E' <| Ψ |> {{ | RET a => ⌜φ a⌝; | EXN e => ⌜ψ e⌝ }}.
Proof.
  iIntros (Hm).
  iLöb as "IH" forall (m Hm).
  iApply ewp_unfold; rewrite /ewp_pre /=.

  destruct (is_handleable m) as [ h | ] eqn:R.
  - (* [m] is handleable *)
    destruct h as [ a | e | eff f ].
    + (* [ret]'s satisfy [φ] *)
      destruct m as [| | | |???[]| |]; discriminate || injection R as ->.
      by eapply invert_pure_wp_ret in Hm.
    + (* [throw]'s satisfy [ψ] *)
      destruct m as [| | | |???[]| |]; discriminate || injection R as ->.
      by eapply invert_pure_wp_throw in Hm.
    + (* [perform]'s are not immediately pure *)
      destruct m as [| | | |???[]| |]; discriminate || injection R as -> ->.
      by apply invert_pure_wp_stop in Hm.

  - (* [m] is not handleable *)
    intro_state.
    ewp_mask_intro "Hmod".
    iSplit.
    + (* so [m] can step because it is [pure_wp] *)
      destruct (pure_wp_progress m Hm) as [(a, ->)|[(e, ->)|]]; auto; discriminate.
    + (* and no step can change [σ] or escape [pure_wp] *)
      intro_step.
      ewp_cleanup_mod. ewp_mask_elim.
      destruct (pure_wp_preservation Hm Hstep) as (Hm' & <-).
      iFrame.
      by iApply "IH".
Qed.
