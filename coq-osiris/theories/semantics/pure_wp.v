From Coq Require Import FunctionalExtensionality.
From stdpp Require Import relations.
From osiris Require Import base lang syntax.
From osiris.semantics Require Import code eval step simplification.

(** [may] relation : reduction steps for pure computations *)

(* The [may] relation represents reduction steps to reason about pure
computations. It is similar to [step] reductions that do not mention the store,
and reduces impure computations to [crash].

The resulting WP, called [pure_wp] is a pure reasoning mode simpler than full
separation logic. In this way it is similar to the [total] predicate based on
the [simp] relation, but as opposed to [simp], [may] is small-step and allows
non-deterministic choices. The price to pay when reasoning about computations is
the quantification over all possible [may] paths, rather than simply the
existence of a [simp] simplification. This nondeterminism is the reason this
relation was originally called [may]. It would be reasonable to call it
[pure_step], though the correspondence between [may m m'] and [∀ σ, step (σ, m)
(σ, m')] is not perfect.

Compared to the [simp] relation, [may] is able to bypass some steps, for example
[Par m1 (throw e) k] reduces to [k (Throw e)], which is one example of
non-determinism, since [m1] could throw a different exception.

Other differences with [simp]:

- [may] is not reflexive, otherwise the main construct of the [pure_wp]
  predicate would have its conclusion as a premise. For the same reason, one
  should not directly include [simp] in [may] (maybe [simplify (S _)] could be
  fine).

- transitivity is not included, which makes the relation simpler to reason
  about. Transitivity is necessary for [simp] to be able to ignore intermediate
  steps in case of temporary nondeterminism, for example in the different
  components of a [Choose].

- if [m] is impure it can reach [crash] in some number of [may] steps, and so
  [pure_wp] computations are guaranteed to be pure. *)

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
    (discontinue k e1)
| MayParThrowRight {A1 A2 E'} m1 e2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par m1 (Throw e2) k)
    (discontinue k e2)
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
[crash].

However statements of progress and preservations are shown for computations
that are [pure_wp] *)


(** Computations are either final or may reduce *)

Lemma may_cases {A E} (m : micro A E) :
  m = crash ∨ (∃ a, m = ret a) ∨ (∃ e, m = throw e) ∨ (∃ m', may m m').
Proof.
  induction m; eauto with may;
    firstorder; subst; eauto 10 with may.
  destruct c; eauto with may.
  - destruct x; eauto with may.
  - destruct x as [[[[]]]]; eauto with may.
Qed.

(* using [final] from [simplification] *)
Lemma final_or_may {A E} (m : micro A E) : final m ∨ ∃ m', may m m'.
Proof.
  destruct (may_cases m); unfold final; firstorder (subst; eauto).
Qed.

Lemma final_not_may {A E} (m m' : micro A E) : final m → may m m' → False.
Proof.
  destruct m; try tauto; inversion 2.
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

Ltac inv H := inversion H; subst; eq_dep_inj; subst.

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

Lemma invert_may_throw A E e (m : micro A E) : may (throw e) m → False.
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

Lemma invert_may_perform {A E} (m' : micro A E) e h:
  may (Stop CPerform e h) m' → m' = crash.
Proof.
  by inversion 1.
Qed.

Lemma invert_may_par {A1 A2 E A E'} (k : outcome2 (A1 * A2) E → micro A E') m1 m2 m' :
  may (Par m1 m2 k) m' →
  (∃ a1 a2, m1 = ret a1 ∧ m2 = ret a2 ∧ m' = continue k (a1, a2)) ∨
  (∃ m1', may m1 m1' ∧ m' = Par m1' m2 k) ∨
  (∃ m2', may m2 m2' ∧ m' = Par m1 m2' k) ∨
  (∃ e1, m1 = throw e1 ∧ m' = discontinue k e1) ∨
  (∃ e2, m2 = throw e2 ∧ m' = discontinue k e2) ∨
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
  (∃ a, m = ret a ∧ may (continue f a) m1) ∨
  (∃ e, m = throw e ∧ may (discontinue f e) m1).
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


(** [pure_wp] is monotonic *)

Lemma pure_wp_consequence {A E} {φ φ' ψ ψ' : _ → Prop} (m : micro A E) :
  pure_wp m φ ψ → (∀ a, φ a → φ' a) → (∀ e, ψ e → ψ' e) → pure_wp m φ' ψ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma pure_wp_consequence_ret {A E} {φ φ' ψ : _ → Prop} (m : micro A E) :
  pure_wp m φ ψ → (∀ a, φ a → φ' a) → pure_wp m φ' ψ.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma pure_wp_consequence_throw {A E} {φ ψ ψ' : _ → Prop} (m : micro A E) :
  pure_wp m φ ψ → (∀ e, ψ e → ψ' e) → pure_wp m φ ψ'.
Proof.
  induction 1; constructor; auto.
Qed.


(* Postconditions can be strengthened since final states must be reachable *)

Lemma pure_wp_strengthen_reachable {A E} {φ ψ : _ → Prop} (m : micro A E) :
  pure_wp m φ ψ →
  pure_wp m
    (λ a, rtc may m (ret a) ∧ φ a)
    (λ e, rtc may m (throw e) ∧ ψ e).
Proof.
  induction 1 as [ |  | ? ? ? Hex Hfo IH]; constructor; auto with relations.
  intros m' M. clear Hex.
  apply (pure_wp_consequence _ (IH m' M)); firstorder; econstructor; eauto.
Qed.

(* A consequence rule that requires inclusion only on reachable final states *)

Lemma pure_wp_consequence_reachable {A E} {φ φ' ψ ψ' : _ → Prop} (m : micro A E) :
  pure_wp m φ ψ →
  (∀ a, rtc may m (ret a) → φ a → φ' a) →
  (∀ e, rtc may m (throw e) → ψ e → ψ' e) →
  pure_wp m φ' ψ'.
Proof.
  intros P%pure_wp_strengthen_reachable Hv He.
  apply (pure_wp_consequence _ P); firstorder.
Qed.


(** [pure_wp] is preserved by forward [may] steps *)

Lemma pure_wp_may_forward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
  pure_wp m φ ψ → may m m' → pure_wp m' φ ψ.
Proof.
  induction 1; auto; inversion 1.
Qed.

Lemma pure_wp_rtc_may_forward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
  pure_wp m φ ψ → rtc may m m' → pure_wp m' φ ψ.
Proof.
  induction 2; eauto using pure_wp_may_forward.
Qed.


(** [pure_wp] is preserved by deterministic backward [may] steps *)

Definition deterministically {X} (R : relation X) : relation X :=
  λ x y, R x y ∧ ∀ z, R x z → z = y.

Lemma pure_wp_det_may_backward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
  deterministically may m m' → pure_wp m' φ ψ → pure_wp m φ ψ.
Proof.
  intros (M, MF) P. constructor. eauto. firstorder congruence.
Qed.


(** Inversion lemmas on [pure_wp] *)

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

(* The _compat format is slightly easier to prove and is easier to use in cases
  where a result is in hypothesis *)
Lemma pure_wp_try2_compat {A' A E E' φ ψ φ' ψ'} m (f : outcome2 A E → micro A' E') :
  pure_wp m φ ψ →
  (∀ a, φ a → pure_wp (continue f a) φ' ψ') →
  (∀ e, ψ e → pure_wp (discontinue f e) φ' ψ') →
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

Lemma pure_wp_try2 {A' A E E' φ ψ} m (f : outcome2 A E → micro A' E') :
  pure_wp m (λ a, pure_wp (continue f a) φ ψ) (λ e, pure_wp (discontinue f e) φ ψ) →
  pure_wp (try2 m f) φ ψ.
Proof.
  intros P. eapply pure_wp_try2_compat; eauto.
Qed.

Lemma pure_wp_bind {A' A E φ ψ} m (k : A → micro A' E) :
  pure_wp m (λ a, pure_wp (k a) φ ψ) ψ →
  pure_wp (bind m k) φ ψ.
Proof.
  rewrite bind_as_try2. intros. eapply pure_wp_try2; eauto.
  eapply pure_wp_consequence; eauto.
  intros e. rewrite discontinue_glue2. by constructor.
Qed.

Lemma pure_wp_try {A' A E E' φ ψ} m (f : A → micro A' E) (h : E' → micro A' E) :
  pure_wp m (λ a, pure_wp (f a) φ ψ) (λ e, pure_wp (h e) φ ψ) →
  pure_wp (try m f h) φ ψ.
Proof.
  eauto using pure_wp_try2.
Qed.

Lemma pure_wp_bind_compat {A' A E} (φ : A → Prop) (ψ : E → Prop) (φ' : A' → Prop) m k :
  pure_wp m φ ψ →
  (∀ a, φ a → pure_wp (k a) φ' ψ) →
  pure_wp (bind m k) φ' ψ.
Proof.
  intros. eapply pure_wp_bind, pure_wp_consequence_ret; eauto.
Qed.


(** Characterization of [pure_wp] : a computation [m] satisfies some [pure_wp]
if and only if [m] cannot do infinite [may] steps ([m] satisfies [sn may]) and
all final computations reachable from [m] also satisfy the same [pure_wp] *)

Lemma pure_wp_sn {A E} {φ : A → Prop} {ψ : E → Prop} m :
  pure_wp m φ ψ → sn may m.
Proof.
  induction 1; constructor; try solve [intros y M; inversion M].
  firstorder.
Qed.

Lemma pure_wp_long_steps {A E} {φ : A → Prop} {ψ : E → Prop} m :
  pure_wp m φ ψ ↔ sn may m ∧ ∀ f, rtc may m f → final f → pure_wp f φ ψ.
Proof.
  split.
  - intros W; split. by eapply pure_wp_sn.
    intros f S F.
    induction S. auto. apply IHS; auto.
    eauto using pure_wp_may_forward.
  - intros (SN, HF).
    revert HF; induction SN as [m SN IH]; intros HF.
    pose proof (may_cases m) as C.
    rewrite <-!Logic.or_assoc in C.
    destruct C as [C|(m', M)].
    + apply HF. constructor. firstorder subst; done.
    + constructor. eauto. clear m' M.
      intros m' M. apply IH; auto.
      intros f m'f F. apply HF; auto; econstructor; eauto.
Qed.

(* [pure_wp_exists_path] implies e.g. [pure_wp m (λ _, P) (λ _, P) → P] *)

Lemma pure_wp_exists_path {A E} {φ : A → Prop} {ψ : E → Prop} m :
  pure_wp m φ ψ → ∃ f, rtc may m f ∧ final f ∧ pure_wp f φ ψ.
Proof.
  intros W. induction W as [ | | ? ? m (m', M) Hf IH].
  - by repeat econstructor.
  - by repeat econstructor.
  - destruct (IH m' M) as (f & ? & ? & ?).
    assert (rtc may m f) by by econstructor.
    firstorder.
Qed.

Lemma pure_wp_exists_ret_or_throw {A E} {φ : A → Prop} {ψ : E → Prop} m :
  pure_wp m φ ψ →
  (∃ a, rtc may m (ret a) ∧ φ a) ∨
  (∃ e, rtc may m (throw e) ∧ ψ e).
Proof.
  intros ([] & mf & [] & W)%pure_wp_exists_path.
  - apply invert_pure_wp_ret in W; eauto.
  - apply invert_pure_wp_throw in W; eauto.
  - apply invert_pure_wp_crash in W; tauto.
Qed.

Lemma pure_wp_sequentialize {A1 E1 A2 E2} (m1 : micro A1 E1) (m2 : micro A2 E2) φ1 φ2 :
  pure_wp m1 (λ a1, pure_wp m2 (λ a2, φ1 a1 ∧ φ2 a2) (λ _, False)) (λ _, False) →
  pure_wp m1 φ1 (λ _, False) ∧ pure_wp m2 φ2 (λ _, False).
Proof.
  intros Hm1. split.
  - apply (pure_wp_consequence_ret _ Hm1).
    intros a1 []%pure_wp_exists_ret_or_throw; firstorder.
  - destruct (pure_wp_exists_ret_or_throw _ Hm1) as [(a1 & M & Hm2)| ]; firstorder.
    eapply (pure_wp_consequence_ret _ Hm2). firstorder.
Qed.


(** [Par] preserves [pure_wp] *)

(* From two [pure_wp]s on [m1] and [m2] we know [sn may m1] and [sn may m2],
which can be combined to a [sn (either may may) (m1, m2)] on which we can
perform an induction, to simulate the different steps that a [Par m1 m2 k]
computation takes, in order to establish [pure_wp] on [Par m1 m2 k] *)

Inductive either {A B} (R : A → A → Prop) (S : B → B → Prop) : A * B → A * B → Prop :=
  | either_left a a' b : R a a' → either R S (a, b) (a', b)
  | either_right a b b' : S b b' → either R S (a, b) (a, b').

Lemma either_Acc {A B} (R : A → A → Prop) (S : B → B → Prop) a b :
  Acc R a → Acc S b → Acc (either R S) (a, b).
Proof.
  intros Aa; revert b. induction Aa as [a Aa IHa].
  intros b Ab. induction Ab as [b Ab IHb].
  constructor.
  intros (a', b') H.
  inversion H; subst.
  eapply IHa; auto. constructor; eauto.
  eapply IHb; auto.
Qed.

(* [pure_wp] preserved by [Par] : linking postconditions with implications *)

Lemma pure_wp_par_compat {A E A1 A2 E'} m1 m2 φ1 φ2 ψ1 ψ2 φ ψ
  (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp m1 φ1 ψ1 →
  pure_wp m2 φ2 ψ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → pure_wp (continue k (a1, a2)) φ ψ) →
  (∀ e, ψ1 e ∨ ψ2 e → pure_wp (discontinue k e) φ ψ) →
  pure_wp (Par m1 m2 k) φ ψ.
Proof.
  intros H1 H2 Hret Hthr.
  pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
  remember (m1, m2) as p.
  revert m1 m2 Heqp H1 H2.
  induction SN as [(m1, m2) SN IH].
  intros ? ? [=<-<-] H1 H2.
  constructor.
  - (* progress *)
    inversion H1; subst.
    + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
    + (* throw *) eauto with may.
    + firstorder. eexists. by eapply MayParLeft.
  - (* preservation *)
    intros m' M.
    apply invert_may_par in M.
    repeat (destruct M as [M | M]).
    + destruct M as (? & ? & -> & -> & ->). apply Hret; eapply invert_pure_wp_ret; eauto.
    + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto. constructor; apply M1. eauto using pure_wp_may_forward.
    + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto. constructor; apply M2. eauto using pure_wp_may_forward.
    + destruct M as (e1 & -> & ->). apply Hthr. left. eapply invert_pure_wp_throw; eauto.
    + destruct M as (e2 & -> & ->). apply Hthr. right. eapply invert_pure_wp_throw; eauto.
    + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
Qed.

(* [pure_wp] preserved by [Par], stated by giving [m1] a [pure_wp m2]
postcondition and [m2] a [pure_wp m1] postcondition. In other words, in a pure
setting, proving correct a parallel computation of [m1] and [m2] is the same as
proving correct both sequentializations [m1; m2] and [m2; m1]. Both are needed
since exceptions introduce nondeterminism. For example with [m1 = Throw e] and
[m2 = Crash] we have [pure_wp m1 (λ _, False) (λ _, True)]. *)

Lemma pure_wp_par {A E A1 A2 E'} m1 m2 φ ψ
  (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp m1
    (λ a1,
      pure_wp m2
        (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
        (λ e, pure_wp (discontinue k e) φ ψ))
    (λ e, pure_wp (discontinue k e) φ ψ) →
  pure_wp m2
    (λ a2,
      pure_wp m1
        (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
        (λ e, pure_wp (discontinue k e) φ ψ))
    (λ e, pure_wp (discontinue k e) φ ψ) →
  pure_wp (Par m1 m2 k) φ ψ.
Proof.
  intros H1 H2.
  pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
  remember (m1, m2) as p.
  revert m1 m2 Heqp H1 H2.
  induction SN as [(m1, m2) SN IH].
  intros ? ? [=<-<-] H1 H2.
  constructor.
  - (* progress *)
    inversion H1; subst.
    + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
    + (* throw *) eauto with may.
    + firstorder. eexists. by eapply MayParLeft.
  - (* preservation *)
    intros m' M.
    apply invert_may_par in M.
    repeat (destruct M as [M | M]).
    + destruct M as (? & ? & -> & -> & ->). do 2 apply invert_pure_wp_ret in H1, H2; auto.
    + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto.
      * constructor; apply M1.
      * eauto using pure_wp_may_forward.
      * eapply pure_wp_consequence_ret; eauto.
        intros; eapply pure_wp_may_forward; eauto; eauto.
    + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto.
      * constructor; apply M2.
      * eapply pure_wp_consequence_ret; eauto.
        intros; eapply pure_wp_may_forward; eauto; eauto.
      * eauto using pure_wp_may_forward.
    + destruct M as (e1 & -> & ->). apply invert_pure_wp_throw in H1; eauto.
    + destruct M as (e2 & -> & ->). apply invert_pure_wp_throw in H2; eauto.
    + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
Qed.

(** Sequentializations of [Par] for restricted forms of [pure_wp] *)

(* If [m1] cannot raise exceptions, then it is enough to prove that [m1]
satisfies [pure_wp] with the corresponding [pure_wp m2] in postcondition *)

Lemma pure_wp_par_val_left {A E A1 A2 E'} m1 m2 φ ψ
  (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp m1
    (λ a1,
      pure_wp m2
        (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
        (λ e, pure_wp (discontinue k e) φ ψ))
    (λ _, False) →
  pure_wp (Par m1 m2 k) φ ψ.
Proof.
  intros H1.
  (* in order to run an induction on SN (either may may m1 m2) we establish
   [pure_wp m2] with a trivial postcondition for returns *)
  assert (H2 : pure_wp m2 (λ _, True) (λ e, pure_wp (discontinue k e) φ ψ)). {
    apply pure_wp_exists_ret_or_throw in H1.
    destruct H1 as [(a & _ & P) | (e & _ & [])].
    eapply pure_wp_consequence; eauto.
  }
  pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
  remember (m1, m2) as p.
  revert m1 m2 Heqp H1 H2.
  induction SN as [(m1, m2) SN IH].
  intros ? ? [=<-<-] H1 H2.
  constructor.
  - (* progress *)
    inversion H1; subst.
    + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
    + (* throw *) eauto with may.
    + firstorder. eexists. by eapply MayParLeft.
  - (* preservation *)
    intros m' M.
    apply invert_may_par in M.
    repeat (destruct M as [M | M]).
    + destruct M as (? & ? & -> & -> & ->). do 2 apply invert_pure_wp_ret in H1; auto.
    + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto.
      * constructor; apply M1.
      * eauto using pure_wp_may_forward.
    + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto.
      * constructor; apply M2.
      * eapply pure_wp_consequence_ret; eauto.
        intros; eapply pure_wp_may_forward; eauto; eauto.
      * eauto using pure_wp_may_forward.
    + destruct M as (e1 & -> & ->). apply invert_pure_wp_throw in H1; tauto.
    + destruct M as (e2 & -> & ->). eapply invert_pure_wp_throw in H2; eauto.
    + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
Qed.

(* Slightly simpler case when none of the parties involved ([m1], [m2], [k]) can
   throw exceptions *)

Lemma pure_wp_par_vals_left {A E A1 A2 E'} m1 m2 φ
  (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp m1
    (λ a1,
      pure_wp m2
        (λ a2, pure_wp (continue k (a1, a2)) φ (λ _, False))
        (λ _, False))
    (λ _, False) →
  pure_wp (Par m1 m2 k) φ (λ _, False).
Proof.
  intros H1.
  apply pure_wp_par_val_left.
  eapply pure_wp_consequence; eauto. simpl. intros.
  eapply pure_wp_consequence; firstorder eauto.
Qed.


(** [pure_wp] is preserved by [Handle] and [Choose] *)

Lemma pure_wp_handle {A E} m φ ψ (h : _ → micro A E) :
  pure_wp m
    (λ a, pure_wp (h (O3Ret a)) φ ψ)
    (λ e, pure_wp (h (O3Throw e)) φ ψ) →
  pure_wp (Handle m h) φ ψ.
Proof.
  intros Hm. dependent induction Hm; constructor; eauto with may.
  - intros m' M. inv M; auto. edestruct invert_may_ret; eauto.
  - intros m' M. inv M; auto. edestruct invert_may_throw; eauto.
  - firstorder eauto with may.
  - intros m' M. inv M.
    + firstorder; edestruct invert_may_ret; eauto.
    + firstorder; edestruct invert_may_throw; eauto.
    + firstorder. by edestruct (@invert_may_crash val val).
    + firstorder.
Qed.

Lemma pure_wp_Choose {A B E E' φ ψ} m1 m2 (k : outcome2 B E' → micro A E) :
  pure_wp (try2 m1 k) φ ψ →
  pure_wp (try2 m2 k) φ ψ →
  pure_wp (Choose m1 m2 k) φ ψ.
Proof.
  intros H1 H2. constructor. eauto with may.
  intros m' M. by inv M.
Qed.

Lemma pure_wp_choose {A E φ ψ} (m1 m2 : micro A E) :
  pure_wp m1 φ ψ →
  pure_wp m2 φ ψ →
  pure_wp (choose m1 m2) φ ψ.
Proof.
  intros H1 H2.
  apply pure_wp_Choose; eapply pure_wp_try2; eapply pure_wp_consequence; eauto.
  all: by constructor.
Qed.


(** More inversion lemmas on [pure_wp] : bind, [Par]s, [Handle] *)

Lemma invert_pure_wp_try2 {A1 E1 B E' φ ψ} (m : micro A1 E1) (k : _ → micro B E') :
  pure_wp (try2 m k) φ ψ →
  pure_wp m
    (λ a, pure_wp (continue k a) φ ψ)
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (try2 m k) as mt; intros PS; revert m Heqmt.
  induction PS as [ |  | φ ψ m Hex HF IH]; intros m1 Hm1.
  (* if [try2 m1 k] is [ret] or [throw] then [m1] must be too *)
  - destruct m1; try discriminate.
    all: constructor; simpl in Hm1; rewrite <-Hm1; by constructor.
  - destruct m1; try discriminate.
    all: constructor; simpl in Hm1; rewrite <-Hm1; by constructor.
  - (* otherwise [m] reduces to some [m'], and all such [m'] are safe  *)
    subst m.
    (* from the fact that [try2 m1 k] reduce to [m']: *)
    destruct Hex as (m', [(m1' & Hm1 & ->) | ?]%invert_may_try2).
    + (* either [m1] reduces to [m1'] and [m' = try2 m1' k], conclude by IH *)
      constructor; eauto. intros m2 Hm2.
      eapply IH; eauto. by apply may_try2.
    + (* or [m1] is [ret] or [throw] and so is safe *)
      by hnf; firstorder (subst; eauto with pure_wp).
Qed.

Lemma invert_pure_wp_bind {A1 E B φ ψ} (m : micro A1 E) (k : _ → micro B E) :
  pure_wp (bind m k) φ ψ →
  pure_wp m (λ a, pure_wp (k a) φ ψ) ψ.
Proof.
  rewrite bind_as_try2.
  intros H%invert_pure_wp_try2.
  eapply pure_wp_consequence; eauto.
  by intros ? ?%invert_pure_wp_throw.
Qed.

Lemma invert_pure_wp_par_ret_left {A E A1 A2 E' φ ψ} a1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp (Par (ret a1) m2 k) φ ψ →
  pure_wp m2
    (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (Par _ m2 k) as m; intros PS; revert a1 m2 Heqm.
  induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
  destruct (may_cases m2) as [-> | [ | [ | Hm2 ]]].
  - now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
  - firstorder. subst. constructor. apply HF. constructor.
  - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
  - constructor; eauto with may.
Qed.

Lemma invert_pure_wp_par_left {A E A1 A2 E' φ ψ} m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp (Par m1 m2 k) φ ψ →
  pure_wp m1
    (λ a1,
      pure_wp m2
        (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
        (λ e, pure_wp (discontinue k e) φ ψ))
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (Par m1 m2 k) as m; intros PS; revert m1 m2 Heqm.
  induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
  destruct (may_cases m1) as [-> | [ | [ | Hm1 ]]].
  - now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
  - assert (PP : pure_wp (Par m1 m2 k) φ ψ) by by constructor.
    firstorder. subst. constructor. by eapply invert_pure_wp_par_ret_left.
  - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
  - constructor; eauto with may.
Qed.

Lemma invert_pure_wp_par_ret_right {A E A1 A2 E' φ ψ} m1 a2 (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp (Par m1 (ret a2) k) φ ψ →
  pure_wp m1
    (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (Par _ _ k) as m; intros PS; revert m1 a2 Heqm.
  induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
  destruct (may_cases m1) as [-> | [ | [ | Hm1 ]]].
  - now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
  - firstorder. subst. constructor. apply HF. constructor.
  - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
  - constructor; eauto with may.
Qed.

Lemma invert_pure_wp_par_right {A E A1 A2 E' φ ψ} m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  pure_wp (Par m1 m2 k) φ ψ →
  pure_wp m2
    (λ a2,
      pure_wp m1
        (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
        (λ e, pure_wp (discontinue k e) φ ψ))
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (Par m1 m2 k) as m; intros PS; revert m1 m2 Heqm.
  induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
  destruct (may_cases m2) as [-> | [ | [ | Hm2 ]]].
  - now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
  - assert (PP : pure_wp (Par m1 m2 k) φ ψ) by by constructor.
    firstorder. subst. constructor. by eapply invert_pure_wp_par_ret_right.
  - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
  - constructor; eauto with may.
Qed.

Lemma invert_pure_wp_handle {A E φ ψ} m (k : _ → micro A E) :
  pure_wp (Handle m k) φ ψ →
  pure_wp m
    (λ a, pure_wp (continue k a) φ ψ)
    (λ e, pure_wp (discontinue k e) φ ψ).
Proof.
  remember (Handle m k) as h; intros PS; revert m Heqh.
  induction PS as [ |  | φ ψ _m Hex HF IH]; try discriminate; intros m ->.
  destruct (may_cases m) as [-> | [ | [ | Hm ]]].
  - now destruct (invert_pure_wp_crash _ _ (HF crash ltac:(constructor))).
  - firstorder. subst. constructor. eauto with may.
  - destruct H as (e, ->). constructor. eauto with may.
  - constructor; eauto with may.
Qed.


(** Steps from pure computations necessarily are [may] and preserve the store *)

Lemma pure_wp_step_may {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
  pure_wp m φ ψ → step (σ, m) (σ', m') → may m m' ∧ σ' = σ.
Proof.
  revert σ σ' m' φ ψ; induction m; intros σ σ' m' φ ψ Hm Hstep.
  - inv Hstep.
  - inv Hstep.
  - inv Hstep.
  - apply invert_pure_wp_handle in Hm.
    inv Hstep; eauto with may.
    + by apply invert_pure_wp_stop in Hm.
    + edestruct IHm; eauto with may.
  - pose proof invert_pure_wp_stop _ _ _ _ _ Hm.
    destruct c; try tauto; inv Hstep; split; auto; constructor.
  - pose proof invert_pure_wp_par_left _ _ _ Hm as Hm1.
    pose proof invert_pure_wp_par_right _ _ _ Hm as Hm2.
    inv Hstep; try (split; [ | tauto ]).
    all: try by constructor.
    + by apply invert_pure_wp_stop in Hm1.
    + by apply invert_pure_wp_stop in Hm2.
    + edestruct IHm1; eauto with may.
    + edestruct IHm2; eauto with may.
  - inv Hstep; repeat constructor.
Qed.


(* One proof of the preservation of [pure_wp] under [step]s. It may be removed
since it is a consequence of [pure_wp_step_may] and [pure_wp_may_forward],
however it is a demonstration that we can split a [pure_wp] on a [Par] into two
with [invert_pure_wp_par_*] and recombine them with
[pure_wp_par_sequentialization] after a step on either side. This technique is
also useful for [pure_wp_simp]. *)

Lemma pure_wp_preservation_duplicate {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
  pure_wp m φ ψ → step (σ, m) (σ', m') → pure_wp m' φ ψ ∧ σ' = σ.
Proof.
  revert σ σ' m' φ ψ; induction m; intros σ σ' m' φ ψ Hm Hstep.
  - inv Hstep.
  - inv Hstep.
  - inv Hstep.
  - apply invert_pure_wp_handle in Hm.
    inv Hstep.
    + by apply invert_pure_wp_ret in Hm.
    + by apply invert_pure_wp_throw in Hm.
    + by apply invert_pure_wp_stop in Hm.
    + by apply invert_pure_wp_crash in Hm.
    + edestruct IHm as [IH ->]; eauto. split; auto.
      eapply pure_wp_handle; eauto.
  - pose proof invert_pure_wp_stop _ _ _ _ _ Hm.
    destruct c; try tauto; inv Hstep; split; auto;
      eapply pure_wp_may_forward; eauto; constructor.
  - pose proof invert_pure_wp_par_left _ _ _ Hm as Hm1.
    pose proof invert_pure_wp_par_right _ _ _ Hm as Hm2.
    inv Hstep; try (split; [ | tauto ]).
    all: eauto using pure_wp_may_forward with may.
    + by apply invert_pure_wp_stop in Hm1.
    + by apply invert_pure_wp_stop in Hm2.
    + edestruct IHm1 as [IHm1' ->]; eauto. split; auto.
      eapply pure_wp_par. apply IHm1'.
      eapply pure_wp_consequence_ret; eauto. simpl.
      intros a2 Hm1'.
      eapply (IHm1 _ _ _ _ _ Hm1'); eauto.
    + edestruct IHm2 as [IHm2' ->]; eauto. split; auto.
      eapply pure_wp_par. 2: apply IHm2'.
      eapply pure_wp_consequence_ret; eauto. simpl.
      intros a1 Hm2'.
      eapply (IHm2 _ _ _ _ _ Hm2'); eauto.
  - inv Hstep; split; auto; eapply pure_wp_may_forward; eauto with may.
Qed.


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
  destruct (pure_wp_step_may Hm Hstep).
  eauto using pure_wp_may_forward.
Qed.


(** [pure_wp] is preserved by [simp] *)

Lemma pure_wp_simp {A E φ ψ} (m m' : micro A E) :
  simp m m' → pure_wp m' φ ψ → pure_wp m φ ψ.
Proof.
  intros S. revert φ ψ. induction S; eauto; intros φ ψ.
  (* SimpEval and SimpLoop are deterministic may steps *)
  - apply pure_wp_det_may_backward. repeat constructor. by intros z M%invert_may_eval.
  - apply pure_wp_det_may_backward. repeat constructor. by intros z M%invert_may_loop.
  (* Most cases are now simple uses of inversion and compatibility lemmas *)
  - intros P. constructor. eauto with may.
    intros m' [-> | ->]%invert_may_choose; eauto using invert_pure_wp_try2, pure_wp_try2.
  - intros P%invert_pure_wp_try2.
    apply pure_wp_par.
    + by constructor.
    + eapply pure_wp_consequence_ret; eauto. by constructor.
  - intros P%invert_pure_wp_try2.
    apply pure_wp_par.
    + eapply pure_wp_consequence_ret; eauto. by constructor.
    + by constructor.
  - intros P.
    pose proof IHS1 _ _ (invert_pure_wp_par_left _ _ _ P).
    pose proof IHS2 _ _ (invert_pure_wp_par_right _ _ _ P).
    apply pure_wp_par; eapply pure_wp_consequence_ret; eauto; firstorder eauto.
  - (* SimpParThrowAgree *)
    intros P. apply pure_wp_par; eauto with pure_wp.
  - (* Stop CPerform is impure *)
    intros []%invert_pure_wp_stop.
  - intros P. apply pure_wp_handle, IHS. by constructor.
  - intros P. apply pure_wp_handle, IHS. by constructor.
Qed.

(* The reverse, less useful, direction also holds *)
Lemma pure_wp_complexify {A E} (m m' : micro A E) :
  simp m m' → ∀ φ ψ, pure_wp m φ ψ → pure_wp m' φ ψ.
Proof.
  intros S. induction S; eauto; intros φ ψ.
  (* SimpEval and SimpLoop are forward may steps *)
  - intro; eapply pure_wp_may_forward; eauto. constructor.
  - intro; eapply pure_wp_may_forward; eauto. constructor.
  - intros P.
    eapply pure_wp_may_forward in P; [ | constructor ].
    apply pure_wp_try2, IHS1, invert_pure_wp_try2, P.
  - intros P%invert_pure_wp_par_ret_left. by apply pure_wp_try2.
  - intros P%invert_pure_wp_par_ret_right. by apply pure_wp_try2.
  - intros P.
    pose proof IHS1 _ _ (invert_pure_wp_par_left _ _ _ P).
    pose proof IHS2 _ _ (invert_pure_wp_par_right _ _ _ P).
    apply pure_wp_par; eapply pure_wp_consequence_ret; eauto; firstorder eauto.
  - (* SimpParThrowAgree uses only one hyp *)
    by intros P%invert_pure_wp_par_left%IHS1%invert_pure_wp_throw.
  - intros []%invert_pure_wp_stop.
  - by intros P%invert_pure_wp_handle%IHS%invert_pure_wp_ret.
  - by intros P%invert_pure_wp_handle%IHS%invert_pure_wp_throw.
Qed.


(** Intersection rule *)

Lemma pure_wp_intersection {A E} `{Inhabited X} {φ ψ} (m : micro A E) :
  (∀ x : X, pure_wp m (φ x) ψ) →
  pure_wp m (λ a, ∀ x, φ x a) ψ.
Proof.
  intros Hm.
  induction (Hm inhabitant); constructor; eauto using pure_wp_may_forward.
  intros x. apply (invert_pure_wp_ret _ _ _ (Hm x)).
Qed.

Lemma pure_wp_binary_intersection {A E φ1 φ2 ψ} (m : micro A E) :
  pure_wp m φ1 ψ →
  pure_wp m φ2 ψ →
  pure_wp m (λ a, φ1 a ∧ φ2 a) ψ.
Proof.
  intros.
  set (post := λ (b : bool), λ a, if b then φ1 a else φ2 a).
  eapply @pure_wp_consequence with (φ := λ a, ∀ b, post b a) (ψ := ψ).
  { eapply pure_wp_intersection.
    intros b. destruct b; unfold post; assumption. }
  { intros a Hpost. split.
    + apply (Hpost true).
    + apply (Hpost false). }
  { tauto. }
Qed.


(** Compatibility with [widen] *)

Lemma pure_wp_widen {A E} (m : micro A void) φ ψ ψ' :
  pure_wp (E := E) (widen m) φ ψ ↔ pure_wp m φ ψ'.
Proof.
  unfold widen; split.
  - intros P%invert_pure_wp_try2. eapply (pure_wp_consequence _ P); try intros [].
    by intros a ?%invert_pure_wp_ret.
  - intros P. apply pure_wp_try2, (pure_wp_consequence _ P); try intros [].
    by constructor.
Qed.

Lemma pure_wp_evals η es φs ψ :
  Forall2 (λ e φ, pure_wp (eval η e) φ ψ) es φs →
  pure_wp (evals η es) (Forall2 id φs) ψ.
Proof.
  revert φs.
  induction es as [ | e es IHes]; intros φs' Hes.
  - constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (φ & φs & He & Hes & ->).
    eapply pure_wp_par_compat.
    + apply He.
    + apply IHes, Hes.
    + intros v vs Hv Hvs. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.


(** Hoare reasoning rules, no encode *)

Lemma pure_wp_val {A E} (a : A) (ψ : E → Prop) : pure_wp (ret a) (λ b, b = a) ψ.
Proof.
  by constructor.
Qed.

Lemma pure_wp_ifthenelse η e e1 e2 φ ψ :
  pure_wp (eval η e) (λ v, ∃ b : bool, v = #b ∧ pure_wp (eval η (if b then e1 else e2)) φ ψ) ψ →
  pure_wp (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  simpl.
  intros He.
  eapply pure_wp_bind, pure_wp_bind, (pure_wp_consequence _ He); auto.
  intros _v ([] & -> & H); apply pure_wp_ret, H.
Qed.

Lemma pure_wp_assert η e ψ :
  pure_wp (eval η e) (λ v, v = #true) ψ →
  pure_wp (eval η (EAssert e)) (λ v, v = #()) ψ.
Proof.
  intros He. simpl.
  apply pure_wp_choose. by apply pure_wp_ret.
  apply pure_wp_bind, pure_wp_bind.
  apply (pure_wp_consequence _ He); auto.
  intros _ ->.
  repeat econstructor.
Qed.

Lemma pure_wp_seq φ ψ η e1 e2 :
  pure_wp (eval η e1) (λ _, pure_wp (eval η e2) φ ψ) ψ →
  pure_wp (eval η (ESeq e1 e2)) φ ψ.
Proof.
  eauto using pure_wp_bind.
Qed.

Lemma simp_check_div_by_zero z :
  representable z →
  (z ≠ 0)%Z →
  pure_wp (check_div_by_zero (repr z)) (λ v, v = ()) (λ _, False).
Proof.
  intros.
  unfold check_div_by_zero.
  change int.zero with (repr 0).
  rewrite eq_repr_repr by representable.
  case_eq (z =? 0)%Z; [ rewrite Z.eqb_eq | rewrite Z.eqb_neq ]; intro.
  { tauto. }
  { apply pure_wp_val. }
Qed.


(** Encode compatibility *)

Definition encode_pred `{Encode A} (φ : A → Prop) := λ v, ∃ a, v = #a ∧ φ a.

Definition pure_wp_encode `{Encode A} {E} (m : micro val E) (φ : A → Prop) (ψ : E → Prop) :=
  pure_wp m (encode_pred φ) ψ.

Notation "m 'returns' v" := (pure_wp m (λ a, a = v) (λ _, False)) (at level 10).


(** Hoare reasoning rules, with encode *)

Lemma pure_wp_as_bool m φ ψ :
  pure_wp_encode m φ ψ →
  pure_wp (as_bool m) φ ψ.
Proof.
  intro H.
  eapply pure_wp_bind_compat; eauto.
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
  eapply pure_wp_bind_compat. apply pure_wp_as_bool. apply Hb.
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
