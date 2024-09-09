From Coq Require Import FunctionalExtensionality.
From stdpp Require Import relations.
From osiris Require Import base lang syntax.
From osiris.semantics Require Import code eval step simplification.

(** [may] relation: reduction steps for pure computations *)

(* The [may] relation represents reduction steps to reason about pure
computations. It is similar to [step] reductions that do not mention the store,
and reduces impure computations to [crash].

The resulting WP, called [pure] is a pure reasoning mode simpler than full
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

- [may] is not reflexive, otherwise the main construct of the [pure]
  predicate would have its conclusion as a premise. For the same reason, one
  should not directly include [simp] in [may] (maybe [simplify (S _)] could be
  fine).

- transitivity is not included, which makes the relation simpler to reason
  about. Transitivity is necessary for [simp] to be able to ignore intermediate
  steps in case of temporary nondeterminism, for example in the different
  components of a [Choose].

- if [m] is impure it can reach [crash] in some number of [may] steps, and so
  [pure] computations are guaranteed to be pure. *)

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
definition of [pure], but we choose here to make impurities reduce to
[crash].

However statements of progress and preservations are shown for computations
that are [pure] *)


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



