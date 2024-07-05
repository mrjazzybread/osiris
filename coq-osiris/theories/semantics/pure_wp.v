From Coq Require Import FunctionalExtensionality.
From osiris Require Import base lang.
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
  components of a [Choose]. *)

Inductive may {A E} : micro A E → micro A E → Prop :=
| MayEval η e k:
  may
    (Stop CEval (η, e) k)
    (try2 (eval η e) k)
| MayLoop η x i1 i2 e k :
  may
    (Stop CLoop (η, x, i1, i2, e) k)
    (try2 (loop η x i1 i2 e) k)
| MayChooseLeft {B E'} m1 m2 (k : outcome2 B E' → _) :
  may
    (Choose m1 m2 k)
    (try2 m1 k)
| MayChooseRight {B E'} m1 m2 (k : outcome2 B E' → _) :
  may
    (Choose m1 m2 k)
    (try2 m2 k)
| MayParRetLeft {A1 A2 E'} a1 m2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par (Ret a1) m2 k)
    (try2 m2 (join1 a1 k))
| MayParRetRight {A1 A2 E'} m1 a2 (k : outcome2 (A1 * A2) E' → _) :
  may
    (Par m1 (Ret a2) k)
    (try2 m1 (join2 a2 k))
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
| MayHandleRet v k :
  may
    (Handle (Ret v) k)
    (continue k v)
| MayHandleThrow e k :
  may
    (Handle (Throw e) k)
    (discontinue k e)
(* TODO if needed, introduce a constructor corresponding to [SimpPerform].
   Expect a problem in the proof of [invert_may_bind]. Note that this may not be
   useful, since [may] is used only in pure settings. *)
| MayHandle m m' k :
  may m m' ->
  may
    (Handle m k)
    (Handle m' k).

Global Hint Constructors may : may.


(* The following statements, that one may expect, do not hold.

may m m' → ∀ σ, step (σ, m) (σ, m')

may m m' → ∀ σ, ∃ m'', step (σ, m) (σ, m'')

First, because MayParRetLeft/MayParRetRight take a shortcut as soon as [ret] is
present in a [Par], with with no corresponding [step] constructor. (To
circumvent this problem, a simulation statement might be established.)

Second, because [Par (Ret _) (Stop CStore _ _) _] can only [step] to a different
store when the initial store fits. For this, some additional conditional
property of purity would be required.

This purity condition is shown in [immediately_pure_step_may], which shows that
under it, [step]s do not change the store and are included in [may].

Under the same condition the second statement should hold, but it is not
necessary for the end results. *)


(** Compatibility with [bind] *)

Lemma may_eq {A E} (m m1 m2 : micro A E) : may m m1 → m1 = m2 → may m m2.
Proof.
  congruence.
Qed.

Lemma may_bind {A B E} (m m' : micro A E) (k : A → micro B E) :
  may m m' → may (bind m k) (bind m' k).
Proof.
  induction 1; eauto; try solve [ inversion 1 ]; simpl;
    try rewrite bind_try2; try constructor; auto.
  all: eapply may_eq; [ constructor | f_equal ].
  all: extensionality v; destruct v; auto.
Qed.

(** Inversion lemmas *)

(* Inversion lemmas are useful since because of dependent equality [inversion]
   is tedious to use by itself. We use the classical property [inj_pair2], which
   is a consequence of the axiom of the excluded middle. *)

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
  (∃ a, m1 = ret a ∧ m' = try2 m2 (join1 a k)) ∨
  (∃ a, m2 = ret a ∧ m' = try2 m1 (join2 a k)) ∨
  (∃ m1', may m1 m1' ∧ m' = Par m1' m2 k) ∨
  (∃ m2', may m2 m2' ∧ m' = Par m1 m2' k) ∨
  (∃ e1, m1 = throw e1 ∧ m' = k (O2Throw e1)) ∨
  (∃ e2, m2 = throw e2 ∧ m' = k (O2Throw e2)).
Proof.
  inversion 1; subst; eq_dep_inj; subst; eauto 15.
Qed.

Lemma invert_may_choose {A E B E'} (k : outcome2 B E' → micro A E) m1 m2 m' :
  may (Choose m1 m2 k) m' →
  m' = try2 m1 k ∨ m' = try2 m2 k.
Proof.
  inversion 1; subst; eq_dep_inj; subst; eauto 15.
Qed.

Lemma invert_may_bind {A B E} (m : micro A E) (k : A → micro B E) (m1 : micro B E) :
  may (bind m k) m1 →
  (∃ m', may m m' ∧ m1 = bind m' k) ∨
  (∃ a, m = ret a ∧ may (k a) m1).
Proof.
  revert m1; induction m; intros m'.
  - firstorder.
  - inversion 1.
  - inversion 1.
  - inversion 1; subst; now repeat econstructor.
  - intros M.
    left.
    destruct c; try solve [inversion M].
    + (* Stop CEval *)
      simpl in M.
      apply invert_may_eval in M. subst.
      destruct x as (η, e).
      repeat econstructor.
      by rewrite bind_as_try2, try2_try2, pfbind_as_pftry2.
    + (* Stop CLoop *)
      simpl in M; apply invert_may_loop in M; subst.
      destruct x as [[[[]]]].
      repeat econstructor. subst.
      by rewrite bind_as_try2, try2_try2, pfbind_as_pftry2.
  (* for [Stop CPerform] for every [o] the I.H. would provide an [m'] to which
     [k0 o] simplifies. But we would need some [k0'] s.t. [k0'; k] is [k'], then
     we could choose [m1 = Stop CPerform x (pfbind k0 K))] *)
  - (* Par: all shortcuts are compatible with [bind] *)
    simpl.
    intros M.
    left.
    apply invert_may_par in M.
    firstorder; subst.
    all: try solve [repeat (econstructor; eauto)].
    all: repeat econstructor.
    all: rewrite ?bind_as_try2, ?try2_try2, ?pftry2_join1,
        ?pftry2_join2, ?pfbind_as_pftry2; auto.
  - (* Choose *)
    simpl. intros [-> | ->]%invert_may_choose; left; eexists; split.
    1: apply MayChooseLeft.
    2: apply MayChooseRight.
    all: rewrite ?bind_as_try2, ?try2_try2, ?pfbind_as_pftry2; auto.
Qed.


(** The [immediately_pure] predicate excludes subterms that are about to perform
    a mutation step *)

Inductive immediately_pure {A E} : micro A E → Prop :=
  | ImmPure_Ret a : immediately_pure (Ret a)
  | ImmPure_Throw e : immediately_pure (Throw e)
  | ImmPure_Handle m k : immediately_pure m → immediately_pure (Handle m k)
  | ImmPure_Stop_Eval p k : immediately_pure (Stop CEval p k)
  | ImmPure_Stop_Loop p k : immediately_pure (Stop CLoop p k)
  | ImmPure_Par {A1 A2 E'} (m1 : micro A1 E') (m2 : micro A2 E') k :
    immediately_pure m1 →
    immediately_pure m2 →
    immediately_pure (Par m1 m2 k)
  | ImmPure_Choose {B E'} m1 m2 k : immediately_pure (@Choose _ _ B E' m1 m2 k).

(* Unused *)
Lemma immediately_pure_may {A E} (m : micro A E) :
  immediately_pure m →
  (∃ a, m = ret a) ∨ (∃ e, m = throw e) ∨ (∃ m', may m m').
Proof.
  intros P; dependent induction P; try solve [repeat econstructor]; right; right.
  - firstorder; subst; eauto with may.
  - destruct p; eauto with may.
  - destruct p as [[[[]]]]; eauto with may.
  - firstorder; subst; eauto with may.
Qed.

(* pure configuration can step *)
Lemma immediately_pure_can_step {A E} (m : micro A E) :
  immediately_pure m →
  (∃ a, m = ret a) \/ (∃ e, m = throw e) ∨ (∀ σ, can_step (σ, m)).
Proof.
  induction 1; eauto with step.
Qed.

(* [step]ping from a immediately pure configuration does not modify the store
   and correspond to a [may] reduction *)
Lemma immediately_pure_step_may {A E} (m m' : micro A E) σ σ' :
  immediately_pure m →
  step (σ, m) (σ', m') →
  may m m' ∧ σ' = σ.
Proof.
  intros P Hstep.
  revert P.
  dependent induction Hstep; intros P.
  all: try solve [repeat constructor | inversion P ].
  all: try solve [inversion P; subst; inversion H0 || eq_dep_inj; subst; now inversion H1].
  - (* handle *)
    specialize (IHHstep _ _ _ _ JMeq_refl JMeq_refl).
    inversion P; subst; eq_dep_inj; subst.
    firstorder repeat constructor; auto.
  - (* par left *)
    specialize (IHHstep _ _ _ _ JMeq_refl JMeq_refl).
    inversion P; subst; eq_dep_inj; subst.
    firstorder repeat constructor; auto.
  - (* par right *)
    specialize (IHHstep _ _ _ _ JMeq_refl JMeq_refl).
    inversion P; subst; eq_dep_inj; subst.
    firstorder repeat constructor; auto.
Qed.

(** The [pure_wp] predicate *)

(* [pure_wp m φ ψ] states that [m] is either a value satisfying [φ], a raised
exception satisfying [ψ], or can only do pure [may] reduction steps to states
[m'] also satisfying [pure_wp m' φ ψ]. It is somewhat a terminating and pure
version of the standard WP.

The syntactic [immediately_pure] requirement in the stepping case is needed as
[may] does not reduce mutations, and so the [pure_wp] predicate would be
oblivious to mutations. For example only the [MayParThrowLeft] construct applies
to [Par (Throw _) (Stop CStore _ _) _], so we forbid this configuration.
Alternatively, the may relation could reduce to [crash] in cases of mutations;
it would make the definition of [pure_wp] more elegant but it looks like we
might still require a purity property for intermediate proofs.

We also require [is_not_ret] in the stepping case, otherwise the universal
quantification on the [may] reductions of [ret _] would be vacuously true, and
similarly for [is_not_throw]. It corresponds to the [can_step] requirement in
the standard WP. *)

Inductive pure_wp {A E} : micro A E → (A → Prop) → (E → Prop) → Prop :=
  | pure_wp_ret (φ : A → Prop) ψ a : φ a → pure_wp (ret a) φ ψ
  | pure_wp_throw φ (ψ : E → Prop) e : ψ e → pure_wp (throw e) φ ψ
  | pure_wp_may φ ψ m :
    is_not_ret m →
    is_not_throw m →
    immediately_pure m →
    (∀ m', may m m' → pure_wp m' φ ψ) →
    pure_wp m φ ψ.

(* [pure_wp] is easy to reason about *)

Section pure_wp_results.
  Context {A E : Type} (φ : A → Prop) (ψ : E → Prop).

  Lemma pure_wp_immediately_pure m : pure_wp m φ ψ → immediately_pure m.
  Proof.
    induction 1; try econstructor; auto.
  Qed.

  Lemma pure_wp_may_forward m m' : pure_wp m φ ψ → may m m' → pure_wp m' φ ψ.
  Proof.
    induction 1; auto; inversion 1.
  Qed.

  Lemma invert_pure_wp_ret a : pure_wp (ret a) φ ψ → φ a.
  Proof.
    intros S; remember (ret a) as m; revert a Heqm.
    induction S; try congruence. destruct m; discriminate.
  Qed.

  Lemma invert_pure_wp_throw e : pure_wp (throw e) φ ψ → ψ e.
  Proof.
    intros S; remember (throw e) as m; revert e Heqm.
    induction S; try congruence. destruct m; discriminate.
  Qed.

  Lemma pure_wp_step {m σ m' σ'} :
    pure_wp m φ ψ → step (σ, m) (σ', m') → σ' = σ ∧ pure_wp m' φ ψ.
  Proof.
    intros Hm Hstep.
    pose proof immediately_pure_step_may _ _ _ _ (pure_wp_immediately_pure _ Hm) Hstep.
    firstorder eauto using pure_wp_may_forward.
  Qed.
End pure_wp_results.

(* TODO generalize to try2 *)
Lemma pure_wp_bind {A' A E} (φ : A → Prop) (ψ : E → Prop) (φ' : A' → Prop) m k :
  pure_wp m φ ψ →
  (∀ a, φ a → pure_wp (k a) φ' ψ) →
  pure_wp (bind m k) φ' ψ.
Proof.
  induction 1 as [ Ha | e | φ ψ m Nret Nthr Pm Hm IHm]; intros Hk; simpl; auto.
  - by constructor.
  - assert (Sm : pure_wp m φ ψ) by now econstructor.
    constructor.
    + destruct m; simpl; discriminate || congruence.
    + destruct m; simpl; discriminate || congruence.
    + inversion Pm; subst; try by constructor. discriminate.
    + intros m1 [(m' & Hm' & ->) | (a & -> & Hm1)]%invert_may_bind; eauto.
      eapply pure_wp_may_forward; eauto. apply invert_pure_wp_ret in Sm; auto.
Qed.
Import syntax.

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
      inversion Hm; subst. inversion H1.

  - (* [m] is not handleable *)
    intro_state.
    ewp_mask_intro "Hmod".
    iSplit.
    + (* so [m] can step because it is [pure_wp] *)
      inversion Hm; subst; try discriminate.
      iPureIntro.
      edestruct (immediately_pure_can_step m) as [(a, ->) | [(e, ->) | ? ]];
        auto; discriminate.
    + (* and no step changes [σ] or escapes [pure_wp] *)
      intro_step.
      ewp_cleanup_mod. ewp_mask_elim.
      destruct (pure_wp_step _ _ Hm Hstep) as [<- Hm'].
      iFrame.
      by iApply "IH".
Qed.
