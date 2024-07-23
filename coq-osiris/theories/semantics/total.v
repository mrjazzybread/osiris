From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.
From osiris.semantics Require Import simplification pure_wp.

(* This file gives bindings to use [pure_wp] instead of [simp] as the definition
   of [total] (see [simplications.v] for the original definitions) *)

Definition total {A E} := @pure_wp A E.

(* The judgement [totalv m φ] is the special case where [ψ] is [λ _, False].
   It means that [m] must terminate and produce a result [a] such that [φ a]
   holds. *)

Definition totalv {A E} m (φ : A → Prop) :=
  total m φ (λ (e : E), False).

(* The tactic [destruct_total a e] destructs a hypothesis of the form
   [total m φ ψ] or [totalv m φ]. The result of [m], if there is one,
   is named [a]. The exception, if there is one, is named [e]. *)

Ltac destruct_total a e :=
  fail "destruct_total deals with simplification.total, not total = pure_wp".

(* The reasoning rule for [ret _]. *)

Lemma total_ret {A E} a (φ : A → Prop) (ψ : E → Prop) :
  φ a →
  total (ret a) φ ψ.
Proof.
  apply pure_wp_ret.
Qed.

(* The reasoning rule for [throw _]. *)

Lemma total_throw {A E} e (φ : A → Prop) (ψ : E → Prop) :
  ψ e →
  total (throw e) φ ψ.
Proof.
  apply pure_wp_throw.
Qed.

(* The consequence rule. *)

Lemma total_consequence {A E} m (φ φ' : A → Prop) (ψ ψ' : E → Prop) :
  total m φ ψ →
  (∀ a, φ a → φ' a) →
  (∀ e, ψ e → ψ' e) →
  total m φ' ψ'.
Proof.
  apply pure_wp_mono.
Qed.

(* The simplification rule. *)

(* This rule allows performing a simplification step in the middle
   of a Hoare-style proof. *)

(* Although there is no reasoning rule for [Stop], the lemma [total_simp] can
   be used to reason about [Stop CEval] and [Stop CLoop]. *)

Lemma total_simp {A E} m m' (φ : A → Prop) (ψ : E → Prop) :
  simp m m' →
  total m' φ ψ →
  total m φ ψ.
Proof.
  apply pure_wp_simp.
Qed.

(* A reasoning rule for [try2]. *)

Lemma total_try2 {A B E' E} m h
  (φ : B → Prop) (φ' : A → Prop)
  (ψ : E → Prop) (ψ' : E' → Prop) :
  total m φ' ψ' →
  (∀ a, φ' a → total (continue h a) φ ψ) →
  (∀ e, ψ' e → total (discontinue h e) φ ψ) →
  total (try2 m h) φ ψ.
Proof.
  apply pure_wp_try2_compat.
Qed.

(* A reasoning rule for [try]. *)

Corollary total_try {A B E' E} m f g
  (φ : B → Prop) (φ' : A → Prop)
  (ψ : E → Prop) (ψ' : E' → Prop) :
  total m φ' ψ' →
  (∀ a, φ' a → total (f a) φ ψ) →
  (∀ e, ψ' e → total (g e) φ ψ) →
  total (try m f g) φ ψ.
Proof.
  intros; eapply total_try2; eauto.
Qed.

(* A reasoning rule for [orelse]. *)

Lemma total_orelse {A E} (m1 m2 : micro A E) φ ψ1 ψ :
  total m1 φ ψ1 →
  (∀ e, ψ1 e → total m2 φ ψ) →
  total (orelse m1 m2) φ ψ.
Proof.
  intros Hm1 H2. unfold orelse. eauto using total_try, total_ret.
Qed.

(* A reasoning rule for [bind]. *)

Lemma total_bind {A B E} m f
  (φ : B → Prop) (φ' : A → Prop) (ψ : E → Prop) :
  total m φ' ψ →
  (∀ a, φ' a → total (f a) φ ψ) →
  total (bind m f) φ ψ.
Proof.
  rewrite bind_as_try. eauto using total_try, total_throw.
Qed.

Lemma total_bind_unary {A B E} m f (φ : B → Prop) (ψ : E → Prop) :
  total m (λ (a : A), total (f a) φ ψ) ψ →
  total (bind m f) φ ψ.
Proof.
  eauto using total_bind.
Qed.

(* A reasoning rule for [par]. *)

(* This rule requires the exception predicate [ψ] to be deterministic, otherwise
   [Par (throw e) (throw e') _] cannot be simplified *)

Definition deterministic {A} (φ : A → Prop) :=
  ∀ a1 a2, φ a1 → φ a2 → a1 = a2.

Lemma total_par {A1 A2 E} m1 m2 φ1 φ2 (φ : A1 * A2 → Prop) (ψ : E → Prop) :
  deterministic ψ → (* TODO remove, unused *)
  total m1 φ1 ψ →
  total m2 φ2 ψ →
  (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
  total (par m1 m2) φ ψ.
Proof.
  intros.
  eapply pure_wp_par_compat; firstorder eauto; constructor; firstorder.
Qed.

(* A reasoning rule for [choose]. *)

(* This rule is limited to the case where [φ] is deterministic because we
   must ensure that [m1] and [m2] produce the same result. Indeed, unlike
   [step], the relation [simp] can simplify [choose m1 m2] only if both
   sides produce the same result. *)

(* This rule is limited to the case where [ψ] is [λ _, False] because we
   cannot allow [m1] to raise an exception while [m2] terminates, or
   vice-versa. *)

Lemma total_choose {A E} m1 m2 (φ : A → Prop) :
  let ψ := λ (_ : E), False in (* TODO remove *)
  total m1 φ ψ →
  total m2 φ ψ →
  deterministic φ → (* TODO remove *)
  total (choose m1 m2) φ ψ.
Proof.
  intros; eapply pure_wp_choose; eauto.
Qed.

(* The infinitary intersection rule. *)

(* If for every [x] one can prove that the result of [m] satisfies [φ x],
   then one can deduce that the result of [m] satisfies [φ x] for every
   [x] simultaneously. *)

Lemma total_intersection {A E} `{Inhabited X}
  m (φ : X → A → Prop) (ψ : E → Prop) :
  (∀ x, total m (φ x) ψ) →
  total m (λ a, ∀ x, φ x a) ψ.
Proof.
  apply pure_wp_intersection.
Qed.

(* The binary intersection rule. *)

(* If one can prove that the result of [m] satisfies [φ1]
   and if one can prove that the result of [m] satisfies [φ2]
   then one can deduce that the result of [m] satisfies [φ1] and [φ2]
   simultaneously. *)

Lemma total_binary_intersection {A E} m (φ1 φ2 : A → Prop) (ψ : E → Prop) :
  total m φ1 ψ →
  total m φ2 ψ →
  total m (λ a, φ1 a ∧ φ2 a) ψ.
Proof.
  intros.
  set (post := λ (b : bool), λ a, if b then φ1 a else φ2 a).
  eapply total_consequence with (φ := λ a, ∀ b, post b a) (ψ := ψ).
  { eapply total_intersection.
    intros b. destruct b; unfold post; assumption. }
  { intros a Hpost. split.
    + apply (Hpost true).
    + apply (Hpost false). }
  { tauto. }
Qed.

(* The infinitary intersection rule. *)

Lemma totalv_intersection {A E} `{Inhabited X} (m : micro A E) (φ : X → A → Prop) :
  (∀ x, totalv m (φ x)) →
  totalv m (λ a, ∀ x, φ x a).
Proof.
  unfold totalv. eauto using total_intersection.
Qed.

(* The binary intersection rule. *)

Lemma totalv_binary_intersection {A E} (m : micro A E) (φ1 φ2 : A → Prop) :
  totalv m φ1 →
  totalv m φ2 →
  totalv m (λ a, φ1 a ∧ φ2 a).
Proof.
  unfold totalv. eauto using total_binary_intersection.
Qed.

(* -------------------------------------------------------------------------- *)

(* Special cases of the above rules for [totalv]. *)

(* These rules may seem a bit trivial, but it is probably preferable to state
   them explicitly and have them at hand, rather than attempt to reconstruct
   them on the fly every time they are needed. *)

(* The reasoning rule for [ret _]. *)

Lemma totalv_ret {A E} a (φ : A → Prop):
  φ a →
  totalv (ret a : micro A E) φ.
Proof.
  unfold totalv. eauto using total_ret.
Qed.

(* The consequence rule. *)

Lemma totalv_consequence {A E} (m : micro A E) (φ φ' : A → Prop) :
  totalv m φ →
  (∀ a, φ a → φ' a) →
  totalv m φ'.
Proof.
  unfold totalv. eauto using total_consequence.
Qed.

(* The simplification rule. *)

Lemma totalv_simp {A E} (m m' : micro A E) (φ : A → Prop) :
  simp m m' →
  totalv m' φ →
  totalv m φ.
Proof.
  unfold totalv. eauto using total_simp.
Qed.

(* [simp m (ret a)] is equivalent (TODO now only implies) to a Hoare logic judgement [totalv m _]
   whose postcondition is an equality [λ a', a = a']. *)

Lemma simp_totalv {A E} m (a : A) :
  simp m (ret a : micro A E) →
  totalv m (λ a', a = a').
Proof.
  eauto using totalv_simp, totalv_ret.
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [throw _],
   so the handler [g] is dead and no proof obligation bears on it. *)

Lemma totalv_try2 {A B E' E} m (h : outcome2 _ E' → micro B E)
  (φ : B → Prop) (φ' : A → Prop) :
  totalv m φ' →
  (∀ a, φ' a → totalv (continue h a) φ) →
  totalv (try2 m h) φ.
Proof.
  unfold totalv. intros.
  eapply total_try2; try solve [ eauto | simpl; tauto ].
Qed.

(* A reasoning rule for [try]. *)

(* Corollary of [totalv_try2] *)

Corollary totalv_try {A B E' E} m f (g : E' → micro B E)
  (φ : B → Prop) (φ' : A → Prop) :
  totalv m φ' →
  (∀ a, φ' a → totalv (f a) φ) →
  totalv (try m f g) φ.
Proof.
  intros; eapply totalv_try2; eauto.
Qed.

(* A reasoning rule for [bind]. *)

Lemma totalv_bind {A B E} (m : micro A E) f (φ : B → Prop) (φ' : A → Prop) :
  totalv m φ' →
  (∀ a, φ' a → totalv (f a) φ) →
  totalv (bind m f) φ.
Proof.
  unfold totalv. eauto using total_bind.
Qed.

Lemma totalv_bind_unary {A B E} (m : micro A E) f (φ : B → Prop) :
  totalv m (λ (a : A), totalv (f a) φ) →
  totalv (bind m f) φ.
Proof.
  eauto using totalv_bind.
Qed.

(* A reasoning rule for [par]. *)

Lemma totalv_par {A1 A2 E} (m1 m2 : micro _ E) φ1 φ2 (φ : A1 * A2 → Prop) :
  totalv m1 φ1 →
  totalv m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
  totalv (par m1 m2) φ.
Proof.
  unfold totalv.
  apply total_par.
  intros ? ? [].
Qed.

(* A reasoning rule for [choose]. *)

Lemma totalv_choose {A E} (m1 m2 : micro A E) (φ : A → Prop) :
  totalv m1 φ →
  totalv m2 φ →
  deterministic φ →
  totalv (choose m1 m2) φ.
Proof.
  unfold totalv. eauto using total_choose.
Qed.

(* This is the reciprocal bind rule for [totalv]. *)

Lemma invert_totalv_bind {A B E} m (k : A → micro B E) (φ : B → Prop) :
  totalv (bind m k) φ →
  totalv m (λ a, totalv (k a) φ).
Proof.
  apply invert_pure_wp_bind.
Qed.

(* [widen] does not change the [totalv] relation *)
Lemma totalv_widen {A E} (m : micro A void) Φ :
  totalv (E := E) (widen m) Φ <-> totalv m Φ.
Proof.
  apply pure_wp_widen'.
Qed.
