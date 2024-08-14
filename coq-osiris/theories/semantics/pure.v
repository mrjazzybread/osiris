From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step simplification pure_wp.

(* -------------------------------------------------------------------------- *)

(* The judgement [pure m φ] asserts that the computation [m] can be simplified
   to [ret #a], where [a] is a (logical) value so that [φ a] holds. *)

Definition pure `{Encode A} {X} (m : micro val X) (φ : A → Prop) :=
  pure_wp m (λ v, ∃ a, v = #a ∧ φ a) (λ _, False).

(* -------------------------------------------------------------------------- *)

(* Inversion tactic. *)

Ltac destruct_encode_image a :=
  match goal with h: ∃ _, ?v = #_ ∧ _ |- _ =>
    destruct h as (a & ? & ?); try subst v
  end.

(* -------------------------------------------------------------------------- *)

(* A reasoning rule for [ret]. *)

(* The subgoal [v = #a] is explicitly isolated so as to make this lemma
   more widely applicable. A subgoal of the form [v = #a], where [a] is
   a Coq metavariable, can be solved by the tactic [encode]. *)

Lemma pure_ret `{Encode A} {X} (φ : A → Prop) v a :
  v = #a →
  φ a →
  pure (X := X) (ret v) φ.
Proof.
  unfold pure; eauto using pure_wp_ret.
Qed.

(* A reasoning rule for ret that can instantiate the goal when it is an evar *)

Lemma pure_ret_eq `{Encode A} {X : Type} (a : A) :
  pure (X := X) (ret #a) (λ a', a' = a).
Proof.
  intros.
  eapply pure_ret; eauto.
Qed.

(* The consequence rule. *)

Lemma pure_consequence `{Encode A} {X} m (φ ψ : A → Prop) :
  pure m φ →
  (∀ a, φ a → ψ a) →
  pure (X := X) m ψ.
Proof.
  intros. eapply pure_wp_mono_ret; [ eauto |].
  firstorder.
Qed.

(* A reasoning rule for [try2]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [throw _],
   so the handler [z] is dead and no proof obligation bears on it. *)

Lemma pure_try2 A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) h (φ : A → Prop) (ψ : B → Prop)
  :
  pure m φ →
  (∀ a, φ a → pure (continue h #a) ψ) →
  pure (X := Y) (try2 m h) ψ.
Proof.
  intros. eapply pure_wpv_try2_compat; eauto.
  simpl. intros v Hv. destruct_encode_image a. firstorder.
Qed.

(* A reasoning rule for [try]; corollary of [pure_try2] *)

Corollary pure_try A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) k z (φ : A → Prop) (ψ : B → Prop)
:
  pure m φ →
  (∀ a, φ a → pure (k #a) ψ) →
  pure (X := Y) (try m k z) ψ.
Proof.
  intros; eapply pure_try2; eauto.
Qed.

(* A reasoning rule for [bind]. *)

(* This is [@bind val val]. Attempting to apply this lemma to [@bind A B]
   where [A] and [B] are types other than [val] will not work! *)

Lemma pure_bind A X (_ : Encode A) B (_ : Encode B)
  m k (φ : A → Prop) (ψ : B → Prop)
:
  pure m φ →
  (∀ a, φ a → pure (k #a) ψ) →
  pure (X := X) (bind m k) ψ.
Proof.
  rewrite bind_as_try. eauto using pure_try.
Qed.

Lemma pure_bind_unary A X (_ : Encode A) B (_ : Encode B)
  m k (ψ : B → Prop)
:
  pure m (λ (a : A), pure (k #a) ψ) →
  pure (X := X) (bind m k) ψ.
Proof.
  eauto using pure_bind.
Qed.

(* A reasoning rule for [Par m1 m2 k z]. *)

(* We cannot give a reasoning rule for [par m1 m2] because its type is
   [micro (val * val)], not [micro val]. However, we can give a rule
   for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

Lemma pure_par `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  pure (X := X) m1 φ1 →
  pure m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → pure (k (#a1, #a2)) φ) →
  pure (X := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros Hm1 Hm2 Hentail. rewrite <- try_par.
  eapply pure_wpv_try_compat.
  { eapply pure_wp__par with (φ := λ v, pure (k v) φ); [ eauto | eauto |].
    simpl. intros v1 v2 ? ?.
    destruct_encode_image a2. destruct_encode_image a1.
    eauto. }
  { intros v. tauto. }
Qed.

Lemma pure_par' `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  pure (X := X) m1 φ1 →
  pure m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → pure (continue k (#a1, #a2)) φ) →
  pure (X := Y) (Par m1 m2 k) φ.
Proof.
  intros. eapply pure_wp_par_compat; eauto; firstorder subst; eauto.
Qed.

(* Sequentializations of previous lemmas, considering the LHS first *)

(* TODO: I do not seem to be able to use those, for example in pure_eval.v's
[pure_eval_pair] *)

Lemma pure_par_seq `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  pure (X := X) m1 (λ a1 : A1, pure m2 (λ a2 : A2, pure (k (#a1, #a2)) φ)) →
  pure (X := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros Hm1.
  apply pure_wp_par_vals_left.
  eapply (pure_wp_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
  eapply (pure_wp_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
  eauto.
Qed.

Lemma pure_par_seq' `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  pure (X := X) m1 (λ a1 : A1, pure m2 (λ a2 : A2, pure (continue k (#a1, #a2)) φ)) →
  pure (X := Y) (Par m1 m2 k) φ.
Proof.
  intros Hm1.
  apply pure_wp_par_vals_left.
  eapply (pure_wp_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
  eapply (pure_wp_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
  eauto.
Qed.

(* A reasoning rule for [choose]. *)

Lemma pure_choose `{Encode A} {X} m1 m2 (φ : A → Prop) :
  pure (X := X) m1 φ →
  pure m2 φ →
  pure (choose m1 m2) φ.
Proof.
  apply pure_wp_choose.
Qed.

(* The infinitary intersection rule. *)

(* This rule requires the encoding function [# : A → val] to be injective]. *)

Lemma exploit_injectivity `{Inhabited X} `{EncodeInjective A}
  v (φ : X → A → Prop)
:
  (∀ x, ∃ a, v = #a ∧ φ x a) →
  ∃ a, v = #a ∧ (∀ x, φ x a).
Proof.
  intros Hxa.
  generalize (Hxa inhabitant); intros. destruct_encode_image a.
  exists a. split; [ eauto |].
  intros x. destruct (Hxa x) as (a' & Heq & ?).
  apply encode_injective in Heq. congruence.
Qed.


(* This is the reciprocal bind rule for [pure]. *)

(* Because [pure m _] requires the result of [m] to lie in the image of the
   function [encode], and because this image cannot include every inhabitant
   of the type [val], we cannot expect that [pure (bind m k) φ] implies
   [pure m _]. Thus, we can establish the reciprocal bind rule only under
   the side condition [pure m (λ a, True)], which means that the result of
   the computation [m] lies in the image of the function [encode] at type
   [A]. *)

Lemma invert_pure_bind `{Encode A, Encode B} X m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure m (λ (a : A), True) →
  pure (X := X) m (λ (a : A), pure (k #a) φ).
Proof.
  intros Hmk%invert_pure_wp_bind Hm.
  pose proof pure_wp_binary_intersection _ Hmk Hm as I.
  eapply (pure_wp_mono _ I); firstorder subst; eauto.
Qed.

(* That said, if we take the type [A] to be [val], then -- because [encode]
   at type [val] is the identity function -- this side condition becomes
   trivial, and we can prove a version of the rule that does not have this
   side condition. *)

Lemma invert_pure_bind' `{Encode B} {X} m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure (X := X) m (λ (v : val), pure (k v) φ).
Proof.
  intros Hmk%invert_pure_wp_bind.
  eapply pure_wp_mono; eauto.
Qed.
