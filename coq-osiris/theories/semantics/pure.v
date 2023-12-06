From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step simplification.

(* -------------------------------------------------------------------------- *)

(* The judgement [pure m φ] asserts that the computation [m] can be simplified
   to [ret #a], where [a] is a (logical) value so that [φ a] holds. *)

Definition pure `{Encode A} (m : micro val) (φ : A → Prop) :=
  ∃ a, simp m (ret #a) ∧ φ a.

(* -------------------------------------------------------------------------- *)

(* Inversion tactics. *)

Ltac destruct_pure a :=
  match goal with h: pure _ _ |- _ =>
    destruct h as (a & ? & ?)
  end.

Ltac destruct_encode_image a :=
  match goal with h: ∃ _, ?v = #_ ∧ _ |- _ =>
    destruct h as (a & ? & ?); try subst v
  end.

(* -------------------------------------------------------------------------- *)

(* [pure] can also be defined in terms of [totalv]. *)

Lemma pure_totalv `{Encode A} (m : micro val) (φ : A → Prop) :
  pure m φ ↔
  totalv m (λ v, ∃ a, v = #a ∧ φ a).
Proof.
  split.
  { intros. destruct_pure a. eauto using totalv_simp, totalv_ret. }
  { intros. destruct_total v. destruct_encode_image a. unfold pure. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A reasoning rule for [ret]. *)

(* The subgoal [v = #a] is explicitly isolated so as to make this lemma
   more widely applicable. A subgoal of the form [v = #a], where [a] is
   a Coq metavariable, can be solved by the tactic [encode]. *)

Lemma pure_ret `{Encode A} (φ : A → Prop) v a :
  v = #a →
  φ a →
  pure (ret v) φ.
Proof.
  rewrite pure_totalv. eauto using totalv_ret.
Qed.

(* The consequence rule. *)

Lemma pure_consequence `{Encode A} m (φ ψ : A → Prop) :
  pure m φ →
  (∀ a, φ a → ψ a) →
  pure m ψ.
Proof.
  (* We could give a direct proof. We go through [totalv]. *)
  rewrite !pure_totalv. intros. eapply totalv_consequence; [ eauto |].
  simpl. intros v Hv. destruct_encode_image a. eauto.
Qed.

(* The simplification rule. *)

Lemma pure_simp `{Encode A} m m' (φ : A → Prop) :
  simp m m' →
  pure m' φ →
  pure m φ.
Proof.
  rewrite !pure_totalv. eauto using totalv_simp.
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [Next],
   so the handler [z] is dead and no proof obligation bears on it. *)

Lemma pure_try A (_ : Encode A) B (_ : Encode B)
  (m : micro val) (k : val → micro val) (z : unit → micro val)
  (φ : A → Prop) (ψ : B → Prop)
:
  pure m φ →
  (∀ a, φ a → pure (k #a) ψ) →
  pure (try m k z) ψ.
Proof.
  (* We could give a direct proof. We go through [totalv]. *)
  rewrite !pure_totalv. intros. eapply totalv_try; [ eauto |].
  simpl. intros v Hv. destruct_encode_image a.
  rewrite <- pure_totalv. eauto.
Qed.

(* A reasoning rule for [bind]. *)

(* This is [@bind val val]. Attempting to apply this lemma to [@bind A B]
   where [A] and [B] are types other than [val] will not work! *)

Lemma pure_bind A (_ : Encode A) B (_ : Encode B)
  (m : micro val) (k : val → micro val)
  (φ : A → Prop) (ψ : B → Prop)
:
  pure m φ →
  (∀ a, φ a → pure (k #a) ψ) →
  pure (bind m k) ψ.
Proof.
  rewrite bind_as_try. eauto using pure_try.
Qed.

Lemma pure_bind_unary A (_ : Encode A) B (_ : Encode B)
  (m : micro val) (k : val → micro val)
  (ψ : B → Prop)
:
  pure m (λ (a : A), pure (k #a) ψ) →
  pure (bind m k) ψ.
Proof.
  eauto using pure_bind.
Qed.

(* A reasoning rule for [Par m1 m2 k z]. *)

(* We cannot give a reasoning rule for [par m1 m2] because its type is
   [micro (val * val)], not [micro val]. However, we can give a rule
   for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

Lemma pure_par `{Encode A1, Encode A2, Encode A} m1 m2
  (k : val * val → micro val) (z : unit → micro val)
  (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  pure m1 φ1 →
  pure m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → pure (k (#a1, #a2)) φ) →
  pure (Par m1 m2 k z) φ.
Proof.
  rewrite !pure_totalv. intros Hm1 Hm2 Hentail. rewrite <- try_par.
  eapply totalv_try.
  { eapply totalv_par with (φ := λ v, pure (k v) φ); [ eauto | eauto |].
    simpl. intros v1 v2 ? ?.
    destruct_encode_image a2. destruct_encode_image a1.
    eauto. }
  { intros v. rewrite <- pure_totalv. tauto. }
Qed.

(* A reasoning rule for [choose]. *)

Lemma pure_choose `{Encode A} m1 m2 (φ : A → Prop) :
  pure m1 φ →
  pure m2 φ →
  deterministic φ →
  pure (choose m1 m2) φ.
Proof.
  rewrite !pure_totalv.
  intros. eapply totalv_choose; [ eauto | eauto |].
  unfold deterministic.
  intros v1 v2 ? ?. destruct_encode_image a2. destruct_encode_image a1.
  assert (a1 = a2) by eauto.
  congruence.
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

Lemma pure_intersection `{Inhabited X} `{EncodeInjective A}
  m (φ : X → A → Prop)
:
  (∀ x, pure m (φ x)) →
  pure m (λ a, ∀ x, φ x a).
Proof.
  intros. rewrite pure_totalv.
  eapply totalv_consequence; [| intro; eapply exploit_injectivity ].
  eapply totalv_intersection.
  intros. rewrite <- pure_totalv. eauto.
Qed.

(* The binary intersection rule. *)

(* This rule requires the encoding function [# : A → val] to be injective]. *)

Lemma pure_binary_intersection `{EncodeInjective A} m (φ1 φ2 : A → Prop) :
  pure m φ1 →
  pure m φ2 →
  pure m (λ a, φ1 a ∧ φ2 a).
Proof.
  intros.
  set (post := λ (b : bool), λ a, if b then φ1 a else φ2 a).
  eapply pure_consequence with (φ := λ a, ∀ b, post b a).
  { eapply pure_intersection.
    intros b. destruct b; unfold post; assumption. }
  { intros a Hpost. split.
    + apply (Hpost true).
    + apply (Hpost false). }
Qed.

(* This is the reciprocal bind rule for [pure]. *)

(* Because [pure m _] requires the result of [m] to lie in the image of the
   function [encode], and because this image cannot include every inhabitant
   of the type [val], we cannot expect that [pure (bind m k) φ] implies
   [pure m _]. Thus, we can establish the reciprocal bind rule only under
   the side condition [pure m (λ a, True)], which means that the result of
   the computation [m] lies in the image of the function [encode] at type
   [A]. *)

Lemma invert_pure_bind `{Encode A, Encode B} m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure m (λ (a : A), True) →
  pure m (λ (a : A), pure (k #a) φ).
Proof.
  intros Hmk Hm.
  rewrite pure_totalv in Hmk.
  apply invert_totalv_bind in Hmk.
  destruct_total v.

  (* The problem that we now face is to prove that the value [v] produced
     by [m] must be of the form [#a]. The hypothesis [Hm] is necessary for
     this purpose. *)
  destruct_pure a. simp_ret_confluent. subst v.

  (* We can then conclude. *)
  unfold pure. exists a. split; [ eauto |].
  destruct_total v. destruct_encode_image b. eauto.
Qed.

(* That said, if we take the type [A] to be [val], then -- because [encode]
   at type [val] is the identity function -- this side condition becomes
   trivial, and we can prove a version of the rule that does not have this
   side condition. *)

Lemma invert_pure_bind' `{Encode B} m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure m (λ (v : val), pure (k v) φ).
Proof.
  intros Hmk.
  rewrite pure_totalv in Hmk.
  apply invert_totalv_bind in Hmk.
  destruct_total v.
  unfold pure. exists v. split; [ eauto |].
  destruct_total v'. destruct_encode_image b. eauto.
Qed.
