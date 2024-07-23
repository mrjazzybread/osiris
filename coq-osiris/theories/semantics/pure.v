From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step simplification pure_wp total.

(* -------------------------------------------------------------------------- *)

(* The judgement [pure m φ] asserts that the computation [m] can be simplified
   to [ret #a], where [a] is a (logical) value so that [φ a] holds. *)

Definition pure `{Encode A} {X} (m : micro val X) (φ : A → Prop) :=
  totalv m (λ v, ∃ a, v = #a ∧ φ a).

(* -------------------------------------------------------------------------- *)

(* Inversion tactics. *)

(*
Ltac destruct_pure a :=
  match goal with h: pure _ _ |- _ =>
    destruct h as (a & ? & ?)
  end.
*)

Ltac destruct_encode_image a :=
  match goal with h: ∃ _, ?v = #_ ∧ _ |- _ =>
    destruct h as (a & ? & ?); try subst v
  end.

(* -------------------------------------------------------------------------- *)

(* [pure] can also be defined in terms of [totalv] and in terms of [total]. *)

Lemma pure_totalv `{Encode A} {X} (m : micro val X) (φ : A → Prop) :
  pure m φ ↔
  totalv m (λ v, ∃ a, v = #a ∧ φ a).
Proof.
  reflexivity.
Qed.

Lemma pure_total `{Encode A} {X} (m : micro val X) (φ : A -> Prop) :
  pure m φ <->
  total m (λ v, ∃ a, v = #a ∧ φ a) (λ _, False).
Proof.
  apply pure_totalv.
Qed.

(* [pure (try _ _ _)] can be expressed in terms of [total]. *)

Lemma total_pure_try {B E E'} `{Encode A} (m : micro B E')
  (k : _ -> micro val E) (ko : E' -> micro val E)  (φ : A -> Prop)
  :
  total m (λ v, pure (k v) φ) (λ e, pure (ko e) φ) ->
  pure (try m k ko) φ.
Proof.
  intros. apply pure_total.
  eapply total_try; [ eassumption | | ]; firstorder eauto.
Qed.

(* [pure_try_total] is currently unused *)

(* Lemma pure_try_total {B E} `{Encode A} (m : micro B E) *)
(*   (k : _ -> micro val A) ko (φ : A -> Prop) : *)
(*   pure (try m k ko) φ -> *)
(*   total m (λ v, pure (k v) φ) (λ e, pure (ko e) φ). *)
(* Proof. *)
(*   intros Hp. destruct_pure a. *)
(*   eapply total_consequence. *)
(*   { eapply invert_simp_try_ret; eassumption. } *)
(*   { simpl; intros. exists a; tauto. } *)
(*   { simpl; intros. exists a; tauto. } *)
(* Qed. *)


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
  rewrite pure_totalv. eauto using totalv_ret.
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
  (* We could give a direct proof. We go through [totalv]. *)
  rewrite !pure_totalv. intros. eapply totalv_consequence; [ eauto |].
  simpl. intros v Hv. destruct_encode_image a. eauto.
Qed.

(* The simplification rule. *)

Lemma pure_simp `{Encode A} {X} m m' (φ : A → Prop) :
  simp m m' →
  pure (X := X) m' φ →
  pure (X := X) m φ.
Proof.
  rewrite !pure_totalv. eauto using totalv_simp.
Qed.

(* Corollary when simplifying to a return *)

Lemma pure_simp_ret `{Encode A} {X : Type} (m : micro val X) (a : A) :
  simp m (ret #a) → pure m (λ a', a' = a).
Proof.
  intros. eapply pure_simp; eauto.
  eapply pure_ret; eauto.
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
  (* We could give a direct proof. We go through [totalv]. *)
  rewrite !pure_totalv. intros. eapply totalv_try2; [ eauto |].
  simpl. intros v Hv. destruct_encode_image a.
  rewrite <- pure_totalv. eauto.
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
  rewrite !pure_totalv. intros Hm1 Hm2 Hentail. rewrite <- try_par.
  eapply totalv_try.
  { eapply totalv_par with (φ := λ v, pure (k v) φ); [ eauto | eauto |].
    simpl. intros v1 v2 ? ?.
    destruct_encode_image a2. destruct_encode_image a1.
    eauto. }
  { intros v. rewrite <- pure_totalv. tauto. }
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

(* TODO: I do not seem to be able to use those, for example in simp_eval.v's
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
