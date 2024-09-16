From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code.

From osiris.program_logic.pure Require Export pure_judgement pure_notation.

(* -------------------------------------------------------------------------- *)

(* Inversion tactic. *)

Ltac returns_eauto :=
  match goal with
  | h: returns _ ?v |- _ =>
      let a := fresh "v" in
      let Ha_ensures := fresh "Ha_ensures" in
      destruct h as (a & ? & Ha_ensures); try subst v
  end.

#[export]
  Hint Extern 1 (pure _ (returns _) _) => returns_eauto; by firstorder : pure.

#[export]
  Hint Extern 1 ({ _ ?v ensures _ }) => returns_eauto : pure.

#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

(* -------------------------------------------------------------------------- *)

(* A reasoning rule for [ret]. *)

(* The subgoal [v = #a] is explicitly isolated so as to make this lemma
   more widely applicable. A subgoal of the form [v = #a], where [a] is
   a Coq metavariable, can be solved by the tactic [encode]. *)

Lemma jm_ret `{Encode A} {E} (φ : A → Prop) v a :
  v = #a →
  φ a →
  jm (E := E) (ret v) φ.
Proof.
  intros; apply pure_ret; esplit; eauto.
Qed.

(* A reasoning rule for ret that can instantiate the goal when it is an evar *)

Lemma jm_ret_eq `{Encode A} {X : Type} (a : A) :
  jm (E := X) (ret #a) (λ a', a' = a).
Proof.
  intros.
  eapply jm_ret; eauto.
Qed.

Lemma jm_returns `{Encode A} {X : Type}
  (a : val) (k : val -> micro val X) (φ : A -> Prop):
  jm (E := X) (k a) φ ->
  returns (λ v : val, { k v ensures φ }) a.
Proof.
  intros; eauto with pure.
Qed.

(* The consequence rule. *)

Lemma jm_consequence `{Encode A} {X} m (φ ψ : A → Prop) :
  jm m φ →
  (∀ a, φ a → ψ a) →
  jm (E := X) m ψ.
Proof.
  intros. eapply pure_mono_ret; [ eauto |].
  firstorder.
Qed.

(* A reasoning rule for [try2]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [throw _],
   so the handler [z] is dead and no proof obligation bears on it. *)

Lemma jm_try2 A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) h (φ : A → Prop) (ψ : B → Prop)
  :
  jm m φ →
  (∀ a, φ a → jm (continue h #a) ψ) →
  jm (E := Y) (try2 m h) ψ.
Proof.
  intros. eapply purev_try2_conseq; eauto.
  simpl. intros v Hv.
  eauto with pure.
Qed.

(* A reasoning rule for [try]; corollary of [jm_try2] *)

Corollary jm_try A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) k z (φ : A → Prop) (ψ : B → Prop)
:
  jm m φ →
  (∀ a, φ a → jm (k #a) ψ) →
  jm (E := Y) (try m k z) ψ.
Proof.
  intros; eapply jm_try2; eauto.
Qed.

(* A reasoning rule for [bind]. *)

(* This is [@bind val val]. Attempting to apply this lemma to [@bind A B]
   where [A] and [B] are types other than [val] will not work! *)

Lemma jm_bind A X (_ : Encode A) B (_ : Encode B)
  m k (φ : A → Prop) (ψ : B → Prop)
:
  jm m φ →
  (∀ a, φ a → jm (k #a) ψ) →
  jm (E := X) (bind m k) ψ.
Proof.
  rewrite bind_as_try. eauto using jm_try.
Qed.

Lemma jm_bind_unary A X (_ : Encode A) B (_ : Encode B)
  m k (ψ : B → Prop)
:
  jm m (λ (a : A), jm (k #a) ψ) →
  jm (E := X) (bind m k) ψ.
Proof.
  eauto using jm_bind.
Qed.

(* A reasoning rule for [Par m1 m2 k z]. *)

(* We cannot give a reasoning rule for [par m1 m2] because its type is
   [micro (val * val)], not [micro val]. However, we can give a rule
   for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

Lemma jm_par `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  jm (E := X) m1 φ1 →
  jm m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → jm (k (#a1, #a2)) φ) →
  jm (E := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros Hm1 Hm2 Hentail. rewrite <- try_par.
  eapply purev_try_conseq.
  { eapply pure_par with (φ := λ v, jm (k v) φ); [ eauto | eauto |].
    simpl. intros v1 v2 ? ?. eauto with pure. }
  { intros v. tauto. }
Qed.

Lemma jm_par' `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  jm (E := X) m1 φ1 →
  jm m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → jm (continue k (#a1, #a2)) φ) →
  jm (E := Y) (Par m1 m2 k) φ.
Proof.
  intros. eapply pure_Par_conseq; eauto; firstorder subst; eauto.
Qed.

(* Sequentializations of previous lemmas, considering the LHS first *)

(* TODO: I do not seem to be able to use those, for example in pure_eval.v's
[pure_eval_pair] *)

Lemma jm_par_seq `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  jm (E := X) m1 (λ a1 : A1,
    jm m2 (λ a2 : A2, jm (k (#a1, #a2)) φ)) →
  jm (E := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros Hm1.
  apply pure_Par_vals_left.
  eapply (pure_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
  eapply (pure_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
  eauto.
Qed.

Lemma jm_par_seq' `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  jm (E := X) m1 (λ a1 : A1,
    jm m2 (λ a2 : A2, jm (continue k (#a1, #a2)) φ)) →
  jm (E := Y) (Par m1 m2 k) φ.
Proof.
  intros Hm1.
  apply pure_Par_vals_left.
  eapply (pure_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
  eapply (pure_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
  eauto.
Qed.

(* A reasoning rule for [choose]. *)

Lemma jm_choose `{Encode A} {X} m1 m2 (φ : A → Prop) :
  jm (E := X) m1 φ →
  jm m2 φ →
  jm (choose m1 m2) φ.
Proof.
  apply pure_choose.
Qed.

(* This is the reciprocal bind rule for [pure]. *)

(* Because [pure m ##_ ⊥] requires the result of [m] to lie in the image of the
   function [encode], and because this image cannot include every inhabitant
   of the type [val], we cannot expect that [pure (bind m k) ##φ ⊥] implies
   [pure m ##_ ⊥]. Thus, we can establish the reciprocal bind rule only under
   the side condition [pure m ##(λ a, True) ⊥], which means that the result of
   the computation [m] lies in the image of the function [encode] at type
   [A]. *)

Lemma invert_jm_bind `{Encode A, Encode B} X m k (φ : B → Prop) :
  jm (bind m k) φ →
  jm m (λ (a : A), True) →
  jm (E := X) m (λ (a : A), jm (k #a) φ).
Proof.
  intros Hmk%invert_pure_bind Hm.
  pose proof pure_binary_intersection _ Hmk Hm as I.
  eapply (pure_mono _ I); firstorder subst; eauto.
Qed.

(* That said, if we take the type [A] to be [val], then -- because [encode]
   at type [val] is the identity function -- this side condition becomes
   trivial, and we can prove a version of the rule that does not have this
   side condition. *)

Lemma invert_jm_bind' `{Encode B} {X} m k (φ : B → Prop) :
  jm (bind m k) φ →
  jm (E := X) m (λ (v : val), jm (k v) φ).
Proof.
  intros Hmk%invert_pure_bind.
  eapply pure_mono; eauto; intros; by apply jm_returns.
Qed.
