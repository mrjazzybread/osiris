From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.

(* This file defines what it means for a configuration to be safe. The
   structure of configurations does not matter; the definition of safety
   relies only on 1- recognizing results; and 2- the relation [step]. *)

(* -------------------------------------------------------------------------- *)

(* A configuration [c] is safe with respect to a postcondition [φ] if 1- [c]
   does not fail; and 2- if [c] is a result [(σ, Ret v)] then [φ σ v] holds.
   This is a partial correctness interpretation: divergence is permitted. *)

(* We first define what it means to be safe for [n] steps. *)

Fixpoint initially_safe {A} (n : nat) (c : config A) (φ : store → A → Prop) : Prop :=
  match n with
  | 0 =>
      (* Every configuration is safe for zero steps. *)
      True
  | S n =>
      (* [(σ, Ret v)] is safe with respect to [φ] if [φ σ v] holds. *)
      (∃ σ v, c = (σ, Ret v) ∧ φ σ v) ∨
      (
        (* A non-result [c] is safe for [n+1] steps if and only if
           1- it is not stuck, i.e., it can step; and
           2- every reduct [c'] of [c] is safe for [n] steps. *)
        can_step c ∧
        (∀ c', step c c' → initially_safe n c' φ)
      )
  end.

(* If, for every [n], a configuration is safe for [n] steps,
   then this configuration is safe. *)

Definition safe {A} (c : config A) (φ : store → A → Prop) :=
  ∀ n, initially_safe n c φ.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [initially_safe]. *)

(* A paraphrase lemma. *)

Lemma unfold_initially_safe_S {A n c} (φ : store → A → Prop) :
  initially_safe (S n) c φ =
  (
    (∃ σ v, c = (σ, Ret v) ∧ φ σ v) ∨
    (
      can_step c ∧
      (∀ c', step c c' → initially_safe n c' φ)
    )
  ).
Proof.
  reflexivity.
Qed.

(* A tactic that destructs a hypothesis whose form is the right-hand side
   of the above equation. *)

Ltac destruct_initially_safe_S H :=
  let Hcanstep := fresh "Hcanstep" in
  destruct H as [(? & ? & ? & ?) | (Hcanstep & H)];
  simplify_eq;
  try solve [
    exfalso; subst; destruct_step
  | exfalso; eauto with invert_can_step
  ].

(* -------------------------------------------------------------------------- *)

(* If [n1 ≤ n2] holds, then a configuration that is safe for [n2] steps is
   also safe for [n1] steps. *)

Lemma initially_safe_monotonic {A} (φ : store → A → Prop) :
  ∀ n1 n2 m,
  initially_safe n2 m φ →
  n1 ≤ n2 →
  initially_safe n1 m φ.
Proof.
  induction n1; simpl; intros n2 m Hsafe Hleq; [ tauto |].
  destruct n2 as [| n2 ]; [ lia |].
  rewrite unfold_initially_safe_S in Hsafe.
  intuition eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [φ] entails [φ'], then a computation that is safe with respect to [φ]
   is also safe with respect to [φ']. *)

Lemma initially_safe_covariant {A} (φ φ' : store → A → Prop) :
  (∀ σ a, φ σ a → φ' σ a) →
  ∀ n c,
  initially_safe n c φ →
  initially_safe n c φ'.
Proof.
  induction n; simpl; intros c Hsafe; [ tauto |].
  destruct Hsafe as [ Hsafe | Hsafe ]; [ left | right ].
  { destruct Hsafe as (? & ? & ? & ?). eauto. }
  { intuition eauto. }
Qed.

Lemma safe_covariant {A c} (φ φ' : store → A → Prop) :
  safe c φ →
  (∀ σ a, φ σ a → φ' σ a) →
  safe c φ'.
Proof.
  unfold safe. eauto using initially_safe_covariant.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas prove [initially_safe] assertions. *)

(* Every configuration is safe for 0 steps. *)

Lemma initially_safe_zero {A c} (φ : store → A → Prop) :
  initially_safe 0 c φ.
Proof.
  simpl. tauto.
Qed.

(* [(σ, ret a)] is safe for [n] steps, for every [n],
   provided [φ σ a] holds. *)

Lemma initially_safe_ret {A n σ a} (φ : store → A → Prop) :
  φ σ a →
  initially_safe n (σ, ret a) φ.
Proof.
  unfold safe. intros. destruct n; simpl; eauto.
Qed.

(* [c] is safe for [n+1] steps provided it is not stuck
   and every reduct [c'] of [c] is safe for [n] steps. *)

Lemma initially_safe_step {A n c} (φ : store → A → Prop) :
  can_step c →
  (∀ c', step c c' → initially_safe n c' φ) →
  initially_safe (S n) c φ.
Proof.
  intros. rewrite unfold_initially_safe_S. right. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are inversion lemmas. They extract information out
   of the judgement [initially_safe (S n) c φ] under a hypothesis about the
   observable behavior of the configuration [c]. They correspond to the three
   cases of the triplicity principle (with two subcases for answers). *)

Lemma invert_initially_safe_result {A n σ a} (φ : store → A → Prop) :
  initially_safe (S n) (σ, Ret a) φ →
  φ σ a.
Proof.
  simpl.
  intros [ H | H ].
  { destruct H as (v & ? & ? & ?). congruence. }
  { destruct H as (H & _). exfalso. eauto with invert_can_step. }
Qed.

Lemma invert_initially_safe_next {A n σ} (φ : store → A → Prop) :
  initially_safe (S n) (σ, Next) φ →
  False.
Proof.
  simpl.
  intros [ H | H ].
  { destruct H as (v & ? & ? & ?). congruence. }
  { destruct H as (H & _). exfalso. eauto with invert_can_step. }
Qed.

Lemma invert_initially_safe_step {A n c c'} (φ : store → A → Prop) :
  initially_safe (S n) c φ →
  step c c' →
  initially_safe n c' φ.
Proof.
  intros Hsafe Hstep.
  rewrite unfold_initially_safe_S in Hsafe.
  destruct_initially_safe_S Hsafe;
  eauto.
Qed.

Lemma invert_initially_safe_stuck {A n c} (φ : store → A → Prop) :
  initially_safe (S n) c φ →
  stuck c →
  False.
Proof.
  intros Hsafe Hstuck.
  rewrite unfold_initially_safe_S in Hsafe.
  destruct_initially_safe_S Hsafe.

  (* Case: [m] is a result. *)
  (* A result is not stuck: contradiction. *)
  { subst. eauto using invert_stuck_answer with is_answer. }

  (* Case: [m] can step. *)
  (* A term that can step is not stuck. Contradiction. *)
  { clear Hsafe. eauto using can_step_not_stuck. }

Qed.

(* -------------------------------------------------------------------------- *)

(* Two consequences of the previous lemma. *)

(* An iterated version of [invert_initially_safe_step]. *)

Lemma invert_initially_safe_steps k :
  ∀ {A n c c'} (φ : store → A → Prop),
  initially_safe (k + n) c φ →
  steps k c c' →
  initially_safe n c' φ.
Proof.
  induction k; intros A n c c' φ Hsafe Hsteps;
  inversion Hsteps; subst; clear Hsteps.
  (* Base case. *)
  { simpl in Hsafe. assumption. }
  (* Step case; subcase [StepsZero]. *)
  { eauto using initially_safe_monotonic with lia. }
  (* Step case; subcase [StepsSucc]. *)
  { eapply IHk; [| eassumption ].
    eauto using invert_initially_safe_step. }
Qed.

(* A consequence of [invert_initially_safe_stuck]. *)

Lemma invert_initially_safe_crash {A n σ} (φ : store → A → Prop) :
  initially_safe (S n) (σ, Crash) φ →
  False.
Proof.
  eauto using invert_initially_safe_stuck, stuck_Crash.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are inversion lemmas. They extract information out
   of the judgement [safe c φ] under a hypothesis about the observable
   behavior of the configuration [c]. *)

Lemma invert_safe_result {A a σ} (φ : store → A → Prop) :
  safe (σ, Ret a) φ →
  φ σ a.
Proof.
  unfold safe. intros Hsafe. specialize (Hsafe 1).
  eauto using (invert_initially_safe_result φ).
Qed.

Lemma invert_safe_next {A σ} (φ : store → A → Prop) :
  safe (σ, Next) φ →
  False.
Proof.
  unfold safe. intros Hsafe. specialize (Hsafe 1).
  eauto using invert_initially_safe_next.
Qed.

Lemma invert_safe_step {A c c'} (φ : store → A → Prop) :
  safe c φ →
  step c c' →
  safe c' φ.
Proof.
  unfold safe. eauto using invert_initially_safe_step.
Qed.

Lemma invert_safe_stuck {A c} (φ : store → A → Prop) :
  safe c φ →
  stuck c →
  False.
Proof.
  unfold safe. intros Hsafe Hstuck. specialize (Hsafe 1).
  eauto using invert_initially_safe_stuck.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas characterize the interaction of [safe] with the three
   kinds of configurations: results, configurations that can step, and stuck
   terms. *)

(* [(σ, ret a)] is safe iff [φ σ a] holds. *)

Lemma prove_safe_ret {A σ a} (φ : store → A → Prop) :
  φ σ a →
  safe (σ, ret a) φ.
Proof.
  unfold safe. eauto using initially_safe_ret.
Qed.

Lemma safe_ret {A σ a} (φ : store → A → Prop) :
  safe (σ, ret a) φ ↔
  φ σ a.
Proof.
  split; eauto using (invert_safe_result φ), prove_safe_ret.
Qed.

(* [(σ, Next)] is not safe. *)

Lemma safe_next {A σ} (φ : store → A → Prop) :
  safe (σ, Next) φ ↔
  False.
Proof.
  split; [ eauto using invert_safe_next | tauto ].
Qed.

(* Provided [c] is not stuck,
   [c] is safe iff
   every reduct [c'] of [c] is safe. *)

Lemma safe_step {A c} (φ : store → A → Prop) :
  can_step c →
  safe c φ ↔
  (∀ c', step c c' → safe c' φ).
Proof.
  intros Hcanstep. split.
  { eauto using invert_safe_step. }
  { unfold safe. intros Hsafe.
    destruct n; eauto using initially_safe_zero, initially_safe_step. }
Qed.

(* A stuck configuration is not safe. *)

Lemma safe_stuck {A c} (φ : store → A → Prop) :
  stuck c →
  safe c φ ↔
  False.
Proof.
  split; [| tauto ]. eauto using invert_safe_stuck.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas describe the interaction of safety and [bind],
   and culminate in a proof that [safety] commutes with [bind]. *)

(* If [m1] is safe for [n1] steps and (then, for every result [a])
      [m2 a] is safe for [n2] steps
   then [bind m1 m2] is safe for [min n1 n2] steps.

   In other words,
   if [m1] is safe for [n] steps and (then, for every result [a])
      [m2 a] is safe for [n] steps
   then [bind m1 m2] is safe for [n] steps.

   One cannot expect to obtain safety for [n1+n2] steps. To see this,
   consider the case where [n1] is zero. With no hypothesis at all
   about [m1], one would have to prove that [m2 a] is safe for [n2]
   steps. *)

Lemma initially_safe_bind_aux_1 {A B} (m2 : A → free B) :
  ∀ n (m1 : free A) σ (φ : store → B → Prop),
  initially_safe n (σ, m1) (λ σ' a, initially_safe n (σ', m2 a) φ) →
  initially_safe n (σ, bind m1 m2) φ.
Proof.
  induction n; [tauto |].
  intros m1 σ φ Hsafe.
  destruct_initially_safe_S Hsafe.

  (* Case: [m1] is [ret _]. *)
  { clear IHn. assumption. }

  (* Case: [m1] can step. *)
  { rewrite unfold_initially_safe_S. right. split.
    (* Subgoal: [bind m1 m2] can step as well. *)
    { eauto using can_step_bind. }
    (* Subgoal: every reduct of [bind m1 m2] is safe for [n] steps. *)
    intros [σ' m'] Hstep.
    (* Because [m1] can step, a reduct of [bind m1 m2] must be of the form
       [bind m'1 m2], where [m'1] is a reduct of [m1]. *)
    assert (Hnoret: ¬ is_answer m1) by eauto using can_step_not_answer.
    specialize (invert_step_bind' Hstep Hnoret).
    clear Hstep Hcanstep Hnoret.
    intros (m'1 & Hstep & ?). subst.
    specialize (Hsafe _ Hstep). clear Hstep.
    (* The goal follows from the induction hypothesis and from the fact that
       [initially_safe] is covariant in its postcondition and monotonic
       in its step index. *)
    eapply IHn; clear IHn.
    eapply initially_safe_covariant; [| exact Hsafe ].
    clear Hsafe σ σ' m1 m'1.
    intros σ' a Hm2a.
    eapply initially_safe_monotonic; [ exact Hm2a |].
    lia. }

Qed.

(* Conversely, if [bind m1 m2] is safe for [n1 + n2] steps
   then [m1] is safe for [n1] steps and (then, for every result [a])
        [m2 a] is safe for [n2] steps. *)

Lemma initially_safe_bind_aux_2 {A B} (m2 : A → free B) :
  ∀ n1 n2 (m1 : free A) σ (φ : store → B → Prop),
  initially_safe (n1 + n2) (σ, bind m1 m2) φ →
  initially_safe n1 (σ, m1) (λ σ' a, initially_safe n2 (σ', m2 a) φ).
Proof.
  induction n1; intros n2 m1 σ φ; [ simpl; tauto |].
  intros Hsafe.
  rewrite unfold_initially_safe_S.
  (* Proceed by cases on [m1]. Three cases arise. *)
  triplicity σ m1 Hm1; [ clear IHn1 | | clear IHn1 ].

  (* Case: [m1] is an answer. *)
  { destruct_answer.
    (* Sub-case: [m1] is [ret a]. *)
    { left. eauto using initially_safe_monotonic with lia. }
    (* Sub-case: [m1] is [Next]. *)
    { exfalso. rewrite bind_next in Hsafe.
      eauto using invert_initially_safe_next. }
  }
  (* Case: [m1] can step. *)
  { right. split; [ eauto |].
    intros [σ'1 m'1] Hstep.
    apply IHn1. clear IHn1.
    eapply invert_initially_safe_step.
    + eauto.
    + eauto using step_bind. }

  (* Case: [m1] fails. *)
  { exfalso. eauto using invert_initially_safe_stuck, stuck_bind. }

Qed.

(* The intersection rule of Hoare logic: if for every [x] the computation
   [m] admits the postcondition [φ x], then [m] admits the postcondition
   [∀ x, φ x]. *)

Lemma initially_safe_intersection {A X} {_ : Inhabited X}
  (φ : X → store → A → Prop) :
  ∀ n c,
  (∀ x, initially_safe n c (φ x)) →
  initially_safe n c (λ σ a, ∀ x, φ x σ a).
Proof.
  induction n; [ simpl; tauto |]; intros [σ m] Hsafe.
  rewrite unfold_initially_safe_S.
  (* Proceed by cases on [m]. Three cases arise. *)
  triplicity σ m Hm; [ clear IHn | | clear IHn ].

  (* Case: [m] is an answer. *)
  { destruct_answer.
    (* Sub-case: [m] is [ret a]. *)
    { left. eexists _, _. split; [ eauto |].
      intros x. specialize (Hsafe x).
      destruct_initially_safe_S Hsafe.
      congruence. }
    (* Sub-case: [m] is [Next]. *)
    { exfalso. specialize (Hsafe inhabitant).
      eauto using invert_initially_safe_next. }
  }
  (* Case: [m] can step. *)
  { right. split; [ eauto |].
    intros m' Hstep.
    eapply IHn; clear IHn.
    intros x. specialize (Hsafe x).
    destruct_initially_safe_S Hsafe.
    eauto. }

  (* Case: [m1] is stuck. *)
  (* The fact that the type [X] is inhabited is exploited. *)
  { exfalso.
    specialize (Hsafe inhabitant).
    eauto using invert_initially_safe_stuck. }

Qed.

(* A sequence [bind m1 m2] is safe if and only if
   [m1] is safe and (then, for every result [a])
   [m2 a] is safe. *)

Lemma safe_bind {A B} m1 σ (m2 : A → free B) (φ : store → B → Prop) :
  safe (σ, bind m1 m2) φ ↔
  safe (σ, m1) (λ σ' a, safe (σ', m2 a) φ).
Proof.
  unfold safe.
  split; intros Hsafe.
  (* This implication corresponds to the completeness of the program logic.
     It is interesting to note that the intersection rule is used here. *)
  { intros n1.
    eapply initially_safe_intersection. intros n2.
    eapply initially_safe_bind_aux_2.
    eapply Hsafe. }
  (* This implication corresponds to the soundness of the program logic. *)
  { intros n.
    eapply initially_safe_bind_aux_1.
    eapply initially_safe_covariant; [| eauto ]; intros ? a Hm2a.
    eapply Hm2a. }
Qed.

Lemma prove_safe_bind {A B} m1 σ (m2 : A → free B) (φ : store → B → Prop) :
  safe (σ, m1) (λ σ' a, safe (σ', m2 a) φ) →
  safe (σ, bind m1 m2) φ.
Proof.
  rewrite safe_bind. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The natural next step would be to prove a rule for parallel composition,
   but it is not easy to provide such a rule for a Hoare logic where the
   state is monolithic. So, this exercise stops here. *)
