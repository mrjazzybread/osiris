Require Import lang base free eval step steps.

(* This file defines what it means for a computation (in the free monad) to
   be safe. The structure of computations does not matter; the definition
   of safety relies only on 1- recognizing results; and 2- the relation
   [step]. *)

(* -------------------------------------------------------------------------- *)

(* A computation [m] is safe with respect to a postcondition [φ] if
   1- [m] does not fail; and 2- if [m] produces a result [v] then [φ v]
   holds. This is a partial correctness interpretation: divergence is
   permitted. *)

(* We first define what it means to be safe for [n] steps. *)

Fixpoint initially_safe {A} (n : nat) (m : free A) (φ : A → Prop) : Prop :=
  match n with
  | 0 =>
      (* Every computation is safe for zero steps. *)
      True
  | S n =>
      (* A result [Ret v] is safe with respect to [φ] if [φ v] holds. *)
      (∃ v, m = Ret v ∧ φ v) ∨
      (
        (* A non-result [m] is safe for [n+1] steps if and only if
           1- it is not stuck, i.e., it can step; and
           2- every reduct [m'] of [m] is safe for [n] steps. *)
        can_step m ∧
        (∀ m', step m m' → initially_safe n m' φ)
      )
  end.

(* If, for every [n], a computation is safe for [n] steps,
   then this computation is safe. *)

Definition safe {A} (m : free A) (φ : A → Prop) :=
  ∀ n, initially_safe n m φ.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [initially_safe]. *)

(* A paraphrase lemma. *)

Lemma unfold_initially_safe_S {A} (n : nat) (m : free A) (φ : A → Prop) :
  initially_safe (S n) m φ =
  (
    (∃ v, m = Ret v ∧ φ v) ∨
    (
      can_step m ∧
      (∀ m', step m m' → initially_safe n m' φ)
    )
  ).
Proof.
  reflexivity.
Qed.

(* A tactic that destructs a hypothesis whose form is the right-hand side
   of the above equation. *)

Ltac destruct_initially_safe_S H :=
  let Hcanstep := fresh "Hcanstep" in
  destruct H as [(? & ? & ?) | (Hcanstep & H)];
  try solve [
    false; subst; destruct_step
  | false; eauto with invert_can_step
  ].

(* -------------------------------------------------------------------------- *)

(* If [n1 ≤ n2] holds, then a computation that is safe for [n2] steps is
   also safe for [n1] steps. *)

Lemma initially_safe_monotonic {A} (φ : A → Prop) :
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

Lemma initially_safe_covariant {A} (φ φ' : A → Prop) :
  (∀ a, φ a → φ' a) →
  ∀ n m,
  initially_safe n m φ →
  initially_safe n m φ'.
Proof.
  induction n; simpl; intros m Hsafe; [ tauto |].
  destruct Hsafe as [ Hsafe | Hsafe ]; [ left | right ].
  { destruct Hsafe as (? & ? & ?). eauto. }
  { intuition eauto. }
Qed.

Lemma safe_covariant {A} (m : free A) (φ φ' : A → Prop) :
  safe m φ →
  (∀ a, φ a → φ' a) →
  safe m φ'.
Proof.
  unfold safe. eauto using initially_safe_covariant.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas prove [initially_safe] assertions. *)

(* Every term is safe for 0 steps. *)

Lemma initially_safe_zero {A} (m : free A) (φ : A → Prop) :
  initially_safe 0 m φ.
Proof.
  simpl. tauto.
Qed.

(* [ret a] is safe for [n] steps, for every [n], provided [φ a] holds. *)

Lemma initially_safe_ret {A} n (a : A) (φ : A → Prop) :
  φ a →
  initially_safe n (ret a) φ.
Proof.
  unfold safe. intros. destruct n; simpl; eauto.
Qed.

(* [m] is safe for [n+1] steps provided it is not stuck
   and every reduct [m'] of [m] is safe for [n] steps. *)

Lemma initially_safe_step {A} n m (φ : A → Prop) :
  can_step m →
  (∀ m', step m m' → initially_safe n m' φ) →
  initially_safe (S n) m φ.
Proof.
  intros. rewrite unfold_initially_safe_S. right. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are inversion lemmas. They extract information out
   of the judgement [initially_safe (S n) m φ] under a hypothesis about the
   observable behavior of the computation [m]. They correspond to the three
   cases of the triplicity principle (with two subcases for answers). *)

Lemma invert_initially_safe_result {A} {n} {a} (φ : A → Prop) :
  initially_safe (S n) (Ret a) φ →
  φ a.
Proof.
  simpl.
  intros [ H | H ].
  { destruct H as (v & ? & ?). congruence. }
  { destruct H as (H & _). false. eauto with invert_can_step. }
Qed.

Lemma invert_initially_safe_next {A} {n} (φ : A → Prop) :
  initially_safe (S n) Next φ →
  False.
Proof.
  simpl.
  intros [ H | H ].
  { destruct H as (v & ? & ?). congruence. }
  { destruct H as (H & _). false. eauto with invert_can_step. }
Qed.

Lemma invert_initially_safe_step {A} {n} m m' {φ : A → Prop} :
  initially_safe (S n) m φ →
  step m m' →
  initially_safe n m' φ.
Proof.
  intros Hsafe Hstep.
  rewrite unfold_initially_safe_S in Hsafe.
  destruct_initially_safe_S Hsafe.
  eauto.
Qed.

Lemma invert_initially_safe_stuck {A} {n} {m : free A} {φ : A → Prop} :
  initially_safe (S n) m φ →
  stuck m →
  False.
Proof.
  intros Hsafe Hstuck.
  rewrite unfold_initially_safe_S in Hsafe.
  destruct_initially_safe_S Hsafe.

  (* Case: [m] is a result. *)
  (* A result is not stuck: contradiction. *)
  { subst m. eauto using invert_stuck_answer with is_answer. }

  (* Case: [m] can step. *)
  (* A term that can step is not stuck. Contradiction. *)
  { clear Hsafe. eauto using can_step_not_stuck. }

Qed.

(* -------------------------------------------------------------------------- *)

(* Two consequences of the previous lemma. *)

(* An iterated version of [invert_initially_safe_step]. *)

Lemma invert_initially_safe_steps k :
  ∀ {A} n m m' {φ : A → Prop},
  initially_safe (k + n) m φ →
  steps k m m' →
  initially_safe n m' φ.
Proof.
  induction k; intros A n m m' φ Hsafe Hsteps;
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

Lemma invert_initially_safe_fail {A} {n} {φ : A → Prop} :
  initially_safe (S n) Fail φ →
  False.
Proof.
  eauto using invert_initially_safe_stuck, stuck_Fail.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are inversion lemmas. They extract information out
   of the judgement [safe m φ] under a hypothesis about the observable
   behavior of the computation [m]. *)

Lemma invert_safe_result {A} {a} (φ : A → Prop) :
  safe (Ret a) φ →
  φ a.
Proof.
  unfold safe. intros Hsafe. specialize (Hsafe 1).
  eauto using (invert_initially_safe_result φ).
Qed.

Lemma invert_safe_next {A} (φ : A → Prop) :
  safe Next φ →
  False.
Proof.
  unfold safe. intros Hsafe. specialize (Hsafe 1).
  eauto using invert_initially_safe_next.
Qed.

Lemma invert_safe_step {A} m m' {φ : A → Prop} :
  safe m φ →
  step m m' →
  safe m' φ.
Proof.
  unfold safe. eauto using invert_initially_safe_step.
Qed.

Lemma invert_safe_stuck {A} {m : free A} {φ : A → Prop} :
  safe m φ →
  stuck m →
  False.
Proof.
  unfold safe. intros Hsafe Hstuck. specialize (Hsafe 1).
  eauto using invert_initially_safe_stuck.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas characterize the interaction of [safe] with the three
   kinds of computations: results, terms that can reduce, and stuck terms. *)

(* [ret a] is safe iff [φ a] holds. *)

Lemma prove_safe_ret {A} (a : A) (φ : A → Prop) :
  φ a →
  safe (ret a) φ.
Proof.
  unfold safe. eauto using initially_safe_ret.
Qed.

Lemma safe_ret {A} (a : A) (φ : A → Prop) :
  safe (ret a) φ ↔
  φ a.
Proof.
  split; eauto using (invert_safe_result φ), prove_safe_ret.
Qed.

(* [Next] is not safe. *)

Lemma safe_next {A} (φ : A → Prop) :
  safe Next φ ↔
  False.
Proof.
  split; [ eauto using invert_safe_next | tauto ].
Qed.

(* Provided [m] is not stuck,
   [m] is safe iff
   every reduct [m'] of [m] is safe. *)

Lemma safe_step {A} m (φ : A → Prop) :
  can_step m →
  safe m φ ↔
  (∀ m', step m m' → safe m' φ).
Proof.
  intros Hcanstep. split.
  { eauto using invert_safe_step. }
  { unfold safe. intros Hsafe.
    destruct n; eauto using initially_safe_zero, initially_safe_step. }
Qed.

(* A stuck term is not safe. *)

Lemma safe_stuck {A} m (φ : A → Prop) :
  stuck m →
  safe m φ ↔
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
  ∀ n (m1 : free A) (φ : B → Prop),
  initially_safe n m1 (λ a, initially_safe n (m2 a) φ) →
  initially_safe n (bind m1 m2) φ.
Proof.
  induction n; [tauto |]. intros m1 φ Hsafe.
  rewrite unfold_initially_safe_S in Hsafe.
  destruct_initially_safe_S Hsafe.

  (* Case: [m1] is [ret _]. *)
  { subst m1. clear IHn. rewrite bind_ret. assumption. }

  (* Case: [m1] can step. *)
  { rewrite unfold_initially_safe_S. right. split.
    (* Subgoal: [bind m1 m2] can step as well. *)
    { eauto using can_step_bind. }
    (* Subgoal: every reduct of [bind m1 m2] is safe for [n] steps. *)
    intros m' Hstep.
    (* Because [m1] can step, a reduct of [bind m1 m2] must be of the form
       [bind m'1 m2], where [m'1] is a reduct of [m1]. *)
    assert (Hnoret: ¬ is_answer m1) by eauto using can_step_not_answer.
    specialize (invert_step_bind' _ _ _ Hstep Hnoret).
    clear Hstep Hcanstep Hnoret.
    intros (m'1 & Hstep & ?). subst m'.
    specialize (Hsafe _ Hstep). clear Hstep.
    (* The goal follows from the induction hypothesis and from the fact that
       [initially_safe] is covariant in its postcondition and monotonic
       in its step index. *)
    eapply IHn; clear IHn.
    eapply initially_safe_covariant; [| exact Hsafe ]; clear Hsafe.
    intros a Hm2a.
    eapply initially_safe_monotonic; [ exact Hm2a |].
    lia. }

Qed.

(* Conversely, if [bind m1 m2] is safe for [n1 + n2] steps
   then [m1] is safe for [n1] steps and (then, for every result [a])
        [m2 a] is safe for [n2] steps. *)

Lemma initially_safe_bind_aux_2 {A B} (m2 : A → free B) :
  ∀ n1 n2 (m1 : free A)  (φ : B → Prop),
  initially_safe (n1 + n2) (bind m1 m2) φ →
  initially_safe n1 m1 (λ a, initially_safe n2 (m2 a) φ).
Proof.
  induction n1; intros n2 m1 φ; [ simpl; tauto |].
  intros Hsafe.
  rewrite unfold_initially_safe_S.
  (* Proceed by cases on [m1]. Three cases arise. *)
  triplicity m1 Hm1; [ clear IHn1 | | clear IHn1 ].

  (* Case: [m1] is an answer. *)
  { destruct_answer.
    (* Sub-case: [m1] is [ret a]. *)
    { eauto using initially_safe_monotonic with lia. }
    (* Sub-case: [m1] is [Next]. *)
    { false. rewrite bind_next in Hsafe.
      eauto using invert_initially_safe_next. }
  }
  (* Case: [m1] can step. *)
  { right. split; [ eauto |].
    intros m'1 Hstep.
    apply IHn1. clear IHn1.
    eapply invert_initially_safe_step.
    + eauto.
    + eauto using step_bind. }

  (* Case: [m1] fails. *)
  { false. eauto using invert_initially_safe_stuck, stuck_bind. }

Qed.

(* The intersection rule of Hoare logic: if for every [x] the computation
   [m] admits the postcondition [φ x], then [m] admits the postcondition
   [∀ x, φ x]. *)

Lemma initially_safe_intersection {A X} {_ : Inhabited X} (φ : X → A → Prop) :
  ∀ n m,
  (∀ x, initially_safe n m (φ x)) →
  initially_safe n m (λ a, ∀ x, φ x a).
Proof.
  induction n; [ simpl; tauto |]; intros m Hsafe.
  rewrite unfold_initially_safe_S.
  (* Proceed by cases on [m]. Three cases arise. *)
  triplicity m Hm; [ clear IHn | | clear IHn ].

  (* Case: [m] is an answer. *)
  { destruct_answer.
    (* Sub-case: [m] is [ret a]. *)
    { left. eexists. split; [ eauto |].
      intros x. specialize (Hsafe x).
      destruct_initially_safe_S Hsafe.
      congruence. }
    (* Sub-case: [m] is [Next]. *)
    { false. specialize (Hsafe inhabitant).
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
  { false.
    specialize (Hsafe inhabitant).
    eauto using invert_initially_safe_stuck. }

Qed.

(* A sequence [bind m1 m2] is safe if and only if
   [m1] is safe and (then, for every result [a])
   [m2 a] is safe. *)

Lemma safe_bind {A B} (m1 : free A) (m2 : A → free B) (φ : B → Prop) :
  safe (bind m1 m2) φ ↔ safe m1 (λ a, safe (m2 a) φ).
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
    eapply initially_safe_covariant; [| eauto ]; intros a Hm2a.
    eapply Hm2a. }
Qed.

Lemma prove_safe_bind {A B} (m1 : free A) (m2 : A → free B) (φ : B → Prop) :
  safe m1 (λ a, safe (m2 a) φ) →
  safe (bind m1 m2) φ.
Proof.
  rewrite safe_bind. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Special cases of [safe_step]. *)

Lemma prove_safe_stop {A} η e (k : val → free A) φ :
  safe (eval η e) (λ v, safe (k v) φ) →
  safe (Stop Eval (η, e) k) φ.
Proof.
  intros.
  rewrite safe_step by eauto with step.
  intros. destruct_step.
  rewrite safe_bind.
  assumption.
Qed.

Lemma prove_safe_flip {A} (k : bool → free A) φ :
  (∀ b, safe (k b) φ) →
  safe (Flip k) φ.
Proof.
  intros.
  rewrite safe_step by eauto with step.
  intros. destruct_step. eauto.
Qed.

Lemma prove_safe_par_ret_ret {A1 A2 A} a1 a2 (k : A1 * A2 → free A) ko φ :
  safe (k (a1, a2)) φ →
  safe (Par (Ret a1) (Ret a2) k ko) φ.
Proof.
  intros.
  rewrite safe_step by eauto with step.
  intros. repeat destruct_step. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas describe the interaction of safety and [par]. *)

(* Some of these lemmas concern the special case where [ko] is [next].
   It may be desirable to remove this hypothesis and to state more general
   lemmas. These more general statements may need to use the more general
   judgement [safe2]. TODO *)

(* If [m1] and [m2] are (independently) safe for [n] steps
   and if the continuation [k],
   applied to the pair [(v1, v2)],
   is safe for [n] steps,
   then [Par m1 m2 k ko] is safe for [n] steps. *)

Lemma prove_initially_safe_par :
  ∀ n {A1 A2 A} m1 m2 (k : A1 * A2 → free A) ko φ φ1 φ2,
  initially_safe n m1 φ1 →
  initially_safe n m2 φ2 →
  (∀ v1 v2, φ1 v1 → φ2 v2 → initially_safe n (k (v1, v2)) φ) →
  initially_safe n (Par m1 m2 k ko) φ.
Proof.
  induction n; [ simpl; tauto |].
  intros A1 A2 A m1 m2 k ko φ φ1 φ2.
  intros Hm1 Hm2 Hk.
  rewrite unfold_initially_safe_S. right.
  split; [ eauto with step |].
  intros m' Hstep. destruct_step.
  (* Case: [StepParRetRet]. *)
  { apply invert_initially_safe_result in Hm1, Hm2.
    eauto using initially_safe_monotonic with lia. }
  (* Case: [StepParFailLeft]. *)
  { eapply invert_initially_safe_fail in Hm1. tauto. }
  (* Case: [StepParFailRight]. *)
  { eapply invert_initially_safe_fail in Hm2. tauto. }
  (* Case: [StepParNextLeft]. *)
  { eapply invert_initially_safe_next in Hm1. tauto. }
  (* Case: [StepParNextRight]. *)
  { eapply invert_initially_safe_next in Hm2. tauto. }
  (* Case: [StepParLeft]. *)
  { eapply IHn;
    eauto using invert_initially_safe_step,
                initially_safe_monotonic with lia. }
  (* Case: [StepParRight]. *)
  { eapply IHn;
    eauto using invert_initially_safe_step,
                initially_safe_monotonic with lia. }
Qed.

(* If [m1] and [m2] are (independently) safe
   and if the continuation [k],
   applied to the pair [(v1, v2)],
   is safe,
   then [Par m1 m2 k ko] is safe. *)

Lemma prove_safe_par {A1 A2 A} m1 m2 (k : A1 * A2 → free A) ko φ :
  ∀ φ1 φ2,
  safe m1 φ1 →
  safe m2 φ2 →
  (∀ v1 v2, φ1 v1 → φ2 v2 → safe (k (v1, v2)) φ) →
  safe (Par m1 m2 k ko) φ.
Proof.
  unfold safe. eauto using prove_initially_safe_par.
Qed.

(* If [par m1 m2] is safe for [n + 1] steps
   then [m1] is safe for [n] steps.

   As the postcondition [φ1], we use the most precise postcondition,
   which describes exactly the set of values that [m1] can produce
   in at most [n] steps. *)

Lemma invert_initially_safe_par_left :
  ∀ n {A1 A2 A} m1 m2 (k : A1 * A2 → free A) φ,
  initially_safe (S n) (Par m1 m2 k next) φ →
  let φ1 := produces n m1 in
  initially_safe n m1 φ1.
Proof.
  induction n; [ simpl; tauto |].
  intros A1 A2 A m1 m2 k φ Hsafe φ1.

  triplicity m1 Hm1.

  (* Case: [m1] is an answer. *)
  { destruct_answer.
    { eapply initially_safe_ret. subst φ1. eauto with steps. }
    { false.
      (* The hypothesis [ko = next] is used in this subcase. *)
      eapply invert_initially_safe_step in Hsafe; [| eauto with step ].
      eapply invert_initially_safe_next in Hsafe.
      tauto. }
  }

  (* Case: [m1] can take a step. *)
  { rewrite unfold_initially_safe_S. right. split; [ eauto |]. clear Hm1.
    intros m'1 Hstep. subst φ1.
    eapply initially_safe_covariant with (φ := produces n m'1).
    { eauto with steps. }
    eapply IHn.
    eapply invert_initially_safe_step; [ exact Hsafe |].
    eauto with step. }

  (* Case: [m1] is stuck. *)
  { apply only_fail_is_stuck in Hm1. subst m1. false.
    eapply invert_initially_safe_step in Hsafe; [| eauto with step ].
    eapply invert_initially_safe_fail in Hsafe.
    tauto. }

Qed.

(* A symmetric copy of the previous lemma. *)

Lemma invert_initially_safe_par_right :
  ∀ n {A1 A2 A} m1 m2 (k : A1 * A2 → free A) φ,
  initially_safe (S n) (Par m1 m2 k next) φ →
  let φ2 := produces n m2 in
  initially_safe n m2 φ2.
Proof.
  induction n; [ simpl; tauto |].
  intros A1 A2 A m1 m2 k φ Hsafe φ2.

  triplicity m2 Hm2.

  (* Case: [m2] is an answer. *)
  { destruct_answer.
    { eapply initially_safe_ret. subst φ2. eauto with steps. }
    { false.
      (* The hypothesis [ko = next] is used in this subcase. *)
      eapply invert_initially_safe_step in Hsafe; [| eauto with step ].
      eapply invert_initially_safe_next in Hsafe.
      tauto. }
  }

  (* Case: [m2] can take a step. *)
  { rewrite unfold_initially_safe_S. right. split; [ eauto |]. clear Hm2.
    intros m'2 Hstep. subst φ2.
    eapply initially_safe_covariant with (φ := produces n m'2).
    { eauto with steps. }
    eapply IHn.
    eapply invert_initially_safe_step; [ exact Hsafe |].
    eauto with step. }

  (* Case: [m2] is stuck. *)
  { apply only_fail_is_stuck in Hm2. subst m2. false.
    eapply invert_initially_safe_step in Hsafe; [| eauto with step ].
    eapply invert_initially_safe_fail in Hsafe.
    tauto. }

Qed.

(* If [(Par m1 m2 k ko)] is safe for [n1 + n2 + 1 + n] steps
   and if [v1] and [v2] are values that [m1] and [m2] can produce
   in [n1] and [n2] steps, respectively,
   then the application of the continuation [k]
   to the pair [(v1, v2)]
   is safe for [n] steps. *)

Lemma invert_initially_safe_par_continuation :
  ∀ n n1 n2 {A1 A2 A} m1 m2 (k : A1 * A2 → free A) ko φ,
  initially_safe (n1 + n2 + 1 + n) (Par m1 m2 k ko) φ →
  let φ1 := produces n1 m1 in
  let φ2 := produces n2 m2 in
  ∀ v1 v2, φ1 v1 → φ2 v2 → initially_safe n (k (v1, v2)) φ.
Proof.
  intros n n1 n2 A1 A2 A m1 m2 k ko φ.
  intros Hsafe φ1 φ2.
  intros v1 v2 Hv1 Hv2.
  eapply invert_initially_safe_steps; [ exact Hsafe |].
  subst φ1 φ2. unfold produces in Hv1, Hv2.
  eapply steps_transitive; [ eapply steps_transitive |].
  { eapply steps_par_left. exact Hv1. }
  { eapply steps_par_right. exact Hv2. }
  { eapply one_step. eauto with step. }
Qed.

(* If [Par m1 m2 k next] is safe
   then [m1] and [m2] are (independently) safe
   and the continuation [k],
   applied to a pair [(v1, v2)],
   where [v1] and [v2] are values that can be produced by [m1] and [m2],
   is safe. *)

Lemma invert_safe_par {A1 A2 A} m1 m2 (k : A1 * A2 → free A) φ :
  safe (Par m1 m2 k next) φ →
  ∃ φ1 φ2,
  safe m1 φ1 ∧
  safe m2 φ2 ∧
  (∀ v1 v2, φ1 v1 → φ2 v2 → safe (k (v1, v2)) φ).
Proof.
  unfold safe. intros Hsafe.
  exists (λ a1, ∃ n, produces n m1 a1).
  exists (λ a2, ∃ n, produces n m2 a2).
  repeat split.
  { intros n. specialize (Hsafe (S n)).
    apply invert_initially_safe_par_left in Hsafe.
    eauto using initially_safe_covariant. }
  { intros n. specialize (Hsafe (S n)).
    apply invert_initially_safe_par_right in Hsafe.
    eauto using initially_safe_covariant. }
  { intros v1 v2 (n1 & Hv1) (n2 & Hv2).
    eauto using invert_initially_safe_par_continuation. }
Qed.

(* Thus, we have proved the following equivalence law,
   which characterizes the safety of a [Par] construct,
   in the case where [ko] is [next]. *)

Lemma safe_par {A1 A2 A} m1 m2 (k : A1 * A2 → free A) φ :
  safe (Par m1 m2 k next) φ ↔
  ∃ φ1 φ2,
  safe m1 φ1 ∧
  safe m2 φ2 ∧
  (∀ v1 v2, φ1 v1 → φ2 v2 → safe (k (v1, v2)) φ).
Proof.
  split.
  { eauto using invert_safe_par. }
  { intros (φ1 & φ2 & ? & ? & ?). eauto using prove_safe_par. }
Qed.

(* Auxiliary lemmas. *)

Local Lemma descend_forall {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) →
  (∀ a, P a) ↔ (∀ a, Q a).
Proof.
  firstorder.
Qed.

Local Lemma descend_exists {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) →
  (∃ a, P a) ↔ (∃ a, Q a).
Proof.
  firstorder.
Qed.

Local Lemma descend_conj (P Q P' Q' : Prop) :
  (P ↔ P') →
  (Q ↔ Q') →
  (P ∧ Q) ↔ (P' ∧ Q').
Proof.
  tauto.
Qed.

(* In the case of the binary combinator [par m1 m2],
   the above equivalence law can be simplified as follows. *)

Lemma safe_par' {A1 A2} (m1 : free A1) (m2 : free A2)
  (φ : A1 * A2 → Prop) :
  safe (par m1 m2) φ ↔
  ∃ φ1 φ2,
  safe m1 φ1 ∧
  safe m2 φ2 ∧
  (∀ v1 v2, φ1 v1 → φ2 v2 → φ (v1, v2)).
Proof.
  unfold par. rewrite safe_par.
  apply descend_exists; intro φ1.
  apply descend_exists; intro φ2.
  apply descend_conj; [ tauto |].
  apply descend_conj; [ tauto |].
  apply descend_forall; intro v1.
  apply descend_forall; intro v2.
  apply descend_forall; intro Hv1.
  apply descend_forall; intro Hv2.
  rewrite safe_ret. tauto.
Qed.

(* If one side is a result, then the above equivalence laws can be
   further simplified as follows. *)

Lemma prove_safe_Par_ret_left {A1 A2 A} a1 m2
  (k : A1 * A2 → free A)
  (φ : A → Prop) :
  safe m2 (λ v2, safe (k (a1, v2)) φ) →
  safe (Par (Ret a1) m2 k next) φ.
Proof.
  intros Hsafe.
  rewrite safe_par.
  exists (λ v1, v1 = a1).
  exists (λ v2, safe (k (a1, v2)) φ).
  rewrite safe_ret.
  repeat split.
  + assumption.
  + intros. subst. assumption.
Qed.

Lemma safe_par_ret_left {A1 A2} (a1 : A1) (m2 : free A2)
  (φ : A1 * A2 → Prop) :
  safe (par (ret a1) m2) φ ↔
  safe m2 (λ v2, φ (a1, v2)).
Proof.
  split.
  (* One implication. *)
  { rewrite safe_par'.
    intros (φ1 & φ2 & Ha1 & Hm2 & Hk).
    rewrite safe_ret in Ha1.
    eauto using safe_covariant. }
  (* The reverse implication. *)
  { intros Hm2. eapply prove_safe_Par_ret_left.
    eapply safe_covariant; [ eassumption |].
    intros a2. simpl. rewrite safe_ret. tauto. }
Qed.

(* Symmetric copies of the previous lemmas. *)

Lemma prove_safe_Par_ret_right {A1 A2 A} m1 a2
  (k : A1 * A2 → free A)
  (φ : A → Prop) :
  safe m1 (λ v1, safe (k (v1, a2)) φ) →
  safe (Par m1 (Ret a2) k next) φ.
Proof.
  intros Hsafe.
  rewrite safe_par.
  exists (λ v1, safe (k (v1, a2)) φ).
  exists (λ v2, v2 = a2).
  rewrite safe_ret.
  repeat split.
  + assumption.
  + intros. subst. assumption.
Qed.

Lemma safe_par_ret_right {A1 A2} (m1 : free A1) (a2 : A2)
  (φ : A1 * A2 → Prop) :
  safe (par m1 (ret a2)) φ ↔
  safe m1 (λ v1, φ (v1, a2)).
Proof.
  split.
  (* One implication. *)
  { rewrite safe_par'.
    intros (φ1 & φ2 & Hm1 & Ha2 & Hk).
    rewrite safe_ret in Ha2.
    eauto using safe_covariant. }
  (* The reverse implication. *)
  { intros Hm1. eapply prove_safe_Par_ret_right.
    eapply safe_covariant; [ eassumption |].
    intros a1. simpl. rewrite safe_ret. tauto. }
Qed.
