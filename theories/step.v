Require Import Coq.Program.Equality.
Require Import lang monads free eval.

(* This file defines an ample-step semantics, that is, a reduction semantics
   of the form [step m m'] where [m] and [m'] are computations in the [free]
   monad. *)

(* The definition of the relation [step] interprets a [Stop] event as a
   request for a recursive invocation of the evaluator. *)

(* Working directly with the relation [step] removes the need to transport
   computations from the free monad into some other monad. (This was the
   job of the function [handle] defined in handle.v.) *)

(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Next] cannot step. They are answers. *)

(* [Fail] cannot step. It represents a crash. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always be reduced. This preserves the property that the only stuck term
   is [Fail]. There is a lot of non-determinism in these reduction rules:
   e.g., [Par Fail Next _ _] can reduce to either [Fail] or [Next]. *)

Inductive step {A} : free A → free A → Prop :=

  (* [Stop η e k] steps to an invocation of [eval η e] followed
     with the continuation [k]. *)
  | StepStop :
      ∀ η e k,
      step
        (Stop η e k)
        (bind (eval η e) k)

  (* [Flip k] steps to an application of the continuation [k] to
     either [false] or [true]. *)
  | StepFlip :
      ∀ b k,
      step
        (Flip k)
        (k b)

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2} (v1 : A1) (v2 : A2) k ko,
      step
        (Par (Ret v1) (Ret v2) k ko)
        (k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParFailLeft :
      ∀ {A1 A2} (m2 : free A2) k ko,
      step
        (Par (@Fail A1) m2 k ko)
        Fail
  | StepParFailRight :
      ∀ {A1 A2} (m1 : free A1) k ko,
      step
        (Par m1 (@Fail A2) k ko)
        Fail

  (* If a soft failure on either side is detected, then
     the failure continuation [n] can be invoked. *)
  | StepParNextLeft :
      ∀ {A1 A2} (m2 : free A2) k ko,
      step
        (Par (@Next A1) m2 k ko)
        (ko())
  | StepParNextRight :
      ∀ {A1 A2} (m1 : free A1) k ko,
      step
        (Par m1 (@Next A2) k ko)
        (ko())

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2} (m1 m'1 : free A1) (m2 : free A2) k ko,
      step m1 m'1 →
      step
        (Par m1 m2 k ko)
        (Par m'1 m2 k ko)
  | StepParRight :
      ∀ {A1 A2} (m1 : free A1) {m2 m'2 : free A2} k ko,
      step m2 m'2 →
      step
        (Par m1 m2 k ko)
        (Par m1 m'2 k ko)

.

Global Hint Constructors step : step.

Ltac destruct_step :=
  match goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

(* -------------------------------------------------------------------------- *)

(* A term [m] is an answer iff it is of the form [Ret a] or [Next]. *)

Definition is_answer {A} (m : free A) :=
  match m with
  | Ret a => True
  | Next  => True
  | _     => False
  end.

Lemma is_answer_ret {A} (a : A) :
  is_answer (Ret a).
Proof.
  simpl. eauto.
Qed.

Lemma is_answer_next {A} :
  is_answer (@Next A).
Proof.
  simpl. eauto.
Qed.

Global Hint Resolve is_answer_ret is_answer_next : is_answer.

Ltac destruct_answer :=
  match goal with h: is_answer ?m |- _ =>
    destruct m; try solve [ false; tauto ]; clear h
  end.

(* -------------------------------------------------------------------------- *)

(* [m] can step if there exists [m'] such that [m] steps to [m']. *)

Definition can_step {A} (m : free A) :=
  ∃ m', step m m'.

Global Hint Unfold can_step : step.

(* -------------------------------------------------------------------------- *)

(* A term that is not an answer and that is unable to step is stuck. *)

Definition stuck {A} (m : free A) :=
  ¬ is_answer m ∧
  (∀ m', ¬ step m m').

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* This auxiliary lemma is useful when a constructor of the relation [step]
   cannot be applied directly. *)

Lemma step_eq {A} (m1 m2 m2' : free A) :
  step m1 m2 →
  m2 = m2' →
  step m1 m2'.
Proof.
  intros. subst. assumption.
Qed.

(* [Stop] can step. *)

Lemma can_step_stop {A} η e (k : val → free A) :
  can_step (Stop η e k).
Proof.
  unfold can_step. eauto with step.
Qed.

Global Hint Resolve can_step_stop : step.

(* [Flip] can step. *)

Lemma can_step_flip {A} (k : bool → free A) :
  can_step (Flip k).
Proof.
  unfold can_step. eauto using (StepFlip false).
Qed.

Global Hint Resolve can_step_flip : step.

(* The following auxiliary lemma is used in the proof of [can_step_par],
   which establishes a stronger result. *)

Local Lemma can_step_under_par {A1 A2 A} m1 m2 (k : A1 * A2 → free A) ko :
  can_step m1 ∨ can_step m2 →
  can_step (Par m1 m2 k ko).
Proof.
  unfold can_step.
  intros [ (m'1 & ?) | (m'2 & ?) ]; eauto with step.
Qed.

(* [Par] can step. *)

Lemma can_step_par :
  ∀ {A} (m : free A) {A1 A2} m1 m2 (k : A1 * A2 → free A) ko,
  m = Par m1 m2 k ko →
  can_step m.
Proof.
  induction m; try solve [ congruence ].
  intros A'1 A'2 m'1 m'2 k' ko' Heq.
  (* The hypothesis [Heq] is tricky because it involves different types
     on either side. Fortunately, [dependent destruction] is capable
     of deconstructing it for us. Phew! *)
  dependent destruction Heq.
  destruct m'1; eauto using can_step_under_par with step.
  destruct m'2; eauto using can_step_under_par with step.
Qed.

Global Hint Resolve can_step_par : step.

(* Stepping in the left-hand side of [bind] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_bind {A B} (m m' : free A) (f : A → free B) :
  step m m' →
  step (bind m f) (bind m' f).
Proof.
  inversion 1; subst;
  rewrite ?bind_stop, ?bind_flip, ?bind_par, ?bind_fail;
  rewrite ?bind_associativity by typeclasses eauto;
  eauto using step_eq with step.
Qed.

(* Conversely, if [bind m f] takes a step, then this must be either because
   [m] itself takes a step (under a context) or because [m] is [ret a] and
   the computation [f a] takes a step. *)

(* See also [invert_step_bind'] further on. *)

Lemma invert_step_bind {A B} (m : free A) (f : A → free B) (b' : free B) :
  step (bind m f) b' →
  (∃ m', step m m' ∧ b' = bind m' f) ∨
  (∃ a, m = Ret a ∧ step (f a) b').
Proof.
  destruct m;
  rewrite ?bind_ret, ?bind_stop, ?bind_flip, ?bind_par, ?bind_fail;
  intro;
  try solve [
    (* Case: [Ret] *)
    right; eauto
  | (* Every other case: *)
    left; destruct_step; eauto with step
  ].
  (* Case: [Stop]. *)
  (* This case does not quite fall into the general case above,
     so we deal with it by hand. *)
  { left. destruct_step.
    eexists. split; [ constructor |].
    rewrite bind_associativity by typeclasses eauto.
    reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [is_answer]. *)

Lemma is_answer_bind {A B} (m : free A) (f : A → free B) :
  ¬ is_answer m →
  ¬ is_answer (bind m f).
Proof.
  destruct m; simpl; tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [can_step]. *)

(* [Ret a] cannot step. *)

Lemma invert_can_step_Ret {A} (a : A) :
  can_step (Ret a) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

(* [Fail] cannot step. *)

Lemma invert_can_step_Fail {A} :
  can_step (Fail : free A) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

(* [Next] cannot step. *)

Lemma invert_can_step_Next {A} :
  can_step (Next : free A) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Fail
  invert_can_step_Next
: invert_can_step.

(* Stepping in the left-hand side of [bind] is permitted. *)

Lemma can_step_bind {A B} (m : free A) (f : A → free B) :
  can_step m →
  can_step (bind m f).
Proof.
  unfold can_step. intros (m' & Hstep). eauto using step_bind.
Qed.

(* A term that can step is not an answer. *)

Lemma can_step_not_answer {A} (m : free A) :
  can_step m →
  ¬ is_answer m.
Proof.
  intros.
  destruct m; try solve [ false; eauto with invert_can_step | simpl; tauto ].
Qed.

(* As a special case of [invert_step_bind], if it is known that [m] is not an
   answer, and if [bind m f] takes a step, then this must be because [m] takes
   a step (under a context). In other words, reduction under a context is
   mandatory: no other reduction is possible. *)

Lemma invert_step_bind' {A B} (m : free A) (f : A → free B) (b' : free B) :
  step (bind m f) b' →
  ¬ is_answer m →
  (∃ m', step m m' ∧ b' = bind m' f).
Proof.
  intros Hstep Hnoret.
  specialize (invert_step_bind _ _ _ Hstep).
  intros [ ? | (a & ? & ?) ].
  { eauto. }
  { subst m. false. simpl in Hnoret. tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [stuck]. *)

(* An answer is not stuck. *)

Lemma invert_stuck_answer {A} (m : free A) :
  is_answer m →
  stuck m →
  False.
Proof.
  unfold stuck. tauto.
Qed.

(* A term that can step is not stuck. *)

Lemma can_step_not_stuck {A} (m : free A) :
  can_step m →
  stuck m →
  False.
Proof.
  unfold can_step, stuck.
  intros (m' & Hstep).
  intros (_ & Hnostep).
  eapply Hnostep. exact Hstep.
Qed.

(* [Fail] is stuck. *)

Lemma stuck_Fail {A} :
  stuck (Fail : free A).
Proof.
  unfold stuck. split. eauto. inversion 1.
Qed.

(* The only stuck term is [Fail]. *)

Lemma only_fail_is_stuck {A} (m : free A) :
  stuck m →
  m = Fail.
Proof.
  intros.
  destruct m; try solve [
    reflexivity
  | false;
    eauto using invert_stuck_answer, can_step_not_stuck with step is_answer
  ].
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B} (m : free A) (f : A → free B) :
  stuck m →
  stuck (bind m f).
Proof.
  intros.
  assert (m = Fail) by eauto using only_fail_is_stuck.
  subst m. rewrite bind_fail.
  eauto using stuck_Fail.
Qed.

(* -------------------------------------------------------------------------- *)

(* A triplicity principle. *)

(* This principle allows case analyses with three cases, as follows:
   either [m] is a result, or [m] can step, or [m] is stuck. *)

Lemma triplicity {A} (m : free A) :
  is_answer m ∨
  can_step m ∨
  stuck m.
Proof.
  destruct m; eauto using stuck_Fail with step is_answer.
Qed.

Ltac triplicity m H :=
  destruct (triplicity m) as [ H | [ H | H ]].
