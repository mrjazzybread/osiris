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

Definition step {A} (m : free A) (m' : free A) : Prop :=
  match m with
  | Ret a =>
      (* [Ret a] cannot step. It is a result. *)
      False
  | Fail =>
      (* [Fail] cannot step. It represents a crash. *)
      False
  | Next =>
      (* [Next] cannot step, and is not expected to occur at the top level
         of a computation anyway. *)
      False
  | Stop η e k =>
      (* [Stop η e k] steps to an invocation of [eval η e] followed
         with the continuation [k]. *)
      m' = bind (eval η e) k
  | Flip k =>
      (* [Flip k] steps to an application of the continuation [k] to
         either [false] or [true]. *)
      m' = k false ∨ m' = k true
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

(* -------------------------------------------------------------------------- *)

(* A term that is not an answer and that is unable to step is stuck. *)

Definition stuck {A} (m : free A) :=
  ¬ is_answer m ∧
  (∀ m', ¬ step m m').

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step]. *)

(* [Stop η e k] steps to [bind (eval η e) k],
   and steps to no other term. *)

Lemma step_stop {A} η e k (m' : free A) :
  step (Stop η e k) m' =
  (m' = bind (eval η e) k).
Proof.
  reflexivity.
Qed.

Lemma prove_step_stop {A} η e (k : val → free A) :
  step (Stop η e k) (bind (eval η e) k).
Proof.
  reflexivity.
Qed.

Lemma can_step_stop {A} η e (k : val → free A) :
  can_step (Stop η e k).
Proof.
  unfold can_step. eauto using prove_step_stop.
Qed.

Global Hint Resolve prove_step_stop can_step_stop : step.

Lemma step_flip {A} k (m' : free A) :
  step (Flip k) m' =
  (m' = k false ∨ m' = k true).
Proof.
  reflexivity.
Qed.

Lemma prove_step_flip {A} b (k : bool → free A) :
  step (Flip k) (k b).
Proof.
  destruct b; simpl; tauto.
Qed.

Lemma can_step_flip {A} (k : bool → free A) :
  can_step (Flip k).
Proof.
  unfold can_step. eauto using (prove_step_flip false).
Qed.

Global Hint Resolve prove_step_flip can_step_flip : step.

(* Stepping in the left-hand side of [bind] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_bind {A B} (m m' : free A) (f : A → free B) :
  step m m' →
  step (bind m f) (bind m' f).
Proof.
  destruct m; try (simpl; tauto).
  (* Case: [Stop]. *)
  { rewrite bind_stop.
    rewrite !step_stop. intros. subst m'.
    rewrite bind_bind.
    reflexivity. }
  (* Case: [Flip]. *)
  { rewrite bind_flip.
    rewrite !step_flip. intros [|]; subst m'; eauto. }
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
  destruct m; try (simpl; tauto).
  (* Case: [Ret]. *)
  { rewrite bind_of_return by typeclasses eauto. right. eauto. }
  (* Case: [Stop]. *)
  { rewrite bind_stop, step_stop. intros. subst b'.
    left. eexists. split.
    + rewrite step_stop. reflexivity.
    + rewrite bind_bind. reflexivity. }
  (* Case: [Flip]. *)
  { rewrite bind_flip, step_flip. intros [|]; subst b';
      left; eauto with step. }
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
  intros (m' & Hstep). simpl in Hstep. tauto.
Qed.

(* [Fail] cannot step. *)

Lemma invert_can_step_Fail {A} :
  can_step (Fail : free A) →
  False.
Proof.
  intros (m' & Hstep). simpl in Hstep. tauto.
Qed.

(* [Next] cannot step. *)

Lemma invert_can_step_Next {A} :
  can_step (Next : free A) →
  False.
Proof.
  intros (m' & Hstep). simpl in Hstep. tauto.
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

(* [Fail] is stuck. *)

Lemma stuck_Fail {A} :
  stuck (Fail : free A).
Proof.
  unfold stuck. eauto using invert_can_step_Fail.
Qed.

(* [Stop] is not stuck. *)

Lemma invert_stuck_stop {A} η e k :
  stuck (Stop η e k : free A) →
  False.
Proof.
  intros (_ & H).
  unfold not in H. eapply H.
  eauto with step.
Qed.

(* [Flip] is not stuck. *)

Lemma invert_stuck_flip {A} k :
  stuck (Flip k : free A) →
  False.
Proof.
  intros (_ & H).
  unfold not in H. eapply H.
  eauto using (prove_step_flip false).
Qed.

(* The only stuck term is [Fail]. *)

Lemma only_fail_is_stuck {A} (m : free A) :
  stuck m →
  m = Fail.
Proof.
  intros.
  destruct m; try solve [
    false;
    eauto using invert_stuck_answer, invert_stuck_stop, invert_stuck_flip
      with is_answer
  | reflexivity
  ].
Qed.

(* A term that can step is not stuck. *)

Lemma can_step_not_stuck {A} (m : free A) :
  can_step m →
  stuck m →
  False.
Proof.
  (* We keep this generic proof, although a simpler proof would be
     possible based on the fact that only [Fail] is stuck. *)
  unfold can_step, stuck.
  intros (m' & Hstep).
  intros (_ & Hnostep).
  eapply Hnostep. exact Hstep.
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B} (m : free A) (f : A → free B) :
  stuck m →
  stuck (bind m f).
Proof.
  (* We keep this generic proof, although a simpler proof would be
     possible based on the fact that only [Fail] is stuck. *)
  unfold stuck.
  intros (Hnoret & Hnostep).
  split.
  { eauto using is_answer_bind. }
  { intros b' Hstep.
    specialize (invert_step_bind' _ _ _ Hstep Hnoret); clear Hstep.
    firstorder. }
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
