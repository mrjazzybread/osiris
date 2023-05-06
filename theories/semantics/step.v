From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.
From iris.prelude Require Import prelude options.

(* This file defines an ample-step semantics, that is, a reduction semantics
   of the form [step c c'] where [c] and [c'] are pairs of a computation in
   the [free] monad and a store. *)

(* The definition of the relation [step] provides an interpretation of system
   calls, that is, of [Stop] events. For example, a [Stop CEval] event is
   interpreted as a request for a recursive invocation of the evaluator. *)

(* -------------------------------------------------------------------------- *)

(* A store is a finite map of locations to values. *)

Definition store : Type :=
  gmap loc val.

Implicit Type σ : store.

(* A configuration is a pair of a computation and a store. *)

Definition config (A : Type) : Type :=
  store * free A.

(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Next] cannot step. They are answers. *)

(* [Crash] cannot step. It represents a crash. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always step. This preserves the property that the only stuck term
   is [Crash]. There is a lot of non-determinism in these reduction rules:
   e.g., [Par Crash Next _ _] can step to either [Crash] or [Next]. *)

Inductive step {A} : config A → config A → Prop :=

  (* [Stop CEval (η, e) k] steps to an invocation of [eval η e] followed
     with the continuation [k]. Thus, from the user's perspective, the
     computation [stop CEval (η, e)] behaves just like [eval η e]. *)
  | StepEval :
      ∀ σ η e k,
      step
        (σ, Stop CEval (η, e) k)
        (σ, bind (eval η e) k)

  (* [stop (η, x, i1, i2, e) k] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ η x i1 i2 e k,
      step
        (σ, Stop CLoop (η, x, i1, i2, e) k)
        (σ, bind (loop η x i1 i2 e) k)

  (* [stop CFlip ()] returns either [false] or [true]. *)
  | StepFlip :
      ∀ b σ x k,
      step
        (σ, Stop CFlip x k)
        (σ, k b)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with [v], and returns this location. *)
  | StepAlloc :
      ∀ σ v l k,
      σ !! l = None →
      step
        (σ, Stop CAlloc v k)
        (<[l := v]>σ, k l)

  (* If the location [l] exists, then [stop CLoad l] looks up its content
     in the heap and returns it. *)
  | StepLoadSuccess :
      ∀ σ l k v,
      σ !! l = Some v →
      step
        (σ, Stop CLoad l k)
        (σ, k v)

  (* If the location [l] does not exist, then [stop CLoad l] fails. This
     ensures that [Crash] is the only stuck term. *)
  | StepLoadFailure :
      ∀ σ l k,
      σ !! l = None →
      step
        (σ, Stop CLoad l k)
        (σ, Crash)

  (* If the location [l] exists, then [stop CStore (l, v')] overwrites
     its content with [v'] and returns a unit value. *)
  | StepStoreSuccess :
      ∀ σ l v' v k,
      σ !! l = Some v →
      step
        (σ, Stop CStore (l, v') k)
        (<[ l := v' ]> σ, k tt)

  (* If the location [l] does not exist, then [stop CStore (l, v')] fails.
     This ensures that [Crash] is the only stuck term. *)
  | StepStoreFailure :
      ∀ σ l v' k,
      σ !! l = None →
      step
        (σ, Stop CStore (l, v') k)
        (σ, Crash)

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2} σ (v1 : A1) (v2 : A2) k ko,
      step
        (σ, Par (Ret v1) (Ret v2) k ko)
        (σ, k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParCrashLeft :
      ∀ {A1 A2} σ m2 (k : A1 * A2 → free A) ko,
      step
        (σ, Par Crash m2 k ko)
        (σ, Crash)

  | StepParCrashRight :
      ∀ {A1 A2} σ m1 (k : A1 * A2 → free A) ko,
      step
        (σ, Par m1 Crash k ko)
        (σ, Crash)

  (* If a soft failure on either side is detected, then
     the failure continuation [n] can be invoked. *)
  | StepParNextLeft :
      ∀ {A1 A2} σ m2(k : A1 * A2 → free A) ko,
      step
        (σ, Par Next m2 k ko)
        (σ, ko())

  | StepParNextRight :
      ∀ {A1 A2} σ m1 (k : A1 * A2 → free A) ko,
      step
        (σ, Par m1 Next k ko)
        (σ, ko())

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2} σ σ' (m1 m'1 : free A1) (m2 : free A2) k ko,
      step (σ, m1) (σ', m'1) →
      step
        (σ, Par m1 m2 k ko)
        (σ', Par m'1 m2 k ko)

  | StepParRight :
      ∀ {A1 A2} σ σ' (m1 : free A1) {m2 m'2 : free A2} k ko,
      step (σ, m2) (σ', m'2) →
      step
        (σ, Par m1 m2 k ko)
        (σ', Par m1 m'2 k ko)
.

Global Hint Constructors step : step.

Ltac destruct_step :=
  try match goal with h: step (?σ, Stop ?c ?x ?k) ?m' |- _ =>
    remember x
  end;
  match goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

(* This auxiliary lemma is useful when a constructor of the relation [step]
   cannot be applied directly. *)

Lemma step_up_to_eq {A} (c : config A) σ e e' :
  step c (σ, e) →
  e = e' →
  step c (σ, e').
Proof.
  congruence.
Qed.

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
  is_answer (Next : free A).
Proof.
  simpl. eauto.
Qed.

Global Hint Resolve is_answer_ret is_answer_next : is_answer.

Ltac destruct_answer :=
  match goal with h: is_answer ?m |- _ =>
    destruct m; try solve [ exfalso; tauto ]; clear h
  end.

(* -------------------------------------------------------------------------- *)

(* [c] can step if there exists [c'] such that [c] steps to [c']. *)

Definition can_step {A} (c : config A) :=
  ∃ c', step c c'.

Global Hint Unfold can_step : step.

Ltac destruct_can_step :=
  match goal with
  | h: can_step _ |- _ =>
      destruct h as ((? & ?) & ?)
  end.

(* -------------------------------------------------------------------------- *)

(* A configuration that is not an answer and that is unable to step is
   stuck. *)

Definition stuck {A} (c : config A) :=
  let '(σ, m) := c in
  ¬ is_answer m ∧
  ∀ σ' m', ¬ step (σ, m) (σ', m').

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* [Stop] can step. *)

Lemma can_step_stop {A X Y} σ (c : code X Y) x (k : Y → free A) :
  can_step (σ, Stop c x k).
Proof.
  destruct c; repeat destruct x as (x & ?);
  (* For reading and writing, we must reason by cases, according to
     whether the location [l] is or is not in the domain of [σ]. *)
  try match goal with σ: store, l: loc |- _ => case_eq (σ !! l) end;
  (* All cases except allocation are handled here: *)
  eauto using (StepFlip false), step_up_to_eq with step.
  (* In the case of allocation, we must exhibit an address [l]
     that is not in the domain of [σ]. *)
  { set (l := fresh_loc (dom σ)).
    pose proof (Hl := fresh_loc_fresh (dom σ)).
    rewrite not_elem_of_dom in Hl.
    eauto using step_up_to_eq with step. }
Qed.

Global Hint Resolve can_step_stop : step.

(* The following auxiliary lemma is used in the proof of [can_step_par],
   which establishes a stronger result. *)

Local Lemma can_step_under_par {A1 A2 A} σ m1 m2 (k : A1 * A2 → free A) ko :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step (σ, Par m1 m2 k ko).
Proof.
  intros [|]; destruct_can_step; eauto using step_up_to_eq with step.
Qed.

(* [Par] can step. *)

Lemma can_step_par :
  ∀ {A} (m : free A) {A1 A2} σ m1 m2 (k : A1 * A2 → free A) ko,
  m = Par m1 m2 k ko →
  can_step (σ, m).
Proof.
  induction m; try solve [ congruence ].
  intros A'1 A'2 σ' m'1 m'2 k' ko' Heq.
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

Lemma step_bind {A B} σ σ' (m m' : free A) (f : A → free B) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  inversion 1; subst;
  rewrite ?bind_stop ?bind_par ?bind_crash ?bind_bind;
  eauto using step_up_to_eq with step.
Qed.

(* Conversely, if [bind m f] takes a step, then this must be either because
   [m] itself takes a step (under a context) or because [m] is [ret a] and
   the computation [f a] takes a step. *)

(* See also [invert_step_bind'] further on. *)

Local Hint Extern 1 (_ = _) => rewrite bind_bind : bind_bind.

Lemma invert_step_bind {A B} σ (m : free A) (f : A → free B) c' :
  step (σ, bind m f) c' →
  (∃ m' σ', step (σ, m) (σ', m') ∧ c' = (σ', bind m' f)) ∨
  (∃ a, m = Ret a ∧ step (σ, f a) c').
Proof.
  destruct m;
  rewrite ?bind_ret ?bind_stop ?bind_par ?bind_crash;
  intro;
  try solve [
    (* Case: [Ret] *)
    right; eauto
  | (* Every other case: *)
    left; destruct_step; eauto with step bind_bind
  ].
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

Lemma invert_can_step_Ret {A} σ (a : A) :
  can_step (σ, Ret a) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

(* [Crash] cannot step. *)

Lemma invert_can_step_Crash {A} σ :
  can_step (σ, Crash : free A) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

(* [Next] cannot step. *)

Lemma invert_can_step_Next {A} σ :
  can_step (σ, Next : free A) →
  False.
Proof.
  intros (m' & ?). destruct_step.
Qed.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Crash
  invert_can_step_Next
: invert_can_step.

(* [Par (ret _) (ret _) _ _] can step in only one way.  *)

Lemma step_par_ret_ret {A1 A2 A3} v v' (k: A1 * A2 -> free A3) ko σ σ' m' :
  step (σ, Par (ret v) (ret v') k ko) (σ', m') →
  σ' = σ ∧
  m' = k (v, v').
Proof.
  intros. destruct_step; try solve [ exfalso; destruct_step ].
  split; congruence.
Qed.

(* If the location [l] exists in the store, then [stop CStore (l, v')]
   can step in only one way. *)

Lemma invert_step_store {A} σ l v' v k σ' (m' : free A) :
  σ !! l = Some v →
  step (σ, Stop CStore (l, v') k) (σ', m') →
  σ' = <[ l := v' ]> σ ∧
  m' = k ().
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* If the location [l] exists in the store, then [stop CLoad l]
   can step in only one way. *)

Lemma invert_step_load {A} σ σ' l v k (m' : free A) :
  σ !! l = Some v →
  step (σ, Stop CLoad l k) (σ', m') →
  σ' = σ ∧
  m' = k v.
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* Stepping in the left-hand side of [bind] is permitted. *)

Lemma can_step_bind {A B} σ (m : free A) (f : A → free B) :
  can_step (σ, m) →
  can_step (σ, bind m f).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_bind.
Qed.

(* A term that can step is not an answer. *)

Lemma can_step_not_answer {A} σ (m : free A) :
  can_step (σ, m) →
  ¬ is_answer m.
Proof.
  intros.
  destruct m; try solve [ exfalso; eauto with invert_can_step | simpl; tauto ].
Qed.

(* As a special case of [invert_step_bind], if it is known that [m] is not an
   answer, and if [bind m f] takes a step, then this must be because [m] takes
   a step (under a context). In other words, reduction under a context is
   mandatory: no other reduction is possible. *)

Lemma invert_step_bind' {A B} σ (m : free A) (f : A → free B) c' :
  step (σ, bind m f) c' →
  ¬ is_answer m →
  (∃ σ' m', step (σ, m) (σ', m') ∧ c' = (σ', bind m' f)).
Proof.
  intros Hstep Hnoret.
  apply invert_step_bind in Hstep.
  destruct Hstep as [ (? & ? & Hstep & ->) | ( ? & -> & ? )].
  { eauto. }
  { exfalso. by apply Hnoret. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [stuck]. *)

(* An answer is not stuck. *)

Lemma invert_stuck_answer {A} (m : free A) σ :
  is_answer m →
  stuck (σ, m) →
  False.
Proof.
  unfold stuck. tauto.
Qed.

(* A term that can step is not stuck. *)

Lemma can_step_not_stuck {A} (m : free A) σ :
  can_step (σ, m) →
  stuck (σ, m) →
  False.
Proof.
  unfold can_step, stuck.
  intros ([] & Hstep).
  intros (_ & Hnostep).
  eapply Hnostep. exact Hstep.
Qed.

(* [Crash] is stuck. *)

Lemma stuck_Crash {A} σ :
  stuck (σ, Crash : free A).
Proof.
  unfold stuck. split.
  { eauto. }
  { inversion 1. }
Qed.

(* The only stuck term is [Crash]. *)

Lemma only_crash_is_stuck {A} σ (m : free A) :
  stuck (σ, m) →
  m = Crash.
Proof.
  intros.
  destruct m; try solve [
    reflexivity
  | exfalso;
    eauto using invert_stuck_answer, can_step_not_stuck with step is_answer
  ].
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B} σ (m : free A) (f : A → free B) :
  stuck (σ, m) →
  stuck (σ, bind m f).
Proof.
  intros.
  assert (m = Crash) by eauto using only_crash_is_stuck.
  subst m. rewrite bind_crash.
  eauto using stuck_Crash.
Qed.

(* -------------------------------------------------------------------------- *)

(* A triplicity principle. *)

(* This principle allows case analyses with three cases, as follows:
   either [m] is a result, or [m] can step, or [m] is stuck. *)

Lemma triplicity {A} σ (m : free A) :
  is_answer m ∨
  can_step (σ, m) ∨
  stuck (σ, m).
Proof.
  destruct m; eauto using stuck_Crash with step is_answer.
Qed.

Ltac triplicity σ m H :=
  destruct (triplicity σ m) as [ H | [ H | H ]].
