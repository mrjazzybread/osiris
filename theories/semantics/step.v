From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.
From iris.prelude Require Import prelude options.

(* This file defines an ample-step semantics, that is, a reduction semantics
   of the form [step m m'] where [m] and [m'] are computations in the [free]
   monad. *)

(* The definition of the relation [step] interprets a [Stop] event as a
   request for a recursive invocation of the evaluator. *)

(* Working directly with the relation [step] removes the need to transport
   computations from the free monad into some other monad. (This was the
   job of the function [handle] defined in handle.v.) *)

(* -------------------------------------------------------------------------- *)

(* A store is a finite map of locations to values. *)

Definition store : Type := gmap loc val.

Implicit Type σ : store.

(* The state of an execution is a term of type [free A] taken together with
   a store. *)
Definition state (A : Type) : Type := store * free A.


(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Next] cannot step. They are answers. *)

(* [Crash] cannot step. It represents a crash. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always be reduced. This preserves the property that the only stuck term
   is [Crash]. There is a lot of non-determinism in these reduction rules:
   e.g., [Par Crash Next _ _] can reduce to either [Crash] or [Next]. *)

Inductive step {A} : state A → state A → Prop :=

  (* [Stop CEval (η, e) k] steps to an invocation of [eval η e] followed
     with the continuation [k]. Thus, from the user's perspective, the
     computation [stop CEval (η, e)] behaves just like [eval η e]. *)
  (* Isolating an explicit equality [p = (η, e)] seems necessary to work
     around a bug or limitation (?) in [dependent destruction]. *)
  | StepEval :
      ∀ σ p η e k,
      p = (η, e) →
      step
        (σ, Stop CEval p k)
        (σ, bind (eval η e) k)

  (* [stop (η, x, i1, i2, e) k] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ p η x i1 i2 e k,
      p = (η, x, i1, i2, e) →
      step
        (σ, Stop CLoop p k)
        (σ, bind (loop η x i1 i2 e) k)

  (* [stop CFlip ()] returns either [false] or [true]. *)
  | StepFlip :
      ∀ σ b x k,
      step
        (σ, Stop CFlip x k)
        (σ, k b)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with [v], and returns this location. *)
  | StepAlloc :
      ∀ σ v l k,
      l ∉ dom σ →
      let σ' := <[l := v]>σ in
      step
        (σ, Stop CAlloc v k)
        (σ', k l)

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
      l ∉ dom σ →
      step
        (σ, Stop CLoad l k)
        (σ, Crash)

  (* If the location [l] exists, then [stop CStore (l, v')] overwrites
     its content with [v'] and returns a unit value. *)
  | StepStoreSuccess :
      ∀ σ l v' v k,
      σ !! l = Some v →
      let '(σ', m') := (<[ l := v' ]> σ, k tt) in
      step (σ, Stop CStore (l, v') k) (σ', m')

  (* The [Store] code fails if the updated location is unknown to the store
     This case is required to ensure that [Crash] is the only stuck term. *)
  | StepStoreFailure :
      ∀ σ (l: loc) v k (H: l ∉ dom σ),
      step
        (σ, Stop CStore (l, v) k)
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
  match goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

Lemma step_up_to_eq {A} (c : state A) σ e e' :
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

(* [m] can step if there exists [m'] such that [m] steps to [m']. *)

Definition can_step {A} (s : state A) :=
  ∃ s', step s s'.

Global Hint Unfold can_step : step.

(* -------------------------------------------------------------------------- *)

(* A term that is not an answer and that is unable to step is stuck. *)

Definition stuck {A} (m : state A) :=
  match m with
  | (σ, m) => ¬ is_answer m ∧
             (∀ m' σ', ¬ step (σ, m) (σ', m'))
  end.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* This auxiliary lemma is useful when a constructor of the relation [step]
   cannot be applied directly. *)

Lemma step_eq {A} (s1 s2 s2' : state A) :
  step s1 s2 →
  s2 = s2' →
  step s1 s2'.
Proof.
  intros. subst. assumption.
Qed.

(* [Stop] can step. *)

Lemma can_step_stop {A X Y} (σ: store) (c : code X Y) x (k : Y → free A) :
  can_step (σ, Stop c x k).
Proof.
  eauto with step.
  destruct c; repeat destruct x as (x & ?).
  - exists (σ, bind (eval x e) k). eauto with step.
  - exists (σ, bind (loop x v i0 i e) k). eauto with step.
  - exists (σ, k false). eauto with step.
  - set (l := fresh_loc (dom σ)).
    exists (<[l:=x]> σ, k l).
    eauto using fresh_loc_fresh with step.
  - (* TODO: destruct the "belongs to" predicate instead of the result of
     *       lookup. *)
    destruct (σ !! x) eqn:E.
    + (* The load operation will succeed. *)
      exists (σ, k v). eauto with step.
    + (* The load operation will fail. *)
      exists (σ, Crash). constructor.
      apply not_elem_of_dom_2, E.
  - (* TODO: ditto. *)
    destruct (σ !! x) eqn:E.
    + (* The store operation will succeed. *)
      eexists _. eauto with step.
    + (* The store operation will fail. *)
      apply not_elem_of_dom_2 in E.
      exists (σ, Crash).
      eauto with step.
Qed.

Global Hint Resolve can_step_stop : step.

(* The following auxiliary lemma is used in the proof of [can_step_par],
   which establishes a stronger result. *)

Local Lemma can_step_under_par {A1 A2 A} σ m1 m2 (k : A1 * A2 → free A) ko :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step (σ, Par m1 m2 k ko).
Proof.
  unfold can_step. eauto with step.
  intros[[[]]|[[]]]. (* TODO: restore the previous proof relying on [eauto]. *)
  - eexists _. apply StepParLeft, H.
  - eexists _. apply StepParRight, H.
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

Lemma step_bind {A B} (σ σ': store) (m m' : free A) (f : A → free B) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  inversion 1; subst;
  rewrite ?bind_stop ?bind_par ?bind_crash ?bind_bind;
  eauto using step_up_to_eq with step.
  (* TODO: improve the way this case is handled: *)
  - econstructor. eauto.
Qed.

(* Conversely, if [bind m f] takes a step, then this must be either because
   [m] itself takes a step (under a context) or because [m] is [ret a] and
   the computation [f a] takes a step. *)

(* See also [invert_step_bind'] further on. *)

Local Hint Extern 1 (_ = _) => rewrite bind_bind : bind_bind.

Lemma invert_step_bind {A B} σ (m : free A) (f : A → free B) (b' : state B) :
  step (σ, bind m f) b' →
  (∃ m' σ', step (σ, m) (σ', m') ∧ b' = (σ', bind m' f)) ∨
  (∃ a, m = Ret a ∧ step (σ, f a) b').
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
  (* TODO: unify the Stop case with the others. *)
  left; destruct_step; unshelve eauto with step bind_bind.
  - pose proof (StepEval σ (η, e) η e k (eq_refl (η, e))) as Hstep.
    exists (bind (eval η e) k), σ.
    split; eauto with step bind_bind.
  - pose proof (StepLoop σ (η, x0, i1, i2, e) η x0 i1 i2 e k (eq_refl _)).
    exists (bind (loop η x0 i1 i2 e) k), σ.
    split; eauto with step bind_bind.
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

(* [Par (ret _) (ret _) _ _] can only reduce in one way.  *)
Lemma step_par_ret_ret {A1 A2 A3} {v: A1} {v': A2} {k: A1 * A2 -> free A3} {ko σ m}:
  step (σ, Par (ret v) (ret v') k ko) m → m = (σ, k (v, v')).
Proof.
  intros H; destruct_step; first done.
  - inversion H.
  - inversion H.
Qed.

Lemma invert_step_store {A} σ ℓ v' v k (m': state A) :
  σ !! ℓ = Some v' →
  step (σ, Stop CStore (ℓ, v) k) m' →
  m' = (<[ ℓ := v ]> σ, k ()).
Proof.
  intros Hℓ Hstep. remember (ℓ, v).
  inversion Hstep.
  all: apply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
  all: simplify_eq.
  - reflexivity.
  - exfalso.
    apply H3. apply elem_of_dom_2 in Hℓ. exact Hℓ.
Qed.

Lemma invert_step_load {A} σ σ' ℓ v k (m': free A) :
  σ !! ℓ = Some v →
  step (σ, Stop CLoad ℓ k) (σ', m') →
  σ' = σ ∧ m' = k v.
Proof.
  intros Hin Hstep.
  dependent destruction Hstep;
    (split; first reflexivity).
  - by simplify_eq.
  - exfalso. apply H, elem_of_dom_2 with v, Hin.
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

Lemma invert_step_bind' {A B} σ (m : free A) (f : A → free B) (b' : state B) :
  step (σ, bind m f) b' →
  ¬ is_answer m →
  (∃ σ' m', step (σ, m) (σ', m') ∧ b' = (σ', bind m' f)).
Proof.
  intros Hstep Hnoret.
  pose proof (invert_step_bind σ m f b' Hstep) as [(?&?&Hstep'&->)|(?&->&?)].
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

Lemma step_can_step {A} (s s': state A):
  step s s' → can_step s.
Proof.
  intros?. by exists s'.
Qed.

(* TODO seems redundant with invert_can_step_crash *)
Lemma can_step_crash {A} σ :
  ~ (can_step (σ, @crash A)).
Proof.
  intros H%invert_can_step_Crash. assumption.
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
