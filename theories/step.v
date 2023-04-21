From stdpp Require Import gmap.
Require Import lang base free eval store.

(* This file defines an ample-step semantics, that is, a reduction semantics
   of the form [step m m'] where [m] and [m'] are computations in the [free]
   monad. *)

(* The definition of the relation [step] interprets a [Stop] event as a
   request for a recursive invocation of the evaluator. *)

(* Working directly with the relation [step] removes the need to transport
   computations from the free monad into some other monad. (This was the
   job of the function [handle] defined in handle.v.) *)

(* -------------------------------------------------------------------------- *)
(* The state of an execution is a term of type [free A] taken together with
   a store. *)
Definition state (A : Type) : Type := store * free A.


(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Next] cannot step. They are answers. *)

(* [Fail] cannot step. It represents a crash. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always be reduced. This preserves the property that the only stuck term
   is [Fail]. There is a lot of non-determinism in these reduction rules:
   e.g., [Par Fail Next _ _] can reduce to either [Fail] or [Next]. *)

Inductive step {A} : state A → state A → Prop :=

  (* [Stop Eval (η, e) k] steps to an invocation of [eval η e] followed
     with the continuation [k]. *)
  (* Isolating an explicit equality [p = (η, e)] seems necessary to work
     around a bug or limitation (?) in [dependent destruction]. *)
  | StepEval :
      ∀ σ p η e k,
      p = (η, e) →
      step
        (σ, Stop Eval p k)
        (σ, bind (eval η e) k)

  (* [Stop Loop (η, x, i1, i2, e) k] steps to [loop η x i1 i2 e] followed
     with the continuation [k]. *)
  | StepLoop :
      ∀ σ p η x i1 i2 e k,
      p = (η, x, i1, i2, e) →
      step
        (σ, Stop Loop p k)
        (σ, bind (loop η x i1 i2 e) k)

  (* [Stop Flip () k] steps to an application of the continuation [k] to
     either [false] or [true]. *)
  | StepFlip :
      ∀ σ b x k,
      step
        (σ, Stop Flip x k)
        (σ, k b)

  (* [Stop Ref v] adds a fresh location in the store and stores [v] there; and
      steps to an application of the continuation [k] to this location. *)
  | StepStopRef :
      ∀ σ v k,
      let '(l, σ') := store_ref σ v in
      step
        (σ, Stop Ref v k)
        (σ', k l)

  | StepStopLoadSuccess :
      ∀ σ l k (H: l ∈ dom σ),
      let v := store_load σ l H in
      step
        (σ, Stop Load l k)
        (σ, k v)

  | StepStopLoadFailure :
      ∀ σ l k (H: l ∉ dom σ),
      step
        (σ, Stop Load l k)
        (σ, Fail)

  | StepStopStoreSuccess :
      ∀ σ l v k (H: l ∈ dom σ),
      step (σ, Stop Store (l, v) k) (<[ l := v]> σ, k tt)

  | StepStopStoreFailure :
      ∀ σ (l: loc) v k (H: l ∉ dom σ),
      step
        (σ, Stop Store (l, v) k)
        (<[ l := v ]>σ, Fail)

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2} σ (v1 : A1) (v2 : A2) k ko,
      step
        (σ, Par (Ret v1) (Ret v2) k ko)
        (σ, k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParFailLeft :
      ∀ {A1 A2} σ m2 (k : A1 * A2 → free A) ko,
      step
        (σ, Par Fail m2 k ko)
        (σ, Fail)
  | StepParFailRight :
      ∀ {A1 A2} σ m1 (k : A1 * A2 → free A) ko,
      step
        (σ, Par m1 Fail k ko)
        (σ, Fail)

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
    destruct m; try solve [ false; tauto ]; clear h
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
  - exists (σ, bind (eval x e) k). apply StepEval, eq_refl.
  - exists (σ, bind (loop x v i0 i e) k). apply StepLoop, eq_refl.
  - exists (σ, k false). apply StepFlip.
  - set ℓ := fresh_locs (dom σ).
    exists (<[ℓ:=x]> σ, k ℓ). apply StepStopRef.
  - (* TODO: destruct the "belongs to" predicate instead of the result of
     *       lookup. *)
    destruct (σ !! x) eqn:E.
    + (* The load operation will succeed. *)
      apply elem_of_dom_2 in E.
      exists (σ, k (store_load σ x E)).
      apply StepStopLoadSuccess.
    + (* The load operation will fail. *)
      exists (σ, Fail). apply StepStopLoadFailure.
      apply not_elem_of_dom_2, E.
  - (* TODO: ditto. *)
    destruct (σ !! x) eqn:E.
    + (* The store operation will succeed. *)
      apply elem_of_dom_2 in E.
      exists (store_store σ x v E, k tt).
      by apply StepStopStoreSuccess.
    + (* The store operation will fail. *)
      apply not_elem_of_dom_2 in E.
      exists (<[ x := v ]> σ, Fail).
      by apply StepStopStoreFailure.
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
  step (σ, (bind m) f) (σ', (bind m') f).
Proof.
  inversion 1; subst;
  rewrite ?bind_stop ?bind_par ?bind_fail ?bind_bind;
  eauto using step_eq with step;
  eauto using StepFlip, step_eq with step.
  (* TODO: improve the way the new cases are handeled. *)
  - by pose proof (StepStopRef σ v (λ v0 : loc, bind (k v0) f)) as Hstep.
  - by pose proof (StepStopLoadSuccess σ' l (λ v1 : val, bind (k v1) f) H3) as Hstep.
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
  rewrite ?bind_ret ?bind_stop ?bind_par ?bind_fail;
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
  - pose proof (StepStopRef σ x k).
    simpl in H.
    exists (k (fresh_locs (dom σ))), (<[fresh_locs (dom σ):=x]> σ).
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

(* [Fail] cannot step. *)

Lemma invert_can_step_Fail {A} σ :
  can_step (σ, Fail : free A) →
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
  invert_can_step_Fail
  invert_can_step_Next
: invert_can_step.

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
  destruct m; try solve [ false; eauto with invert_can_step | simpl; tauto ].
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

(* [Fail] is stuck. *)

Lemma stuck_Fail {A} σ :
  stuck (σ, Fail : free A).
Proof.
  unfold stuck. split. eauto. inversion 1.
Qed.

(* The only stuck term is [Fail]. *)

Lemma only_fail_is_stuck {A} σ (m : free A) :
  stuck (σ, m) →
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

Lemma stuck_bind {A B} σ (m : free A) (f : A → free B) :
  stuck (σ, m) →
  stuck (σ, bind m f).
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

Lemma triplicity {A} σ (m : free A) :
  is_answer m ∨
  can_step (σ, m) ∨
  stuck (σ, m).
Proof.
  destruct m; eauto using stuck_Fail with step is_answer.
Qed.

Ltac triplicity σ m H :=
  destruct (triplicity σ m) as [ H | [ H | H ]].
