From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.
From iris.prelude Require Import prelude options.

(* This file defines an ample-step semantics, that is, a reduction semantics
   of the form [step c c'] where [c] and [c'] are pairs of a computation in
   the [micro] monad and a store. *)

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
  store * micro A.

(* This tactic explodes a configuration [c] into a pair [(σ, m)]. *)

Ltac destruct_config :=
  repeat match goal with c: config _ |- _ => destruct c end.

(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] cannot step. It is a result. *)

(* [Next] and [Crash] cannot step. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always step. This preserves the property that the only stuck terms are
   [Next] and [Crash]. There is a lot of non-determinism in these reduction
   rules: e.g., [Par Crash Next _ _] can step to either [Crash] or [Next]. *)

Inductive step {A} : config A → config A → Prop :=

  (* [Stop CEval (η, e) k ko] steps to an invocation of [eval η e] under
     [try _ k ko]. Thus, from the user's perspective, the computation
     [stop CEval (η, e)] behaves just like [eval η e]. *)
  | StepEval :
      ∀ σ η e k ko,
      step
        (σ, Stop CEval (η, e) k ko)
        (σ, try (eval η e) k ko)

  (* [stop (η, x, i1, i2, e)] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ η x i1 i2 e k ko,
      step
        (σ, Stop CLoop (η, x, i1, i2, e) k ko)
        (σ, try (loop η x i1 i2 e) k ko)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with [v], and returns this location. *)
  | StepAlloc :
      ∀ σ v l k ko,
      σ !! l = None →
      step
        (σ, Stop CAlloc v k ko)
        (<[l := v]>σ, k l)

  (* If the location [l] exists, then [stop CLoad l] looks up its content
     in the heap and returns it. *)
  | StepLoadSuccess :
      ∀ σ l v k ko,
      σ !! l = Some v →
      step
        (σ, Stop CLoad l k ko)
        (σ, k v)

  (* If the location [l] does not exist, then [stop CLoad l] fails. This
     ensures that [Crash] is the only stuck term. *)
  | StepLoadFailure :
      ∀ σ l k ko,
      σ !! l = None →
      step
        (σ, Stop CLoad l k ko)
        (σ, Crash)

  (* If the location [l] exists, then [stop CStore (l, v')] overwrites
     its content with [v'] and returns a unit value. *)
  | StepStoreSuccess :
      ∀ σ l v' v k ko,
      σ !! l = Some v →
      step
        (σ, Stop CStore (l, v') k ko)
        (<[ l := v' ]> σ, k tt)

  (* If the location [l] does not exist, then [stop CStore (l, v')] fails.
     This ensures that [Crash] is the only stuck term. *)
  | StepStoreFailure :
      ∀ σ l v' k ko,
      σ !! l = None →
      step
        (σ, Stop CStore (l, v') k ko)
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
      ∀ {A1 A2} σ m2 (k : A1 * A2 → micro A) ko,
      step
        (σ, Par Crash m2 k ko)
        (σ, Crash)

  | StepParCrashRight :
      ∀ {A1 A2} σ m1 (k : A1 * A2 → micro A) ko,
      step
        (σ, Par m1 Crash k ko)
        (σ, Crash)

  (* If a soft failure on either side is detected, then
     the failure continuation [n] can be invoked. *)
  | StepParNextLeft :
      ∀ {A1 A2} σ m2(k : A1 * A2 → micro A) ko,
      step
        (σ, Par Next m2 k ko)
        (σ, ko())

  | StepParNextRight :
      ∀ {A1 A2} σ m1 (k : A1 * A2 → micro A) ko,
      step
        (σ, Par m1 Next k ko)
        (σ, ko())

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2} σ σ' (m1 m'1 : micro A1) (m2 : micro A2) k ko,
      step (σ, m1) (σ', m'1) →
      step
        (σ, Par m1 m2 k ko)
        (σ', Par m'1 m2 k ko)

  | StepParRight :
      ∀ {A1 A2} σ σ' (m1 : micro A1) {m2 m'2 : micro A2} k ko,
      step (σ, m2) (σ', m'2) →
      step
        (σ, Par m1 m2 k ko)
        (σ', Par m1 m'2 k ko)

  (* [choose] steps to either side. *)
  | StepChooseLeft :
      ∀ {B} σ m1 m2 (k : B → micro A) z,
      step
        (σ, Choose m1 m2 k z)
        (σ, try m1 k z)

  | StepChooseRight :
      ∀ {B} σ m1 m2 (k : B → micro A) z,
      step
        (σ, Choose m1 m2 k z)
        (σ, try m2 k z)

.

Global Hint Constructors step : step.

Ltac destruct_step :=
  try match goal with h: step (?σ, Stop ?c ?x ?k ?ko) ?m' |- _ =>
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

(* [is_ret m] is [Some a] if and only if [m] is [Ret a]. *)

(* [is_ret] offers an executable way of testing whether a computation is
   [Ret _]. *)

Definition is_ret {A} (m : micro A) : option A :=
  match m with
  | Ret a => Some a
  | _     => None
  end.

(* Basic properties of [is_ret]. *)

Lemma invert_is_ret_Some {A} {m : micro A} {a} :
  is_ret m = Some a →
  m = Ret a.
Proof.
  destruct m; inversion 1; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_not_ret m] holds if [m] is not [ret _]. *)

Notation is_not_ret m :=
  (is_ret m = None).

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_not_ret]. *)

Lemma is_not_ret_ret {A} (a : A) :
  is_not_ret (ret a) →
  False.
Proof.
  simpl. congruence.
Qed.

Lemma is_not_ret_bind {A B} (m : micro A) (f : A → micro B) :
  is_not_ret m →
  is_not_ret (bind m f).
Proof.
  destruct m; simpl; congruence.
Qed.

Lemma is_not_ret_crash {A} :
  is_not_ret (Crash : micro A).
Proof.
  reflexivity.
Qed.

Lemma is_not_ret_next {A} :
  is_not_ret (Next : micro A).
Proof.
  reflexivity.
Qed.

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

(* A configuration that is not [ret _] and that is unable to step is stuck. *)

Definition stuck {A} (c : config A) :=
  let '(σ, m) := c in
  is_not_ret m ∧
  ∀ σ' m', ¬ step (σ, m) (σ', m').

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* [Ret a] cannot step. *)

Lemma invert_can_step_Ret {A} σ (a : A) :
  can_step (σ, Ret a) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [Crash] cannot step. *)

Lemma invert_can_step_Crash {A} σ :
  can_step (σ, Crash : micro A) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [Next] cannot step. *)

Lemma invert_can_step_Next {A} σ :
  can_step (σ, Next : micro A) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Crash
  invert_can_step_Next
: invert_can_step.

(* If the location [l] exists in the store, then [stop CStore (l, v')]
   can step in only one way. *)

Lemma invert_step_store {A} σ l v' v k ko σ' (m' : micro A) :
  σ !! l = Some v →
  step (σ, Stop CStore (l, v') k ko) (σ', m') →
  σ' = <[ l := v' ]> σ ∧
  m' = k ().
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* If the location [l] exists in the store, then [stop CLoad l]
   can step in only one way. *)

Lemma invert_step_load {A} σ σ' l v k ko (m' : micro A) :
  σ !! l = Some v →
  step (σ, Stop CLoad l k ko) (σ', m') →
  σ' = σ ∧
  m' = k v.
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* A term that can step is not [ret _]. *)

Lemma can_step_is_not_ret {A} σ (m : micro A) :
  can_step (σ, m) →
  is_not_ret m.
Proof.
  intros.
  destruct m; solve [ exfalso; eauto with invert_can_step | simpl; tauto ].
Qed.

(* [Stop] can step. *)

Lemma can_step_stop {A X Y} σ (c : code X Y) x (k : Y → micro A) ko :
  can_step (σ, Stop c x k ko).
Proof.
  destruct c; repeat destruct x as (x & ?);
  (* For reading and writing, we must reason by cases, according to
     whether the location [l] is or is not in the domain of [σ]. *)
  try match goal with σ: store, l: loc |- _ => case_eq (σ !! l) end;
  (* All cases except allocation are handled here: *)
  eauto using step_up_to_eq with step.
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

Local Lemma can_step_under_par {A1 A2 A} σ m1 m2 (k : A1 * A2 → micro A) ko :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step (σ, Par m1 m2 k ko).
Proof.
  intros [|]; destruct_can_step; eauto using step_up_to_eq with step.
Qed.

(* [Par] can step. *)

Lemma can_step_par :
  ∀ {A} (m : micro A) {A1 A2} σ m1 m2 (k : A1 * A2 → micro A) ko,
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

Lemma can_step_choose :
  ∀ {A B} σ m m1 m2 (k : A → micro B) z,
  m = Choose m1 m2 k z →
  can_step (σ, m).
Proof.
  intros. subst. unfold can_step. eauto with step.
Qed.

Global Hint Resolve can_step_par can_step_choose : step.

(* Stepping in the left-hand side of [try] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_try {A B} σ σ' (m m' : micro A) (f : A → micro B) ko :
  step (σ, m) (σ', m') →
  step (σ, try m f ko) (σ', try m' f ko).
Proof.
  inversion 1; subst;
  rewrite ?try_stop ?try_par ?try_choose ?try_crash ?try_try;
  eauto using step_up_to_eq with step.
Qed.

(* As a special case, stepping under [bind] is also permitted. *)

Lemma step_bind {A B} σ σ' (m m' : micro A) (f : A → micro B) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  rewrite !bind_as_try. eauto using step_try.
Qed.

(* Corollaries. *)

Lemma can_step_try {A B} σ (m : micro A) (f : A → micro B) ko :
  can_step (σ, m) →
  can_step (σ, try m f ko).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_try.
Qed.

Lemma can_step_bind {A B} σ (m : micro A) (f : A → micro B) :
  can_step (σ, m) →
  can_step (σ, bind m f).
Proof.
  rewrite bind_as_try. eauto using can_step_try.
Qed.

Global Hint Resolve can_step_try can_step_bind : can_step.

(* If [try m f ko] takes a step, and if [m] can step, then the step taken by
   [try m f ko] must a step of [m] under the context [try _ f ko]. *)

(* In other words, reduction under a context is mandatory: no other reduction
   is possible. *)

Lemma invert_step_try {A B σ} {m : micro A} {f : A → micro B} {ko σ' mm} :
  step (σ, try m f ko) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try m' f ko).
Proof.
  destruct m;
  rewrite ?try_ret ?try_stop ?try_par ?try_crash;
  intros;
  try solve [
    (* Case: [Ret] *)
    exfalso; eauto with invert_can_step
  | (* Every other case: *)
    destruct_step; eauto with step try_try
  ].
Qed.

(* The following lemma looks like a special case of [invert_step_try], but
   is in fact stronger, as it requires just [is_not_ret m] instead of the
   stronger hypothesis [can_step (_, m)]. *)

Lemma invert_step_bind {A B σ m} {f : A → micro B} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  is_not_ret m →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  destruct m;
  rewrite ?try_ret ?try_stop ?try_par ?try_crash;
  intros;
  try solve [
    (* Case: [Ret] *)
    exfalso; eauto using is_not_ret_ret
  | (* Every other case: *)
    destruct_step; eauto with step bind_try
  ].
Qed.

(* -------------------------------------------------------------------------- *)

(* More properties of [is_not_ret]. *)

Lemma is_not_ret_try {A B σ} (m : micro A) (f : A → micro B) ko :
  can_step (σ, m) →
  is_not_ret (try m f ko).
Proof.
  destruct m; simpl; intros;
  solve [ eauto | exfalso; eauto with invert_can_step ].
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [stuck]. *)

(* [ret _] is not stuck. *)

Lemma invert_stuck_ret {A} (a : A) σ :
  stuck (σ, ret a) →
  False.
Proof.
  unfold stuck. intuition eauto using is_not_ret_ret.
Qed.

(* A configuration that can step is not stuck. *)

Lemma can_step_not_stuck {A} (c : config A) :
  stuck c →
  can_step c →
  False.
Proof.
  destruct c as (σ, m).
  unfold can_step, stuck.
  intros (_ & Hnostep).
  intros ([σ' m'] & Hstep).
  eapply Hnostep. exact Hstep.
Qed.

(* [Crash] is stuck. *)

Lemma stuck_Crash {A} σ :
  stuck (σ, Crash : micro A).
Proof.
  unfold stuck. split.
  { eauto using is_not_ret_crash. }
  { inversion 1. }
Qed.

(* [Next] is stuck. *)

Lemma stuck_Next {A} σ :
  stuck (σ, Next : micro A).
Proof.
  unfold stuck. split.
  { eauto using is_not_ret_next. }
  { inversion 1. }
Qed.

(* The only stuck terms are [Crash] and [Next]. *)

Lemma only_crash_and_next_are_stuck {A} σ (m : micro A) :
  stuck (σ, m) →
  m = Crash ∨ m = Next.
Proof.
  intros.
  destruct m; try solve [
    eauto
  | exfalso; eauto using invert_stuck_ret
  | exfalso; eauto using can_step_not_stuck with step
  ].
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B} σ (m : micro A) (f : A → micro B) :
  stuck (σ, m) →
  stuck (σ, bind m f).
Proof.
  intros [|]%only_crash_and_next_are_stuck; subst m.
  + rewrite bind_crash. eauto using stuck_Crash.
  + rewrite bind_next. eauto using stuck_Next.
Qed.

(* -------------------------------------------------------------------------- *)

(* A triplicity principle. *)

(* This principle allows case analyses with three cases, as follows:
   either [m] is a result, or [m] can step, or [m] is stuck. *)

Lemma triplicity {A} σ (m : micro A) :
  (∃ a, m = ret a) ∨
  can_step (σ, m) ∨
  stuck (σ, m).
Proof.
  destruct m; eauto using stuck_Crash, stuck_Next with step.
Qed.

Ltac triplicity σ m H :=
  let a := fresh "a" in
  destruct (triplicity σ m) as [ (a & ->) | [ H | H ]].
