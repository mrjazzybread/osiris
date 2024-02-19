From stdpp Require Import gmap relations.
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

Definition config (A E : Type) : Type :=
  store * micro A E.

(* This tactic explodes a configuration [c] into a pair [(σ, m)]. *)

Ltac destruct_config :=
  repeat match goal with c: config _ _ |- _ => destruct c end.

(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] cannot step. It is a result. *)

(* [Throw e] and [Crash] cannot step. *)

(* The reduction rules for [Par] are designed so as to guarantee that [Par]
   can always step. This preserves the property that the only stuck terms
   are [Throw _] and [Crash]. There is a lot of non-determinism in these
   reduction rules: e.g., [Par Crash (Throw _) _ _] can step to either
   [Crash] or [Throw _]. *)

Inductive step {A E} : config A E → config A E → Prop :=

  (* [Stop CEval (η, e) k z] steps to an invocation of [eval η e] under
     [try _ k z]. Thus, from the user's perspective, the computation
     [stop CEval (η, e)] behaves just like [eval η e]. *)
  | StepEval :
      ∀ σ η e k z,
      step
        (σ, Stop CEval (η, e) k z)
        (σ, try (eval η e) k z)

  (* [stop (η, x, i1, i2, e)] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ η x i1 i2 e k z,
      step
        (σ, Stop CLoop (η, x, i1, i2, e) k z)
        (σ, try (loop η x i1 i2 e) k z)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with [v], and returns this location. *)
  | StepAlloc :
      ∀ σ v l k z,
      σ !! l = None →
      step
        (σ, Stop CAlloc v k z)
        (<[l := v]>σ, k l)

  (* If the location [l] exists, then [stop CLoad l] looks up its content
     in the heap and returns it. *)
  | StepLoadSuccess :
      ∀ σ l v k z,
      σ !! l = Some v →
      step
        (σ, Stop CLoad l k z)
        (σ, k v)

  (* If the location [l] does not exist, then [stop CLoad l] fails. This
     ensures that [Crash] is the only stuck term. *)
  | StepLoadFailure :
      ∀ σ l k z,
      σ !! l = None →
      step
        (σ, Stop CLoad l k z)
        (σ, Crash)

  (* If the location [l] exists, then [stop CStore (l, v')] overwrites
     its content with [v'] and returns a unit value. *)
  | StepStoreSuccess :
      ∀ σ l v' v k z,
      σ !! l = Some v →
      step
        (σ, Stop CStore (l, v') k z)
        (<[ l := v' ]> σ, k tt)

  (* If the location [l] does not exist, then [stop CStore (l, v')] fails.
     This ensures that [Crash] is the only stuck term. *)
  | StepStoreFailure :
      ∀ σ l v' k z,
      σ !! l = None →
      step
        (σ, Stop CStore (l, v') k z)
        (σ, Crash)

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2 E'} σ (v1 : A1) (v2 : A2) k (z : E' → _),
      step
        (σ, Par (Ret v1) (Ret v2) k z)
        (σ, k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParCrashLeft :
      ∀ {A1 A2 E'} σ m2 (k : A1 * A2 → _) (z : E' → _),
      step
        (σ, Par Crash m2 k z)
        (σ, Crash)

  | StepParCrashRight :
      ∀ {A1 A2 E'} σ m1 (k : A1 * A2 → _) (z : E' → _),
      step
        (σ, Par m1 Crash k z)
        (σ, Crash)

  (* If a soft failure on either side is detected, then
     the failure continuation [z] can be invoked. *)
  | StepParNextLeft :
      ∀ {A1 A2 E'} σ m2 e (k : A1 * A2 → _) (z : E' → _),
      step
        (σ, Par (Throw e) m2 k z)
        (σ, z e)

  | StepParNextRight :
      ∀ {A1 A2 E'} σ m1 e (k : A1 * A2 → _) (z : E' → _),
      step
        (σ, Par m1 (Throw e) k z)
        (σ, z e)

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2 E'} σ σ' m1 m'1 m2 (k : A1 * A2 → _) (z : E' → _),
      step (σ, m1) (σ', m'1) →
      step
        (σ, Par m1 m2 k z)
        (σ', Par m'1 m2 k z)

  | StepParRight :
      ∀ {A1 A2 E'} σ σ' m1 m2 m'2 (k : A1 * A2 → _) (z : E' → _),
      step (σ, m2) (σ', m'2) →
      step
        (σ, Par m1 m2 k z)
        (σ', Par m1 m'2 k z)

  (* [choose] steps to either side. *)
  | StepChooseLeft :
      ∀ {B E'} σ m1 m2 (k : B → _) (z : E' → _),
      step
        (σ, Choose m1 m2 k z)
        (σ, try m1 k z)

  | StepChooseRight :
      ∀ {B E'} σ m1 m2 (k : B → _) (z : E' → _),
      step
        (σ, Choose m1 m2 k z)
        (σ, try m2 k z)

.

Global Hint Constructors step : step.

Ltac destruct_step :=
  try match goal with h: step (?σ, Stop ?c ?x ?k ?z) ?m' |- _ =>
    remember x
  end;
  match goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

(* This auxiliary lemma is useful when a constructor of the relation [step]
   cannot be applied directly. *)

Lemma step_up_to_eq {A E} (c : config A E) σ e e' :
  step c (σ, e) →
  e = e' →
  step c (σ, e').
Proof.
  congruence.
Qed.

(* Inversion properties of [try] and [bind] *)

Lemma invert_try_ret {A B E' F} m1 m2 h v:
  @try A B E' F m1 m2 h = ret v ->
  (∃ a, m1 = ret a /\ m2 a = ret v) \/
  (∃ e, m1 = throw e /\ h e = ret v).
Proof.
  destruct m1 eqn: Hm1; intros; cbn in H; eauto; try solve [inversion H].
Qed.

Lemma invert_bind_ret {A B E} m1 m2 v:
  @bind A B E m1 m2 = ret v ->
  ∃ a, m1 = ret a /\ m2 a = ret v.
Proof.
  destruct m1 eqn: Hm1; intros; cbn in H; eauto; try solve [inversion H].
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_ret m] is [Some a] if and only if [m] is [Ret a]. *)

(* [is_ret] offers an executable way of testing whether a computation is
   [Ret _]. *)

Definition is_ret {A E} (m : micro A E) : option A :=
  match m with
  | Ret a => Some a
  | _     => None
  end.

(* Basic properties of [is_ret]. *)

Lemma invert_is_ret_Some {A E} {m : micro A E} {a} :
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

Lemma is_not_ret_ret {A E} (a : A) :
  is_not_ret (ret a : micro A E) →
  False.
Proof.
  simpl. congruence.
Qed.

Lemma is_not_ret_bind {A B E} (m : micro A E) (f : A → micro B E) :
  is_not_ret m →
  is_not_ret (bind m f).
Proof.
  destruct m; simpl; congruence.
Qed.

Lemma is_not_ret_crash {A E} :
  is_not_ret (Crash : micro A E).
Proof.
  reflexivity.
Qed.

Lemma is_not_ret_throw {A E} (e : E) :
  is_not_ret (throw e : micro A E).
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_throw m] is [Some a] if and only if [m] is [Throw a]. *)

(* [is_throw] offers an executable way of testing whether a computation is
   [Throw _]. *)

Definition is_throw {A B} (m : micro A B) : option B :=
  match m with
  | Throw a => Some a
  | _     => None
  end.

(* Basic properties of [is_throw]. *)

Lemma invert_is_throw_Some {A E} {m : micro A E} {a} :
  is_throw m = Some a →
  m = Throw a.
Proof.
  destruct m; inversion 1; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_not_throw m] holds if [m] is not [throw _]. *)

Notation is_not_throw m :=
  (is_throw m = None).

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_not_throw]. *)

Lemma is_not_throw_throw {A E} (a : E) :
  is_not_throw (throw a : micro A E) →
  False.
Proof.
  simpl. congruence.
Qed.

Lemma is_not_throw_ret {A E} (e : A) :
  is_not_throw (ret e : micro A E).
Proof.
  reflexivity.
Qed.

Lemma is_not_throw_crash {A E} :
  is_not_throw (Crash : micro A E).
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [c] can step if there exists [c'] such that [c] steps to [c']. *)

Definition can_step {A E} (c : config A E) :=
  ∃ c', step c c'.

Global Hint Unfold can_step : step.

Ltac destruct_can_step :=
  match goal with
  | h: can_step _ |- _ =>
      destruct h as ((? & ?) & ?)
  end.

(* -------------------------------------------------------------------------- *)

(* A configuration that is not [ret _] and that is unable to step is stuck. *)

Definition stuck {A E} (c : config A E) :=
  let '(σ, m) := c in
  is_not_ret m ∧
  ∀ σ' m', ¬ step (σ, m) (σ', m').

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* [Ret a] cannot step. *)

Lemma invert_can_step_Ret {A E} σ a :
  can_step ((σ, Ret a) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [Crash] cannot step. *)

Lemma invert_can_step_Crash {A E} σ :
  can_step ((σ, Crash) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [throw e] cannot step. *)

Lemma invert_can_step_Throw {A E} σ e :
  can_step ((σ, throw e) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Crash
  invert_can_step_Throw
: invert_can_step.

(* If the location [l] exists in the store, then [stop CStore (l, v')]
   can step in only one way. *)

Lemma invert_step_store {A E} σ l v' v k z σ' m' :
  σ !! l = Some v →
  @step A E (σ, Stop CStore (l, v') k z) (σ', m') →
  σ' = <[ l := v' ]> σ ∧
  m' = k ().
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* If the location [l] exists in the store, then [stop CLoad l]
   can step in only one way. *)

Lemma invert_step_load {A E} σ σ' l v k z m' :
  σ !! l = Some v →
  @step A E (σ, Stop CLoad l k z) (σ', m') →
  σ' = σ ∧
  m' = k v.
Proof.
  intros. destruct_step; split; congruence.
Qed.

(* A term that can step is not [ret _]. *)

Lemma can_step_is_not_ret {A E} σ m :
  can_step ((σ, m) : config A E) →
  is_not_ret m.
Proof.
  intros.
  destruct m; solve [ exfalso; eauto with invert_can_step | simpl; tauto ].
Qed.

(* [Stop] can step. *)

Lemma can_step_stop {A X Y E' E}
  σ (c : code X Y E') x (k : Y → _) (z : E' → _) :
  can_step ((σ, Stop c x k z) : config A E).
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

Local Lemma can_step_under_par {A1 A2 A E' E}
  σ m1 m2 (k : A1 * A2 → _) (z : E' → _) :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step ((σ, Par m1 m2 k z) : config A E).
Proof.
  intros [|]; destruct_can_step; eauto using step_up_to_eq with step.
Qed.

(* [Par] can step. *)

Lemma can_step_par :
  ∀ {A E} m {A1 A2 E'} σ m1 m2 (k : A1 * A2 → _) (z : E' → _),
  m = Par m1 m2 k z →
  can_step ((σ, m) : config A E).
Proof.
  induction m; try solve [ congruence ].
  intros A'1 A'2 E'' σ' m'1 m'2 k' z' Heq.
  (* The hypothesis [Heq] is tricky because it involves different types
     on either side. Fortunately, [dependent destruction] is capable
     of deconstructing it for us. Phew! *)
  dependent destruction Heq.
  destruct m'1; eauto using can_step_under_par with step.
  destruct m'2; eauto using can_step_under_par with step.
Qed.

Lemma can_step_choose :
  ∀ {A B E' E} σ m m1 m2 (k : A → _) (z : E' → _),
  m = Choose m1 m2 k z →
  can_step ((σ, m) : config B E).
Proof.
  intros. subst. unfold can_step. eauto with step.
Qed.

Global Hint Resolve can_step_par can_step_choose : step.

(* Stepping in the left-hand side of [try] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_try {A B E' E} σ σ' m m' (f : A → micro B E) (h : E' → _) :
  step (σ, m) (σ', m') →
  step (σ, try m f h) (σ', try m' f h).
Proof.
  inversion 1; subst;
  simpl try;
  rewrite ?try_try;
  eauto using step_up_to_eq with step.
Qed.

(* As a special case, stepping under [bind] is also permitted. *)

Lemma step_bind {A B E} σ σ' m m' (f : A → micro B E) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  rewrite !bind_as_try. eauto using step_try.
Qed.

(* Corollaries. *)

Lemma can_step_try {A B E' E} σ m (f : A → micro B E) (h : E' → _) :
  can_step (σ, m) →
  can_step (σ, try m f h).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_try.
Qed.

Lemma can_step_bind {A B E} σ m (f : A → micro B E) :
  can_step (σ, m) →
  can_step (σ, bind m f).
Proof.
  rewrite bind_as_try. eauto using can_step_try.
Qed.

Global Hint Resolve can_step_try can_step_bind : can_step.

(* If [try m f h] takes a step, and if [m] can step, then the step taken by
   [try m f h] must a step of [m] under the context [try _ f h]. *)

(* In other words, reduction under a context is mandatory: no other reduction
   is possible. *)

Lemma invert_step_try {A B E' E σ} {m} {f : A → micro B E} {h : E' → _} {σ' mm} :
  step (σ, try m f h) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try m' f h).
Proof.
  destruct m;
  simpl try;
  intros;
  try solve [
    (* Case: [Ret] *)
    exfalso; eauto with invert_can_step
  | (* Every other case: *)
    destruct_step; eauto with step try_try
  ].
Qed.

Lemma invert_step_try' {A E} m (f : A → micro A E) (h : E → _) σ σ' mm :
  step.step (σ, try m f h) (σ', mm) →
  is_not_ret m ->
  is_not_throw m ->
  (∃ m', step.step (σ, m) (σ', m') ∧ mm = try m' f h).
Proof.
  destruct m;
  simpl try;
  intros;
  try solve [
    (* Case: [Ret] *) inversion H0
  | (* Every other case: *)
  destruct_step; eauto with step try_try; inversion H1
  ].
Qed.

(* The following lemma looks like a special case of [invert_step_try], but
   is in fact stronger, as it requires just [is_not_ret m] instead of the
   stronger hypothesis [can_step (_, m)]. *)

Lemma invert_step_bind {A B E σ m} {f : A → micro B E} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  is_not_ret m →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  destruct m;
  simpl try;
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

Lemma is_not_ret_try {A B E' E σ} m (f : A → micro B E) (h : E' → _) :
  can_step (σ, m) →
  is_not_ret (try m f h).
Proof.
  destruct m; simpl; intros;
  solve [ eauto | exfalso; eauto with invert_can_step ].
Qed.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [stuck]. *)

(* [ret _] is not stuck. *)

Lemma invert_stuck_ret {A E} a σ :
  stuck ((σ, ret a) : config A E) →
  False.
Proof.
  unfold stuck. intuition eauto using is_not_ret_ret.
Qed.

(* A configuration that can step is not stuck. *)

Lemma can_step_not_stuck {A E} (c : config A E) :
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

Lemma stuck_Crash {A E} σ :
  stuck ((σ, Crash) : config A E).
Proof.
  unfold stuck. split.
  { eauto using is_not_ret_crash. }
  { inversion 1. }
Qed.

(* [Throw e] is stuck. *)

Lemma stuck_Throw {A E} σ e :
  stuck ((σ, Throw e) : config A E).
Proof.
  unfold stuck. split.
  { eauto using is_not_ret_throw. }
  { inversion 1. }
Qed.

(* The only stuck terms are [Crash] and [Throw _]. *)

Lemma only_crash_and_throw_are_stuck {A E} σ m :
  stuck ((σ, m) : config A E) →
  m = Crash ∨ ∃ e, m = Throw e.
Proof.
  intros.
  destruct m; try solve [
    eauto
  | exfalso; eauto using invert_stuck_ret
  | exfalso; eauto using can_step_not_stuck with step
  ].
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B E} σ m (f : A → micro B E) :
  stuck (σ, m) →
  stuck (σ, bind m f).
Proof.
  intros [| (e & ?)]%only_crash_and_throw_are_stuck; subst m.
  + rewrite bind_crash. eauto using stuck_Crash.
  + rewrite bind_throw. eauto using stuck_Throw.
Qed.

(* -------------------------------------------------------------------------- *)

(* A triplicity principle. *)

(* This principle allows case analyses with three cases, as follows:
   either [m] is a result, or [m] can step, or [m] is stuck. *)

Lemma triplicity {A E} σ (m : micro A E) :
  (∃ a, m = ret a) ∨
  can_step (σ, m) ∨
  stuck (σ, m).
Proof.
  destruct m; eauto using stuck_Crash, stuck_Throw with step.
Qed.

Ltac triplicity σ m H :=
  let a := fresh "a" in
  destruct (triplicity σ m) as [ (a & ->) | [ H | H ]].

(* -------------------------------------------------------------------------- *)

Definition steps {A E} := @nsteps (config A E) step.

Global Hint Unfold steps : steps.
Global Hint Constructors nsteps : steps.

Definition produces {A E} n (m : micro A E) σ a :=
  steps n (σ, m) (σ, Ret a).

Global Hint Unfold produces : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [produces]. *)

(* [step] and [produces] can be composed. *)

Lemma step_produces {A E} n (m m' : micro A E) σ a :
  step (σ, m) (σ, m') →
  produces n m' σ a →
  produces (S n) m σ a.
Proof.
  unfold produces. econstructor; eauto.
Qed.

Global Hint Resolve step_produces : steps.
