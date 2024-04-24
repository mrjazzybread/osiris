From Coq Require Import Logic.FunctionalExtensionality.
From stdpp Require Import gmap relations.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.
From iris.prelude Require Import prelude options.

(* This file equips the [micro] monad with an operational semantics, that is,
   a reduction semantics of the form [step c c'] where [c] and [c'] are pairs
   of a store and a computation. *)

(* The definition of the relation [step] gives meaning to system calls, that
   is, to [Stop] events. For example, a [Stop CEval] event is interpreted as a
   request for a recursive invocation of the evaluator. It also gives meaning
   to the monad's non-standard constructs, namely [Handle], [Par], [Choose]. *)

(* -------------------------------------------------------------------------- *)

(* A memory block stores either a value or a captured continuation.

   A continuation is either not-yet-shot or already shot.

   This gives rise to three cases: [V] for values, [K] for continuations,
   and [Shot] for already-shot continuations.  *)

Inductive block : Type :=
| V (v : val)
| K (k : outcome2 val exn → microvx)
| Shot.

(* A store (or heap) is a finite map of locations to memory blocks. *)

Definition store : Type :=
  gmap loc block.

Implicit Type σ : store.

(* A configuration is a pair of a computation and a store. *)

Definition config (A E : Type) : Type :=
  store * micro A E.

(* This tactic explodes a configuration [c] into a pair [(σ, m)]. *)

Ltac destruct_config :=
  repeat match goal with c: config _ _ |- _ => destruct c end.

(* -------------------------------------------------------------------------- *)

(* A few technical tactics. *)

(* [exploit_location_lookup] rewrites an equality hypothesis [σ !! l = _]
   to rewrite in another hypothesis or in the goal, provided it mentions
   [σ !! l]. *)

Local Ltac exploit_location_lookup :=
  match goal with
  h1: ?σ !! ?l = _,
  h2: context[?σ !! ?l]
  |- _ =>
    rewrite h1 in h2
  |
  h1: ?σ !! ?l = _
  |- context[?σ !! ?l]
  =>
    rewrite h1
  end.

(* [case_location_lookup] finds an occurrence of [σ !! l] in a hypothesis or
   in the goal and performs a case analysis on [σ !! l], giving rise to 4
   cases (value block; ordinary continuation block; shot continuation block;
   nonexistent address). *)

Local Ltac case_location_lookup :=
  match goal with
  |- context[?σ !! ?l] =>
      let block := fresh "block" in
      let Hσ := fresh in
      destruct (σ !! l) as [ [ | | ] |] eqn:Hσ
  | h: context[?σ !! ?l] |- _ =>
      let block := fresh "block" in
      let Hσ := fresh in
      destruct (σ !! l) as [ [ | | ] |] eqn:Hσ
  end.

Local Hint Extern 1 (_ = _) =>
  exploit_location_lookup
: exploit_location_lookup.

(* -------------------------------------------------------------------------- *)

(* [step_load σ l k] is the right-hand side of the reduction rule [StepLoad].

   The rule loads a value from the store [σ] at location [l] and returns it to
   the continuation [k]. It fails if this location is not in the domain of [σ]
   or contains something other than a value. *)

Definition step_load_2 {A E} σ l (k : outcome2 val exn → _) : micro A E :=
  match σ !! l with
  | Some (V v) => continue k v
  | _          => crash
  end.

Notation step_load σ l k :=
  (σ, step_load_2 σ l k).

(* [step_load_2] commutes with [try2]. This expresses the intuition that
   [step_load_2 σ l k] is parametric in the continuation [k]: it applies
   [k] without inspecting it. In other words, loading is an "algebraic"
   effect. *)

Lemma try2_step_load_2 {A E B F} σ l k (k' : outcome2 A E → micro B F) :
  try2 (step_load_2 σ l k) k' = step_load_2 σ l (pftry2 k k').
Proof.
  unfold step_load_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_store σ l] is the right-hand side of the reduction rule [StepStore].

   This rule loads a value [v] from the store [σ] at location [l], overwrites
   it with the value [v'], and returns a unit value to the continuation [k].
   It fails if the location [l] is not in the domain of [σ] or contains
   something other than a value. *)

Definition step_store_1 σ l v' : store :=
  match σ !! l with
  | Some (V v) => <[ l := V v' ]> σ
  | _          => σ
  end.

Definition step_store_2 {A E} σ l (k : outcome2 unit exn → _) : micro A E :=
  match σ !! l with
  | Some (V v) => continue k ()
  | _          => crash
  end.

Notation step_store σ l v' k :=
  (step_store_1 σ l v', step_store_2 σ l k).

(* Storing is an algebraic effect. *)

Lemma try2_step_store_2 {A B E F} σ l
  (k : outcome2 unit val → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_store_2 σ l (pftry2 k k') = try2 (step_store_2 σ l k) k'.
Proof.
  unfold step_store_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_resume σ l o] is the right-hand side of the rule [StepResume].

   This rule loads a continuation [sk] from the store [σ] at location [l],
   overwrites it with [Shot], and resumes [sk] with the outcome [o] -- so the
   result of resuming [sk] with [o] is returned to the continuation [k]. This
   rule fails if the location [l] is not in the domain of [σ] or contains
   something other than a continuation. *)

Definition step_resume_1 σ l :=
  match σ !! l with
  | Some (K sk) => <[l := Shot]> σ
  | _           => σ
  end.

Definition step_resume_2 {A E} σ l o k : micro A E :=
  match σ !! l with
  | Some (K sk) => try2 (sk o) k
  | _           => crash
  end.

Notation step_resume σ l o k :=
  (step_resume_1 σ l, step_resume_2 σ l o k).

(* Resuming is an algebraic effect. *)

Lemma try2_step_resume_2 {A B E F} σ l o
  (k : _ → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_resume_2 σ l o (pftry2 k k') = try2 (step_resume_2 σ l o k) k'.
Proof.
  unfold step_resume_2. intros.
  case_location_lookup; simplify_eq; eauto with try_try.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_install σ l deep η bs l' k] is the right-hand side of the reduction
   rule [StepInstall].

   TODO change these definitions to *not* read [σ !! l] now;
        instead, replace [sk o] with [stop CResume (l, o)]
   TODO comment. *)

Definition step_install_1 σ l deep η bs l' :=
  match σ !! l with
  | Some (K sk) => <[l' := K (λ o, Handle (sk o) (λ o, eval_match deep η o bs))]> σ
  | _           => σ
  end.

Definition step_install_2 {A E} σ l l' (k : outcome2 loc exn → _) : micro A E :=
  match σ !! l with
  | Some (K sk) => continue k l'
  | _           => crash
  end.

Notation step_install σ l deep η bs l' k :=
  (step_install_1 σ l deep η bs l', step_install_2 σ l l' k).

(* Installing is an algebraic effect. *)

Lemma try2_step_install_2 {A B E F} σ l l'
  (k : _ → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_install_2 σ l l' (pftry2 k k') = try2 (step_install_2 σ l l' k) k'.
Proof.
  unfold step_install_2. intros.
  case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* A summary of our algebraicity laws. *)

Local Hint Resolve
  try2_step_load_2
  try2_step_store_2
  try2_step_resume_2
  try2_step_install_2
: algebraic.

(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Throw e] cannot step. They are results. *)

(* [Crash] cannot step. *)

(* [Stop CPerform e k] cannot step by itself. If it appears in the scope of
   [Handle] then it can step. *)

(* The reduction rules are designed so that [Handle] and [Par] can always
   step. There is a lot of non-determinism in the reduction of [Par]. *)

Inductive step {A E} : config A E → config A E → Prop :=

  (* [Stop CEval (η, e) k] steps to an invocation of [eval η e] under
     [try2 _ k]. Thus, from the user's perspective, the computation
     [stop CEval (η, e)] behaves just like [eval η e]. *)
  | StepEval :
      ∀ σ η e k,
      step
        (σ, Stop CEval (η, e) k)
        (σ, try2 (eval η e) k)

  (* [stop (η, x, i1, i2, e)] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ η x i1 i2 e k,
      step
        (σ, Stop CLoop (η, x, i1, i2, e) k)
        (σ, try2 (loop η x i1 i2 e) k)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with the value [v], and returns this location. *)
  | StepAlloc :
      ∀ σ v l k,
      σ !! l = None →
      step
        (σ, Stop CAlloc v k)
        (<[l := V v]>σ, continue k l)

  (* If the location [l] exists and contains a value [v], then
     [stop CLoad l] returns this value; otherwise, it crashes. *)
  | StepLoad :
      ∀ σ l k c',
      c' = step_load σ l k →
      step
        (σ, Stop CLoad l k)
        c'

  (* If the location [l] exists and contains a value [v], then
     [stop CStore (l, v')] overwrites this value with [v'];
     otherwise, it crashes. *)
  | StepStore :
      ∀ σ l v' k c',
      c' = step_store σ l v' k →
      step
        (σ, Stop CStore (l, v') k)
        c'

  (* If [Handle _ h] observes a normal result [ret v] then it reduces to an
     application of the first arm of the handler [h] to the value [v]. *)
  | StepHandleRet :
      ∀ σ v h,
      step
        (σ, Handle (Ret v) h)
        (σ, h (O3Ret v))

  (* If [Handle _ h] observes an exception [throw e] then it reduces to an
     application of the second arm of the handler [h] to the exception [e]. *)
  | StepHandleThrow :
      ∀ σ e h,
      step
        (σ, Handle (Throw e) h)
        (σ, h (O3Throw e))

  (* If [Handle _ h] observes an effect [perform e k] then it captures the
     continuation [k], which becomes stored at a fresh address [l] in the
     heap. Then, it reduces to an application of the third arm of the
     handler [h] to the effect [e] and to the location [l]. *)
  | StepHandlePerform :
      ∀ σ e k h l,
      σ !! l = None →
      step
        (σ, Handle (Stop CPerform e k) h)
        (<[l := K k]>σ, h (O3Perform e l))

  (* If [Handle _ h] observes a crash then this crash is propagated. *)
  | StepHandleCrash :
      ∀ σ h,
      step
        (σ, Handle Crash h)
        (σ, Crash)

  (* Reduction under [Handle _ h] is permitted. *)
  | StepHandleLeft :
      ∀ σ σ' m m' h,
      step (σ, m) (σ', m') →
      step (σ, Handle m h) (σ', Handle m' h)

  (* [stop Resume (l, o)] reads the continuation [sk] that is stored
     at address [l] in the heap, updates [l] to [Shot], and resumes the
     continuation [sk] with the outcome [o]. *)
  | StepResume :
      ∀ σ l o k c',
      c' = step_resume σ l o k →
      step
        (σ, Stop CResume (l, o) k)
        c'

  (* [stop CInstall (deep, l, η, bs)] wraps the continuation that is currently
     stored at address [l] in an effect handler described by [deep], [η], and
     [bs]. This results in a new continuation, which is stored in the heap at
     a fresh location [l']. This location is returned. *)
  | StepInstall :
      ∀ σ deep l η bs k l' c',
      σ !! l' = None →
      c' = step_install σ l deep η bs l' k →
      step
        (σ, Stop CInstall (deep, l, η, bs) k)
        c'

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2 E'} σ v1 v2 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par (Ret v1) (Ret v2) k)
        (σ, continue k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParCrashLeft :
      ∀ {A1 A2 E'} σ m2 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par Crash m2 k)
        (σ, Crash)

  | StepParCrashRight :
      ∀ {A1 A2 E'} σ m1 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par m1 Crash k)
        (σ, Crash)

  (* If a soft failure on either side is detected, then
     the failure component of the continuation [k] can be invoked. *)
  | StepParThrowLeft :
      ∀ {A1 A2 E'} σ m2 e (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par (Throw e) m2 k)
        (σ, discontinue k e)

  | StepParThrowRight :
      ∀ {A1 A2 E'} σ m1 e (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par m1 (Throw e) k)
        (σ, discontinue k e)

  (* If [Stop (perform e) k] appears under the context [Par _ m2 h] then
     it can capture this evaluation context frame. Thus, it reduces to a
     new term where [Stop (perform e) _] now appears naked and the captured
     evaluation context is [Par (k _) m2 h]. *)
  | StepParPerformLeft :
      ∀ {A1 A2 E'} σ m2 e k (h : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par (Stop CPerform e k) m2 h)
        (σ, Stop CPerform e (λ o, Par (k o) m2 h))

  | StepParPerformRight :
      ∀ {A1 A2 E'} σ m1 e k (h : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par m1 (Stop CPerform e k) h)
        (σ, Stop CPerform e (λ o, Par m1 (k o) h))

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2 E'} σ σ' m1 m'1 m2 (k : outcome2 (A1 * A2) E' → _),
      step (σ, m1) (σ', m'1) →
      step
        (σ, Par m1 m2 k)
        (σ', Par m'1 m2 k)

  | StepParRight :
      ∀ {A1 A2 E'} σ σ' m1 m2 m'2 (k : outcome2 (A1 * A2) E' → _),
      step (σ, m2) (σ', m'2) →
      step
        (σ, Par m1 m2 k)
        (σ', Par m1 m'2 k)

  (* [choose] steps to either side. *)
  | StepChooseLeft :
      ∀ {B E'} σ m1 m2 (k : outcome2 B E' → _),
      step
        (σ, Choose m1 m2 k)
        (σ, try2 m1 k)

  | StepChooseRight :
      ∀ {B E'} σ m1 m2 (k : outcome2 B E' → _),
      step
        (σ, Choose m1 m2 k)
        (σ, try2 m2 k)

.

Global Hint Constructors step : step.

Ltac destruct_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try match goal with h: step (?σ, Stop ?c ?x ?k) ?m' |- _ =>
    remember x
  end;
  match goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

(* -------------------------------------------------------------------------- *)

(* Some derived rules. *)

Lemma StepLoadSuccess {A E} σ l (k : outcome2 val exn → micro A E) v :
  σ !! l = Some (V v) →
  step
    (σ, Stop CLoad l k)
    (σ, continue k v).
Proof.
  intros Heq. econstructor. unfold step_load_2. rewrite Heq. eauto.
Qed.

Lemma StepStoreSuccess {A E} σ l v v' (k : outcome2 unit exn → micro A E) :
  σ !! l = Some (V v) →
  step
    (σ, Stop CStore (l, v') k)
    (<[ l := V v' ]> σ, continue k ()).
Proof.
  intros Heq. econstructor. unfold step_store_1, step_store_2.
  rewrite Heq. eauto.
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

(* -------------------------------------------------------------------------- *)

(* [is_throw m] is [Some a] if and only if [m] is [Throw a]. *)

(* [is_throw] offers an executable way of testing whether a computation is
   [Throw _]. *)

Definition is_throw {A B} (m : micro A B) : option B :=
  match m with
  | Throw a => Some a
  | _       => None
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

(* A configuration that is not [ret _] and that is unable to step is stuck.
   This includes unhandled exceptions and unhandled effects. *)

(* TODO it may be confusing to characterize unhandled exceptions and
   effects as "stuck". Could we just remove [stuck] entirely? *)

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

(* [perform e] cannot step. *)

Lemma invert_can_step_perform σ e :
  can_step (σ, perform e) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Crash
  invert_can_step_Throw
  invert_can_step_perform
: invert_can_step.

(* -------------------------------------------------------------------------- *)

(* If the location [l] exists in the store and contains a value,
   then [stop CLoad l] can step in only one way. *)

Lemma invert_step_load {A E} σ σ' l v k m' :
  σ !! l = Some (V v) →
  @step A E (σ, Stop CLoad l k) (σ', m') →
  σ' = σ ∧
  m' = continue k v.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_load_2. rewrite Heq.
  eauto.
Qed.

(* If the location [l] exists in the store and contains a value,
   then [stop CStore (l, v')] can step in only one way. *)

Lemma invert_step_store {A E} σ l v' v k σ' m' :
  σ !! l = Some (V v) →
  @step A E (σ, Stop CStore (l, v') k) (σ', m') →
  σ' = <[ l := V v' ]> σ ∧
  m' = continue k ().
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_store_1, step_store_2. rewrite Heq.
  eauto.
Qed.

(* If the location [l] exists in the store and contains a continuation,
   then [stop CResume (l, o)] can step in only one way. *)

Lemma invert_step_resume {A E} σ σ' l o k sk m' :
  σ !! l = Some (K sk) →
  @step A E (σ, Stop CResume (l, o) k) (σ', m') →
  σ' = <[ l := Shot ]> σ ∧
  m' = try2 (sk o) k.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_resume_1, step_resume_2. rewrite Heq.
  eauto.
Qed.

(* If the location [l] exists in the store and contains a continuation,
   then [stop CInstall (l, η, bs)] can step in only one way. *)

Lemma invert_step_install {A E} deep σ σ' l η hs k sk m' :
  σ !! l = Some (K sk) ->
  @step A E (σ, Stop CInstall (deep, l, η, hs) k) (σ', m') ->
  ∃ l',
  σ !! l' = None /\
  σ' = <[ l' := K (λ o, Handle (sk o) (λ o, eval_match deep η o hs)) ]> σ /\
  m' = continue k l'.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_install_1, step_install_2. rewrite Heq.
  eauto.
Qed.

(* A term that can step is not [ret _]. *)

Lemma can_step_is_not_ret {A E} σ m :
  can_step ((σ, m) : config A E) →
  is_not_ret m.
Proof.
  intros.
  destruct m; solve [ exfalso; eauto with invert_can_step | simpl; tauto ].
Qed.

(* If [c] is not [CPerform _], then [Stop c x k] can step. *)

Lemma can_step_stop {A X Y E' E}
  σ (c : code X Y E') x (k : outcome2 Y E' → _) :
  match c with CPerform => False | _ => True end →
  can_step ((σ, Stop c x k) : config A E).
Proof.
  destruct c; repeat destruct x as (x & ?); try destruct o;
  (* Get rid of [CPerform]. *)
  first [ tauto | intros _ ];
  (* Deal with all remaining cases except [CAlloc]. *)
  eauto using StepLoad with step.
  (* In the case of allocation, we must exhibit an address [l]
     that is not in the domain of [σ]. *)
  { set (l := fresh (dom σ)).
    assert (lookup l σ = None) by apply not_elem_of_dom, is_fresh.
    eauto using StepAlloc with step. }
  (* In the case of wrap, we must also exhibit an address [l]
     that is not in the domain of [σ]. *)
  { set (l' := fresh (dom σ)).
    assert (lookup l' σ = None) by apply not_elem_of_dom, is_fresh.
    eauto using StepInstall with step. }
Qed.

Global Hint Resolve can_step_stop : step.

(* The following two auxiliary lemmas are used in the proof of
   [can_step_handle_par], which establishes a stronger result. *)

Local Lemma can_step_under_handle {A E} σ m h :
  can_step (σ, m) →
  can_step ((σ, Handle m h) : config A E).
Proof.
  intros; destruct_can_step; eauto using StepHandleLeft with step.
Qed.

Local Lemma can_step_under_par {A1 A2 A E' E}
  σ m1 m2 (k : outcome2 (A1 * A2) E' → _) :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step ((σ, Par m1 m2 k) : config A E).
Proof.
  intros [|]; destruct_can_step;
  eauto using StepParLeft, StepParRight with step.
Qed.

(* [Handle] and [Par] can step. *)

Lemma can_step_handle_par :
  ∀ {A E} (m : micro A E),
  match m with Handle _ _ | Par _ _ _ => True | _ => False end →
  ∀ σ,
  can_step (σ, m).
Proof.
  induction m; try tauto; intros _ σ.
  (* We get two goals, [Handle] and [Par]. *)

  (* Case: [Handle]. *)
  {
    (* Clear the (useless) second induction hypothesis. *)
    clear H.
    (* Analyze [m]; analyze [c]. *)
    destruct m; eauto using can_step_under_handle with step.
    destruct c; eauto using can_step_under_handle with step.
    (* We are now looking at [perform] under [handle]. *)
    (* An allocation is involved, so (again) we must exhibit
       an address [l] that is not in the domain of [σ]. *)
    set (l := fresh (dom σ)).
    assert (lookup l σ = None) by apply not_elem_of_dom, is_fresh.
    (* At this point, the reduction rule [StepHandlePerform] is
       exploited. It is worth noting that this rule can be used
       only if the computation that is being handled has type
       [micro val exn], as opposed to [micro A E]. This explains
       why the [Handle] construct is restricted to this case. *)
    eauto using StepHandlePerform with step.
  }

  (* Case: [Par]. *)
  {
    (* Analyze [m1]. *)
    destruct m1; eauto using can_step_under_par with step.
    + (* Analyze [m2]. *)
      destruct m2; eauto using can_step_under_par with step.
      (* We are now looking at [Stop] under [Par]. *)
      destruct c; eauto using can_step_under_par with step.
    + (* We are now looking at [Stop] under [Par]. *)
      destruct c; eauto using can_step_under_par with step.
  }

Qed.

(* Corollaries: [Handle] can step; [Par] can step. *)

Lemma can_step_handle {A E} σ m h :
  can_step ((σ, Handle m h) : config A E).
Proof.
  eauto using can_step_handle_par.
Qed.

Lemma can_step_par
  {A E A1 A2 E'} σ m1 m2 (k : outcome2 (A1 * A2) E' → _) :
  can_step ((σ, Par m1 m2 k) : config A E).
Proof.
  eauto using can_step_handle_par.
Qed.

(* [Choose] can step. *)

Lemma can_step_choose :
  ∀ {A B E' E} σ m1 m2 (k : outcome2 A E' → _),
  can_step ((σ, Choose m1 m2 k) : config B E).
Proof.
  eauto with step.
Qed.

Global Hint Resolve
  can_step_handle can_step_par can_step_choose
: step.

(* Stepping in the left-hand side of [try2] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_try2 {A B E' E} σ σ' m m' (h : outcome2 A E' → micro B E) :
  step (σ, m) (σ', m') →
  step (σ, try2 m h) (σ', try2 m' h).
Proof.
  inversion 1;
  simplify_eq;
  simpl try2;
  rewrite ?try2_try2;
  eauto with step algebraic f_equal.
Qed.

(* As special cases, stepping under [try] or [bind] is also permitted. *)

Lemma step_try {A B E' E} σ σ' m m' (f : A → micro B E) (h : E' → _) :
  step (σ, m) (σ', m') →
  step (σ, try m f h) (σ', try m' f h).
Proof.
  eauto using step_try2.
Qed.

Lemma step_bind {A B E} σ σ' m m' (f : A → micro B E) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  rewrite !bind_as_try. eauto using step_try.
Qed.

(* Corollaries. *)

Lemma can_step_try2 {A B E' E} σ m (h : outcome2 A E' → micro B E) :
  can_step (σ, m) →
  can_step (σ, try2 m h).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_try2.
Qed.

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

Global Hint Resolve can_step_try2 can_step_try can_step_bind : can_step.

(* If [try m f h] takes a step, and if [m] can step, then the step taken by
   [try m f h] must a step of [m] under the context [try _ f h]. *)

(* In other words, reduction under a context is mandatory: no other reduction
   is possible. *)

Lemma invert_step_try2 {A B E' E σ} {m} {h : outcome2 A E' → micro B E} {σ' mm} :
  step (σ, try2 m h) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try2 m' h).
Proof.
  destruct m;
  simpl try2;
  intros;
  (* Case: [Ret] *)
  try solve [ exfalso; eauto with invert_can_step ];
  (* Every other case: *)
  destruct_step;
  eauto with step algebraic try_try.
Qed.

Lemma invert_step_try {A B E' E σ} {m} {f : A → micro B E} {h : E' → _} {σ' mm} :
  step (σ, try m f h) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try m' f h).
Proof.
  eauto using invert_step_try2.
Qed.

(* A stronger version of the following lemma is proved later on. *)

Lemma invert_step_bind_weak {A B E σ} {m} {f : A → micro B E} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  intros Hstep Hcan.
  rewrite bind_as_try in Hstep.
  destruct (invert_step_try Hstep Hcan) as (m' & ? & ?). subst mm.
  exists m'. rewrite bind_as_try. eauto.
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
  unfold stuck. split; [ eauto | inversion 1 ].
Qed.

(* [Throw e] is stuck. *)

Lemma stuck_Throw {A E} σ e :
  stuck ((σ, Throw e) : config A E).
Proof.
  unfold stuck. split; [ eauto | inversion 1 ].
Qed.

(* [Stop CPerform e k] is stuck. *)

Lemma stuck_Perform {A E} σ e k :
  stuck ((σ, Stop CPerform e k) : config A E).
Proof.
  unfold stuck. split; [ eauto | inversion 1 ].
Qed.

(* The only stuck terms are [Crash] and [Throw _] and [perform _]. *)

Lemma only_crash_and_throw_and_perform_are_stuck {A E} σ m :
  stuck ((σ, m) : config A E) →
  m = Crash ∨ (∃ e, m = Throw e) ∨ (∃ e k, m = Stop CPerform e k).
Proof.
  intros.
  destruct m; try solve [
    eauto
  | exfalso; eauto using invert_stuck_ret
  | exfalso; eauto using can_step_not_stuck with step
  ].
  (* The case of [Stop] remains. *)
  destruct_code; try solve [
    eauto
  | exfalso; eauto using can_step_not_stuck with step
  ].
Qed.

(* TODO could we use this lemma
   and avoid reasoning with [stuck],
   which introduces painful negations? *)
Lemma only_crash_and_throw_and_perform_are_stuck' {A E} σ (m : micro A E) :
  match m with
  | Ret _
  | Crash
  | Throw _
  | Stop CPerform _ _ =>
      True
  | _ =>
      can_step (σ, m)
  end.
Proof.
  destruct m; eauto with step.
  destruct_code; eauto with step.
Qed.

(* If [m] is stuck then [bind m f] is also stuck. *)

Lemma stuck_bind {A B E} σ m (f : A → micro B E) :
  stuck (σ, m) →
  stuck (σ, bind m f).
Proof.
  intros Hstuck.
  apply only_crash_and_throw_and_perform_are_stuck in Hstuck.
  destruct Hstuck as [| [(e & ?) | (e & k & ?)]]; subst m; simpl bind;
  eauto using stuck_Crash, stuck_Throw, stuck_Perform.
Qed.

(* The following lemma is a stronger version of [invert_step_bind_weak].
   It requires just [is_not_ret m] instead of [can_step (_, m)]. *)

Lemma invert_step_bind {A B E σ m} {f : A → micro B E} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  is_not_ret m →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  intros.
  destruct m; intros; try destruct_code;
  (* This takes care of the cases covered by the weak lemma: *)
  eauto using invert_step_bind_weak with step;
  (* The remaining cases are [ret _] and the stuck terms. *)
  simpl in *; solve [ congruence | destruct_step ].
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
  destruct m; try destruct_code;
  eauto using stuck_Crash, stuck_Throw, stuck_Perform with step.
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
