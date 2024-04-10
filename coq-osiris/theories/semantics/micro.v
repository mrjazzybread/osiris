From Coq.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.

From osiris Require Export semantics.outcome.

(* This module defines a meta-language (a monad) within which one can
   implement an interpreter for an object language (such as OCaml). *)

(* This monad explicitly supports crashes, exceptions, delimited control
   effects (that is, effect handlers), a form of parallelism, and a form
   of non-deterministic choice. It implicitly offers support for other
   effects, such as divergence and global state, via "system calls". *)

(* ------------------------------------------------------------------------ *)

(* This module takes the form of a functor, [Make]. We take only one
   instance of this functor, in code.v, so this parameterization is not
   very useful, but it helps us clarify our assumptions. *)

Module Type PARAMS.

(* The type constructor [code] describes a set of services that a
   computation can request from the "runtime system". A service can also
   be thought of as a "system call" that a computation can make.

   A value of type [code X Y E] represents the name of a system call whose
   parameter has type [X], whose result has type [Y], and which can throw
   an exception of type [E]. *)

Parameter code : Type → Type → Type → Type.

(* Our support for delimited control effects allows a single effect, with
   a fixed signature. The following four types play a role in the type of
   the [Handle] construct, as follows:

   - The computation that is placed in the scope of the handler must have
     type [micro val exn]. That is, it may return a result of type [val]
     or throw an exception of type [exn].

   - If and when the handler takes control, it receives an effect of type
     [eff] and a continuation of type [continuation].

   It is crucial that the type [continuation] be abstract, as opposed to a
   function type [outcome2 val exn → micro val exn]. Indeed, if we tried
   to use such a function type, then the type [micro] would appear in a
   negative position inside its own definition.

   In code.v, we instantiate this functor by letting [val], [exn], and
   [eff] be the type of OCaml values and by letting [continuation] be the
   type of OCaml memory locations. Indeed, our continuations are allocated
   in the heap. This serves two purposes: 1- OCaml continuations are
   one-shot, so they must be mutable; 2- an indirection through the heap
   lets us avoid the negative-occurrence issue described above. *)

Parameter val          : Type.
Parameter exn          : Type.
Parameter eff          : Type.
Parameter continuation : Type.

End PARAMS.

Module Make (C : PARAMS).

Import C. (* We write [code] for [C.code]. *)

(* Notations and coercions for outcomes *)
Notation outcome3 := (outcome3 eff continuation).
Definition outcome_inject {A X} : outcome2 A X -> outcome3 A X := outcome2_inject.
Coercion outcome_inject : outcome2 >-> outcome3.

(* The abstract API of this micro monad is as follows.

   [ret a] is a computation that returns the result [a].

   [throw e] is a computation that throws the exception [e].

   [crash] is a hard failure. It represents a crash and cannot be caught.

   [try2 m h] runs the computation [m] under the two-armed handler [h],
   which handles either a result or an exception.

     [try m f h] is an alternate form of [try2], where the result arm [f]
     and the exception arm [h] are represented as two separate functions.
     Thus, if [m] returns a result [a] then [f a] is executed; if [m]
     throws an exception [throw e] then [h e] is executed.

     [bind m f] is the same as [try m f throw]. Thus, if [m] returns a
     result [a] then [f a] is executed; if [m] throws an exception then
     this exception is propagated.

   [handle m h] runs the computation [m] under the three-armed handler
   [h], which handles a result, an exception, or an effect.

   There is no dedicated construct for performing an effect; performing an
   effect is viewed as a particular case of a system call.

   [stop c x] is a system call, that is, a request for an external
   service. The name of the system call is [c] and its argument is [x].
   [c] has type [code X Y E], for some types [X], [Y] and [E]. The
   parameter [x] has type [X], and the outcome of the system call has type
   [outcome2 Y E].

   [par m1 m2] is a parallel evaluation construct. It evaluates [m1] and
   [m2] independently and in parallel. If the two computations have side
   effects (via system calls) then these effects are interleaved in a
   nondeterministic manner. If both computations succeed and return two
   results [v1] and [v2], then [par m1 m2] returns the pair [(v1, v2)]. If
   either side crashes, then [par m1 m2] can crash. If either side raises
   an exception, then this exception can be propagated upwards. If either
   side performs an effect, then this effect can be propagated upwards,
   thereby capturing the other side of the [par] construct in its
   continuation.

   [choose m1 m2] is a non-deterministic choice between the computations
   [m1] and [m2]. One of them is executed; the other is discarded. *)

(* The type [micro A] is inductive: every computation terminates.
   Non-terminating computations can be represented, but must (infinitely
   often) pause by performing a [stop] effect. *)

(* Internally, [bind] and [try] are special cases of [try2]. The
   combinator [try2] is not a constructor: instead, the constructors
   [Handle], [Stop], [Par] and [Choose] contain a built-in [try2]. This
   explains why each of these constructors carries a handler, which in the
   case of [Handle] has three arms, and otherwise has only two arms. This
   representation can be viewed as an implementation detail; however, this
   information does leak if one lets Coq reduce computations to a normal
   form. *)

(* The constructor [Stop] is similar to the constructor [Vis] of
   interaction trees, and the type [code] is similar to an effect
   signature. *)

Inductive micro A E :=
  | Ret (a : A)
  | Throw (e : E)
  | Crash
  | Handle
      (m : micro val exn)
      (h : outcome3 val exn → micro A E)
  | Stop {X Y E'}
      (c : code X Y E') (x : X)
      (k : outcome2 Y E' → micro A E)
  | Par {A1 A2 E'}
      (m1 : micro A1 E') (m2 : micro A2 E')
      (k : outcome2 (A1 * A2) E' → micro A E)
  | Choose {B E'}
      (m1 m2 : micro B E')
      (k : outcome2 B E' → micro A E)
.

(* Make [A] and [E] implicit arguments of the constructors. *)

Arguments Ret       {A E}.
Arguments Throw     {A E}.
Arguments Crash     {A E}.
Arguments Handle    {A E}.
Arguments Stop      {A E X Y E'} c x k.
Arguments Par       {A E A1 A2 E'} m1 m2 k.
Arguments Choose    {A E B E'} m1 m2 k.

(* ------------------------------------------------------------------------ *)

(* The following combinators are public: [ret], [throw], [crash], [stop],
   [par], [choose]. *)

Notation ret :=
  (Ret).

Notation throw :=
  (Throw).

Notation crash :=
  (Crash).

(* This injection of [outcome2] into [micro] represents a trivial
   two-armed (result/exception) handler. *)

Definition inject2 {A E} (o : outcome2 A E) : micro A E :=
  match o with
  | O2Ret a   => Ret a
  | O2Throw a => Throw a
  end.

(* [stop c x] stops, and, once restarted, behaves like the computation
   denoted by the code [c] applied to the argument [x]. The mapping of
   codes to computations is not defined here; it must be supplied a
   posteriori (step.v). *)

Definition stop {X Y E} (c : code X Y E) x : micro Y E :=
  Stop c x inject2.

(* [par m1 m2] runs the computations [m1] and [m2] in parallel,
   producing a pair of results. *)

Definition par {A1 A2 E} (m1 : micro A1 E) (m2 : micro A2 E)
: micro (A1 * A2) E :=
  Par m1 m2 inject2.

(* [choose m1 m2] performs a non-deterministic choice between [m1] and
   [m2] and runs the chosen computation, producing a single result. *)

Definition choose {A E} (m1 m2 : micro A E) : micro A E :=
  Choose m1 m2 inject2.

(* ------------------------------------------------------------------------ *)

(* The monadic combinators [bind], [try2], and [try]. *)

(* [bind m f] sequences the computations [m] and [f]. *)

(* In the cases of [Handle], [Stop], [Par], [Choose], the existing
   handler [h] is composed with the continuation [f]. The notation
   [pfbind h f] is later introduced to express this. *)

Fixpoint bind {A B E} (m : micro A E) (f : A → micro B E) : micro B E :=
  match m with
  | Ret a =>
      f a
  | Throw e =>
      Throw e
  | Crash =>
      Crash
  | Handle m h =>
      Handle m (λ o, bind (h o) f)
  | Stop c x h =>
      Stop c x (λ o, bind (h o) f)
  | Par m1 m2 h =>
      Par m1 m2 (λ o, bind (h o) f)
  | Choose m1 m2 h =>
      Choose m1 m2 (λ o, bind (h o) f)
  end.

Global Arguments bind A B E !m f : simpl nomatch.

(* [fmap f m] is sequences the computation [m] and the pure function [f]. *)

Definition fmap {A B E} (f : A -> B) (m : micro A E) : micro B E :=
  bind m (fun x => ret (f x)).

Global Arguments fmap A B E f m : simpl nomatch.

(* [try2 m f] runs the computation [m] under the two-armed handler [f]. *)

(* In the cases of [Handle], [Stop], [Par], [Choose], the existing
   handler [h] is composed with the continuation [f]. The notation
   [pftry2 h f] is later introduced to express this. *)

Fixpoint try2 {A B E' E}
  (m : micro A E') (f : outcome2 A E' → micro B E)
: micro B E :=
  match m with
  | Ret a =>
      continue f a
  | Throw e =>
      discontinue f e
  | Crash =>
      Crash
  | Handle m h =>
      Handle m (λ o, try2 (h o) f)
  | Stop c x h =>
      Stop c x (λ o, try2 (h o) f)
  | Par m1 m2 h =>
      Par m1 m2 (λ o, try2 (h o) f)
  | Choose m1 m2 h =>
      Choose m1 m2 (λ o, try2 (h o) f)
  end.

(* [try] is defined in terms of [try2]. It expects the two arms of the
   handler to be given by two separate functions [f] and [h]. *)

Definition try {A B E' E}
  (m : micro A E') (f : A → micro B E) (h : E' → micro B E)
: micro B E :=
  try2 m (glue2 f h).

(* Point-free [bind]. *)

Notation pfbind k f :=
  (λ o, bind (k o) f).

(* Point-free [fmap]. *)

Notation pffmap f k := (λ o, fmap f (k o)).

(* Point-free [try2]. *)

Notation pftry2 k h :=
  (λ o, try2 (k o) h).

(* Point-free [try]. *)

Notation pftry k f h :=
  (λ o, try (k o) f h).

(* ------------------------------------------------------------------------ *)

(* [bind] is in fact a special case of [try]. We prefer to give a direct
   definition of [bind] anyway, so as to prevent Coq from expanding uses
   of [bind] into more complex expressions that seem to involve [try]. *)

Lemma bind_as_try2 {A B E} (m : micro A E) (f : A → micro B E) :
  bind m f =
  try2 m (glue2 f throw).
Proof.
  induction m; try solve [
    reflexivity
  | simpl; f_equal; extensionality v; eauto ].
Qed.

Lemma bind_as_try {A B E} (m : micro A E) (f : A → micro B E) :
  bind m f =
  try m f throw.
Proof.
  eapply bind_as_try2.
Qed.

(* Since [bind] is a special case of [try], [fmap] can be written in terms of
 [try] as well. *)

Corollary try_as_fmap {A B E} (f : A -> B) (m : micro A E) :
  try m (fun v => ret (f v)) throw =
  fmap f m.
Proof.
  by rewrite <- bind_as_try.
Qed.

Lemma pftry_pffmap {A B C E} (f : A -> B) (k : C -> micro A E) :
  pftry k (fun v => ret (f v)) throw = pffmap f k.
Proof.
  extensionality v.
  intros; apply try_as_fmap.
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_as_try : bind_as_try.
Global Hint Extern 1 (_ = _) => rewrite try_as_fmap : try_as_fmap.

(* ------------------------------------------------------------------------ *)

(* A public combinator: [orelse]. *)

(* [orelse m1 m2] runs [m1] first. If [m1] succeeds, its result is
   transmitted. If [m1] fails, then [m2] is run. *)

Definition orelse {A E} (m1 m2 : micro A E) : micro A E :=
  try m1 ret (λ _, m2).

(* ------------------------------------------------------------------------ *)

(* A public combinator: [widen]. *)

(* A computation that cannot throw an exception can be assigned the
   type [micro _ E] for an arbitrary [E]. This leads to a choice:
   one can either instantiate [E] with the empty type [void] or
   universally quantify over [E]. Put another way, the question
   is where to put the universal quantifier: either [micro _ (∀E.E)]
   or [∀E. micro _ E].

   In general, monomorphic objects can be easier to work with, so
   using the type [micro _ void], where possible, seems preferable.
   However, polymorphic objects are more flexible. In particular,
   when a computation of type [micro _ void] is used in a context
   where exceptions of type [E] may be thrown, this computation
   must be converted to the type [micro _ E]. The coercion [widen]
   is used for this purpose. *)

Definition widen {A E} (m : micro A void) : micro A E :=
  try m ret elim_void.

(* ------------------------------------------------------------------------ *)

(* Paraphrase lemmas. *)

(* TODO Some of these lemmas are unused. Remove them or make them Local. *)

Lemma bind_ret {A B E} (a : A) (f : A → micro B E) :
  bind (ret a) f =
  f a.
Proof.
  reflexivity.
Qed.

Lemma bind_throw {A B E} (e : E) (f : A → micro B E) :
  bind (throw e) f =
  throw e.
Proof.
  reflexivity.
Qed.

Lemma bind_crash {A B E} (f : A → micro B E) :
  bind crash f =
  crash.
Proof.
  reflexivity.
Qed.

Lemma bind_stop {A B E X Y} (c : code X Y E) x k (f : A → micro B E) :
  bind (Stop c x k) f =
  Stop c x (pfbind k f).
Proof.
  reflexivity.
Qed.

Lemma bind_par {A1 A2 A B E' E}
  (m1 : micro A1 E') (m2 : micro A2 E') k (f : A → micro B E) :
  bind (Par m1 m2 k) f =
  Par m1 m2 (pfbind k f).
Proof.
  reflexivity.
Qed.

Lemma bind_choose {A B C E' E}
  (m1 m2 : micro A E') k (f : B → micro C E) :
  bind (Choose m1 m2 k) f =
  Choose m1 m2 (pfbind k f).
Proof.
  reflexivity.
Qed.

(* Analogous laws for [try]. *)

Lemma try_ret {A B E' E} (a : A) (f : A → micro B E) (z : E' → micro B E) :
  try (ret a) f z =
  f a.
Proof.
  reflexivity.
Qed.

Lemma try_throw {A B E' E} (e : E') (f : A → micro B E) (z : E' → micro B E) :
  try (throw e) f z =
  z e.
Proof.
  reflexivity.
Qed.

Lemma try_crash {A B E' E} (f : A → micro B E) (z : E' → micro B E) :
  try crash f z =
  crash.
Proof.
  reflexivity.
Qed.

Lemma try_Stop {A B E' E X Y}
  (c : code X Y E') x k (f : A → micro B E) (h : E' → micro B E) :
  try (Stop c x k) f h =
  Stop c x (pftry k f h).
Proof.
  reflexivity.
Qed.

Lemma try_Par {A1 A2 A B E' E F}
  (m1 : micro A1 E') (m2 : micro A2 E') k
  (f : A → micro B F) (h : E → micro B F) :
  try (Par m1 m2 k) f h =
  Par m1 m2 (pftry k f h).
Proof.
  reflexivity.
Qed.

Lemma try2_Par {A1 A2 A B E' E F}
  (m1 : micro A1 E') (m2 : micro A2 E') k
  (h : outcome2 A E → micro B F) :
  try2 (Par m1 m2 k) h =
  Par m1 m2 (pftry2 k h).
Proof.
  reflexivity.
Qed.

Lemma try_Choose {A B C E' E F}
  (m1 m2 : micro A E') (k : _ → micro B E)
  (f : B → micro C F) (h : E → micro C F) :
  try (Choose m1 m2 k) f h =
  Choose m1 m2 (pftry k f h).
Proof.
  reflexivity.
Qed.

Global Hint Extern 1 (_ = _) => rewrite try_ret : try_ret.

(* TODO the following two lemmas are unused. Keep or discard? *)

Lemma try2_continue {A B C E F G}
  a
  (h : outcome2 A E → micro B F)
  (k : outcome2 B F → micro C G)
:
  try2 (continue h a) k =
  continue (pftry2 h k) a.
Proof.
  reflexivity.
Qed.

Lemma try2_discontinue {A B C E F G}
  e2
  (h : outcome2 A E → micro B F)
  (k : outcome2 B F → micro C G)
:
  try2 (discontinue h e2) k =
  discontinue (pftry2 h k) e2.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This is just an equality of trees. *)

(* We could give an inductive definition of this equality. I prefer to
   accept the law of functional extensionality, which implies that
   the desired equality coincides with Coq's ordinary equality. *)

Lemma eq_handle_handle {A E} m (k1 k2 : _ → micro A E) :
  (∀ o, k1 o = k2 o) →
  Handle m k1 = Handle m k2.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Lemma eq_stop_stop {A E E' X Y} (c : code X Y E') x
  (k1 k2 : outcome2 Y E' → micro A E) :
  (∀ o, k1 o = k2 o) →
  Stop c x k1 = Stop c x k2.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Lemma eq_par_par {A A1 A2 E E'} m1 m2
  (k k' : outcome2 (A1 * A2) E' → micro A E) :
  (∀ o, k o = k' o) →
  Par m1 m2 k = Par m1 m2 k'.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Lemma eq_choose_choose {A B E E'} m1 m2
  (k k' : outcome2 B E' → micro A E) :
  (∀ o, k o = k' o) →
  Choose m1 m2 k = Choose m1 m2 k'.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Local Hint Resolve
  eq_handle_handle eq_stop_stop eq_par_par eq_choose_choose
: eq.

(* ------------------------------------------------------------------------ *)

(* The monad laws. *)

(* [bind_ret] has been proved already. *)

Lemma bind_ret_right :
  ∀ {A E} (m : micro A E),
  bind m ret = m.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try2_ret_right :
  ∀ {A E} (m : micro A E),
  try2 m inject2 = m.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_ret_right :
  ∀ {A E} (m : micro A E),
  try m ret throw = m.
Proof.
  intros. eapply try2_ret_right.
Qed.

Lemma bind_bind {A B C E} (m : micro A E) (f : A → micro B E) (g : B → micro C E) :
  bind (bind m f) g =
  bind m (pfbind f g).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_try2 {A B C E E'}
  m (f : outcome2 A E' → micro B E) (h : B → micro C E) :
  bind (try2 m f) h =
  try2 m (pfbind f h).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_try {A B C E E'}
  m (f : A → micro B E) (z : E' → micro B E) (h : B → micro C E) :
  bind (try m f z) h =
  try m (pfbind f h) (pfbind z h).
Proof.
  unfold try. induction m; simpl; eauto with eq.
Qed.

Lemma try_bind {A B C E E'}
  m (f : A → micro B E') (k : B → micro C E) (z : E' → micro C E) :
  try (bind m f) k z =
  try m (pftry f k z) z.
Proof.
  unfold try. induction m; simpl; eauto with eq.
Qed.

Lemma try_try {A B C E E' E''} (m : micro A E'') (f : A → micro B E') (k : B → micro C E) h z :
  try (try m f h) k z =
  try m (pftry f k z) (pftry h k z).
Proof.
  unfold try. induction m; simpl; eauto with eq.
Qed.

Lemma try2_try2 {A B C E E' E''} (m : micro A E'') (h : _ → micro B E') (k : _ → micro C E) :
  try2 (try2 m h) k =
  try2 m (pftry2 h k).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_bind : bind_bind.
Global Hint Extern 1 (_ = _) => rewrite bind_try : bind_try.
Global Hint Extern 1 (_ = _) => rewrite try_bind : try_bind.
Global Hint Extern 1 (_ = _) => rewrite try_try : try_try.
Global Hint Extern 1 (_ = _) => rewrite try2_try2 : try_try.

Lemma try2_inject2 {A' E' A E} (o : outcome2 A' E') (k : _ → micro A E) :
  try2 (inject2 o) k = k o.
Proof.
  destruct o; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The constructors [Stop], [Par], and [Choose] can be viewed as
   applications of [stop], [par], and [choose],
   wrapped in [try2]. *)

(* TODO [try_stop], etc. may become unused *)

Lemma try2_stop {A X Y E E'} c (x : X) (k : outcome2 Y E' → micro A E) :
  try2 (stop c x) k = Stop c x k.
Proof.
  simpl. eauto using eq_stop_stop, try2_inject2.
Qed.

Lemma try_stop {A X Y E E'} c (x : X) (k : Y → micro A E) (z : E' → micro A E) :
  try (stop c x) k z = Stop c x (glue2 k z).
Proof.
  eapply try2_stop.
Qed.

Lemma try2_par {A1 A2 A E E'} m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
  try2 (par m1 m2) k = Par m1 m2 k.
Proof.
  simpl. eauto using eq_par_par, try2_inject2.
Qed.

Lemma try_par {A1 A2 A E E'} m1 m2 (k : A1 * A2 → micro A E) (z : E' → micro A E) :
  try (par m1 m2) k z = Par m1 m2 (glue2 k z).
Proof.
  eapply try2_par.
Qed.

Lemma try2_choose {A B E E'} m1 m2 (k : outcome2 A E' → micro B E) :
  try2 (choose m1 m2) k = Choose m1 m2 k.
Proof.
  simpl. eauto using eq_choose_choose, try2_inject2.
Qed.

Lemma try_choose {A B E E'} m1 m2 (k : A → micro B E) (z : E' → micro B E) :
  try (choose m1 m2) k z = Choose m1 m2 (glue2 k z).
Proof.
  eapply try2_choose.
Qed.

(* ------------------------------------------------------------------------ *)

(* A 3-way case analysis principle: a computation [m] is either [ret a]
   or [throw e] or something else. *)

Lemma ret_or_throw_or_else {A E} (m : micro A E) :
  (∃ a, m = ret a) ∨
  (∃ e, m = throw e) ∨
  ((∀ a, m = ret a → False) ∧ (∀ e, m = throw e → False)).
Proof.
  destruct m; solve [ eauto | right; right; split; congruence ].
Qed.

(* ------------------------------------------------------------------------ *)

(* The following inversion lemmas extract information out of an equality
   of the form [try m _ _ = ret _], [try m _ _ = Stop _ _ _], and
   [try m _ _ = Par _ _ _]. They provide information about [m]. *)

(* The following lemma exhibits a disjunction in the conclusion.
   A variant of this statement appears below. *)

Lemma invert_try_eq_ret_disj {A B E E' m}
  {k : A → micro B E} {z : E' → micro B E} {b} :
  try m k z = ret b →
  (∃ a, m = ret a /\ k a = ret b) \/
  (∃ e, m = throw e /\ z e = ret b).
Proof.
  unfold try. destruct m; simpl; solve [ congruence | eauto ].
Qed.

Lemma invert_bind_eq_ret {A B E m} {k : A → micro B E} {b} :
  bind m k = ret b ->
  ∃ a, m = ret a /\ k a = ret b.
Proof.
  destruct m; simpl; solve [ congruence | eauto ].
Qed.

(* These lemmas are written in a form where one assumes that [m] is
   not [ret _] or [throw _]. This allows the conclusion to be simple.
   Without this hypothesis, the conclusion of the lemma would have
   to be a disjunction. *)

Lemma invert_try2_eq_ret {A B E E' m}
  {k : outcome2 A E' → micro B E} {b} :
  try2 m k = ret b →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  False.
Proof.
  destruct m; simpl; solve [ congruence | eauto ].
Qed.

Lemma invert_try2_eq_stop
  {A B E E' E'' m} {f : outcome2 A E' → micro B E}
  {X Y} {c : code X Y E''} {x k} :
  try2 m f = Stop c x k →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k',
  m = Stop c x k' ∧
  k = pftry2 k' f.
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try2_eq_stop :=
  match goal with
  | h: try2 _ _ = Stop _ _ ?k |- _ =>
      apply invert_try2_eq_stop in h; [| eauto | eauto ];
      let k' := fresh k in
      destruct h as (k' & ? & ?);
      subst k; rename k' into k
  | h: Stop _ _ _ = try2 _ _ |- _ =>
      symmetry in h;
      invert_try2_eq_stop
  end.

Lemma invert_try2_eq_par {A A1 A2 B E E' E''}
  {m : micro A E'} {f}
  {m1 m2} {k : outcome2 (A1 * A2) E'' → micro B E}
:
  try2 m f = Par m1 m2 k →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k',
  m = Par m1 m2 k' ∧
  k = pftry2 k' f.
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try2_eq_par :=
  match goal with
  | h: try2 _ _ = Par _ _ ?k |- _ =>
      apply invert_try2_eq_par in h; [| eauto | eauto ];
      let k' := fresh k in
      destruct h as (k' & ? & ?);
      subst k; rename k' into k
  | h: Par _ _ _ = try2 _ _ |- _ =>
      symmetry in h;
      invert_try2_eq_par
  end.

Lemma invert_try2_eq_choose {A B C E E' E''}
  {m : micro A E'} {f m1 m2} {k : outcome2 C E'' → micro B E}
:
  try2 m f = Choose m1 m2 k →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k',
  m = Choose m1 m2 k' ∧
  k = pftry2 k' f.
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try2_eq_choose :=
  match goal with
  | h: try2 _ _ = Choose _ _ ?k |- _ =>
      apply invert_try2_eq_choose in h; [| eauto | eauto ];
      let k' := fresh k in
      destruct h as (k' & ? & ?);
      subst k; rename k' into k
  | h: Choose _ _ _ = try2 _ _ |- _ =>
      symmetry in h;
      invert_try2_eq_choose
  end.

Lemma invert_try2_eq_handle
  {A B E E' m} {f : outcome2 A E' → micro B E}
  {e k} :
  try2 m f = Handle e k →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k',
  m = Handle e k' ∧
  k = pftry2 k' f.
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try2_eq_handle :=
  match goal with
  | h: try2 _ _ = Handle _ ?k |- _ =>
      apply invert_try2_eq_handle in h; [| eauto | eauto ];
      let k' := fresh k in
      destruct h as (k' & ? & ?);
      subst k; rename k' into k
  | h: Handle _ _ = try2 _ _ |- _ =>
      symmetry in h;
      invert_try2_eq_handle
  end.
(* -------------------------------------------------------------------------- *)

(* The auxiliary functions [join1 a1] and [join2 a2] transform a two-armed
   handler that expects a pair into one that expects a single component. *)

(* They are used in the definition of the [simp] relation (simplification.v). *)

Definition join1 {A1 A2 B E E'} (a1 : A1)
  (k : outcome2 (A1 * A2) E' → micro B E)
     : outcome2       A2  E' → micro B E
:=
  glue2
    (λ a2, continue k (a1, a2))
    (discontinue k).

Definition join2 {A1 A2 B E E'} (a2 : A2)
  (k : outcome2 (A1 * A2) E' → micro B E)
     : outcome2  A1       E' → micro B E
:=
  glue2
    (λ a1, continue k (a1, a2))
    (discontinue k).

(* Basic properties. *)

Lemma try2_join1 {A1 A2 B E E'} m a1 (k : outcome2 (A1 * A2) E' → micro B E) :
  try2 m (join1 a1 k) =
  try m (λ a2, continue k (a1, a2)) (discontinue k).
Proof.
  reflexivity.
Qed.

Lemma try2_join2 {A1 A2 B E E'} m a2 (k : outcome2 (A1 * A2) E' → micro B E) :
  try2 m (join2 a2 k) =
  try m (λ a1, continue k (a1, a2)) (discontinue k).
Proof.
  reflexivity.
Qed.

Lemma pftry2_join1 {A1 A2 B C E F G}
  a1
  (h : outcome2 (A1 * A2) E → micro B F)
  (k : outcome2 B F → micro C G)
:
  pftry2 (join1 a1 h) k =
  join1 a1 (pftry2 h k).
Proof.
  extensionality o2. destruct o2; reflexivity.
Qed.

Lemma pftry2_join2 {A1 A2 B C E F G}
  a2
  (h : outcome2 (A1 * A2) E → micro B F)
  (k : outcome2 B F → micro C G)
:
  pftry2 (join2 a2 h) k =
  join2 a2 (pftry2 h k).
Proof.
  extensionality o1. destruct o1; reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* Match whether a computation [e] is an [outcome2], returning an [outcome2] if
  so. *)

(* This is used in the definition of the [ewp] weakest precondition in [ewp.v]. *)

Definition outcome2_opt {A E} (e : micro A E): option (outcome2 A E) :=
  match e with
  | Ret a => Some (O2Ret a)
  | Throw e => Some (O2Throw e)
  | _ => None
  end.

Lemma outcome2_opt_inject2 {A E} (v : outcome2 A E) :
  outcome2_opt (inject2 v) = Some v.
Proof.
  destruct v; auto.
Qed.

End Make.
