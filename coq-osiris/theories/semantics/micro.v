From Coq.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.

(* This module defines a meta-language (a monad) within which one can
   implement an interpreter for an object language (such as OCaml). *)

(* ------------------------------------------------------------------------ *)

(* The monad is parameterized over a type constructor [code], which describes
   a set of services that a computation can request from the runtime system.
   These services can also be thought of as "system calls" that a computation
   can make. A value of type [code X Y E] represents the name of a system call
   whose parameter has type [X], whose result has type [Y], and which can
   throw an exception of type [E]. *)

Module Type CODE.
  Parameter code : Type → Type → Type → Type.
End CODE.

Module Make (C : CODE).

Import C. (* We write [code] for [C.code]. *)

(* ------------------------------------------------------------------------ *)

(* The abstract API of this micro monad is as follows:

   [return] and [bind] have their usual meaning.

   [try m f h] runs the computation [m]. If [m] returns a result [a] then the
   computation [f a] is executed. If [m] ends with an exception [throw e],
   then the computation [h e] is executed.

   [crash] is a hard failure. It represents a crash and cannot be caught.

   [throw e] causes a soft failure. One can think of it as an exception.
   This exception can be caught and handled using [try].

   [stop c x] is a "system call", that is, a request for an external service.
   The code (i.e., the name) of the system call is [c] and its argument is
   [x]. The code [c] has type [code X Y], for some types [X] and [Y]. The
   parameter [x] has type [X], and the result of the system call has type [Y].
   Throughout this file, the type family [code] is a parameter.

   [par m1 m2] is a parallel evaluation construct. It evaluates [m1] and [m2]
   independently and in parallel. If the two computations have side effects
   (via system calls) then these effects are interleaved in a nondeterministic
   manner. If both computations succeed and return two results [v1] and [v2],
   then [par m1 m2] returns the pair [(v1, v2)]. If either computation
   crashes, then [par m1 m2] crashes. If either computation raises an
   exception, then [par m1 m2] raises this exception is transmitted
   upwards.

   [choose m1 m2] is a non-deterministic choice between the computations [m1]
   and [m2]. One of them is executed; the other is discarded. *)

(* The type [micro A] is inductive: every computation terminates.
   Non-terminating computations can be represented, but must (infinitely
   often) pause by performing a [stop] effect. *)

(* Internally, [bind] is just a special case of [try], and [try] itself is not
   a constructor; instead, the constructors [Stop], [Par] and [Choose] contain
   a built-in [try], with two continuations: a normal continuation [k] and an
   exceptional continuation [z]. This can be viewed as an implementation
   detail, but this information does leak if one lets Coq reduce computations
   to a normal form. *)

(* The constructor [Stop] is similar to the constructor [Vis] of interaction
   trees. The type code is similar to an effect signature. *)

Inductive micro A E :=
  | Ret (a : A)
  | Throw (e : E)
  | Crash
  | Stop {X Y E'}
      (c : code X Y E') (x : X)
      (k : Y → micro A E)
      (z : E' → micro A E)
  | Par {A1 A2 E'}
      (m1 : micro A1 E') (m2 : micro A2 E')
      (k : A1 * A2 → micro A E)
      (z : E' → micro A E)
  | Choose {B E'}
      (m1 m2 : micro B E')
      (k : B → micro A E)
      (z : E' → micro A E)
.

(* Make [A] an implicit argument of the constructors. *)

Arguments Ret    {A E}.
Arguments Throw  {A E}.
Arguments Crash  {A E}.
Arguments Stop   {A E X Y E'} c x k z.
Arguments Par    {A E A1 A2 E'} m1 m2 k z.
Arguments Choose {A E B E'} m1 m2 k z.

(* ------------------------------------------------------------------------ *)

(* Let the user view some of the constructors as combinators. *)

Notation ret :=
  (Ret).

Notation throw :=
  (Throw).

Notation crash :=
  (Crash).

(* [stop c x] stops, and, once restarted, behaves like the computation
   denoted by the code [c] applied to the argument [x]. The mapping of
   codes to computations is not defined here; it must be supplied a
   posteriori (step.v). *)

Definition stop {X Y E} (c : code X Y E) x : micro Y E :=
  (Stop c x ret throw).

(* [par m1 m2] runs the computations [m1] and [m2] in parallel,
   producing a pair of results. *)

Definition par {A1 A2 E} (m1 : micro A1 E) (m2 : micro A2 E)
: micro (A1 * A2) E :=
  Par m1 m2 ret throw.

(* [choose m1 m2] performs a non-deterministic choice between [m1] and
   [m2] and runs the chosen computation, producing a single result. *)

Definition choose {A E} (m1 m2 : micro A E) : micro A E :=
  Choose m1 m2 ret throw.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators: [try] and [bind]. *)

(* [bind m f] sequences the computations [m] and [f]. *)

(* The definition of [bind] involves a duplication of [f] in the cases of
   [Stop], [Par], and [Choose]. So it is likely that this monad is not
   suitable for efficient executions of large computations inside Coq. *)

Fixpoint bind {A B E} (m : micro A E) (f : A → micro B E) : micro B E :=
  match m with
  | Ret a =>
      f a
  | Throw e =>
      (* An exception is transmitted. *)
      Throw e
  | Crash =>
      (* A hard failure is transmitted. *)
      Crash
  | Stop c x k z =>
      (* A [Stop] effect is transmitted. The handler [bind _ f] remains
         installed on top of the continuations. *)
      Stop c x (λ y, bind (k y) f) (λ y, bind (z y) f)
  | Par m1 m2 k z =>
      (* Same here. *)
      Par m1 m2 (λ y, bind (k y) f) (λ y, bind (z y) f)
  | Choose m1 m2 k z =>
      (* Same here. *)
      Choose m1 m2 (λ y, bind (k y) f) (λ y, bind (z y) f)
  end.

Global Arguments bind A B E !m f : simpl nomatch.

(* [try m f h] runs the computation [m]. If [m] returns a result [a] then the
   computation [f a] is executed. If [m] ends with an exception [throw e] then
   the computation [h e] is executed. *)

Fixpoint try {A B E' E} (m : micro A E') (f : A → micro B E) (h : E' → micro B E) : micro B E :=
  match m with
  | Ret a =>
      f a
  | Throw e =>
      (* An exception is handled by [h]. *)
      h e
  | Crash =>
      Crash
  | Stop c x k z =>
      (* A [Stop] effect is transmitted. The handler [try _ f h] remains
         installed on top of the continuations. *)
      Stop c x (λ y, try (k y) f h) (λ y, try (z y) f h)
  | Par m1 m2 k z =>
      (* Same here. The handler [try _ f h] remains installed on top of
         both continuations. *)
      Par m1 m2 (λ y, try (k y) f h) (λ y, try (z y) f h)
  | Choose m1 m2 k z =>
      Choose m1 m2 (λ y, try (k y) f h) (λ y, try (z y) f h)
  end.

(* ------------------------------------------------------------------------ *)

(* [bind] is in fact a special case of [try]. We prefer to give a direct
   definition of [bind] anyway, so as to prevent Coq from expanding uses
   of [bind] into more complex expressions that seem to involve [try]. *)

Lemma bind_as_try {A B E} (m : micro A E) (f : A → micro B E) :
  bind m f =
  try m f throw.
Proof.
  induction m; try solve [
    reflexivity
  | simpl; f_equal; extensionality v; eauto ].
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_as_try : bind_as_try.

(* ------------------------------------------------------------------------ *)

(* [orelse m1 m2] runs [m1] first. If [m1] succeeds, its result is
   transmitted. If [m1] fails, then [m2] is run. *)

Definition orelse {A E} (m1 m2 : micro A E) : micro A E :=
  try m1 ret (λ _, m2).

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

Lemma bind_stop {A B E X Y} (c : code X Y E) x k z (f : A → micro B E) :
  bind (Stop c x k z) f =
  Stop c x (λ y, bind (k y) f) (λ y, bind (z y) f).
Proof.
  reflexivity.
Qed.

Lemma bind_par {A1 A2 A B E' E}
  m1 m2 (k : A1 * A2 → micro A E) (z : E' → micro A E)
  (f : A → micro B E) :
  bind (Par m1 m2 k z) f =
  Par m1 m2 (λ v, bind (k v) f) (λ y, bind (z y) f).
Proof.
  reflexivity.
Qed.

Lemma bind_choose {A B C E' E}
  m1 m2 (k : A → micro B E) (z : E' → micro B E) (f : B → micro C E) :
  bind (Choose m1 m2 k z) f =
  Choose m1 m2 (λ a, bind (k a) f) (λ a, bind (z a) f).
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
  (c : code X Y E') x k z (f : A → micro B E) (h : E' → micro B E) :
  try (Stop c x k z) f h =
  Stop c x (λ y, try (k y) f h) (λ y, try (z y) f h).
Proof.
  reflexivity.
Qed.

Lemma try_Par {A1 A2 A B E' E F}
  m1 m2 (k : A1 * A2 → micro A E) (z : E' → micro A E)
  (f : A → micro B F) (z' : E → micro B F) :
  try (Par m1 m2 k z) f z' =
  Par m1 m2 (λ v, try (k v) f z') (λ y, try (z y) f z').
Proof.
  reflexivity.
Qed.

Lemma try_Choose {A B C E' E F} m1 m2 (k : B → micro A E) (z : E' → micro A E) (k' : A → micro C F) (z' : E → micro C F) :
  try (Choose m1 m2 k z) k' z' =
  Choose m1 m2 (λ a, try (k a) k' z') (λ a, try (z a) k' z').
Proof.
  reflexivity.
Qed.

Global Hint Extern 1 (_ = _) => rewrite try_ret : try_ret.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This is just an equality of trees. *)

(* We could give an inductive definition of this equality. I prefer to
   accept the law of functional extensionality, which implies that
   the desired equality coincides with Coq's ordinary equality. *)

Lemma eq_stop_stop {A E E' X Y} (c : code X Y E') x
  (k1 k2 : Y → micro A E) (z1 z2 : E' → micro A E) :
  (∀ v, k1 v = k2 v) →
  (∀ e, z1 e = z2 e) →
  Stop c x k1 z1 = Stop c x k2 z2.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Lemma eq_par_par {A A1 A2 E E'} m1 m2
  (k k' : A1 * A2 → micro A E) (z z' : E' → micro A E) :
  (∀ v, k v = k' v) →
  (∀ e, z e = z' e) →
  Par m1 m2 k z = Par m1 m2 k' z'.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Lemma eq_choose_choose {A B E E'} m1 m2
  (k k' : B → micro A E) (z z' : E' → micro A E) :
  (∀ v, k v = k' v) →
  (∀ e, z e = z' e) →
  Choose m1 m2 k z = Choose m1 m2 k' z'.
Proof.
  intros. f_equal; eauto using functional_extensionality.
Qed.

Local Hint Resolve eq_stop_stop eq_par_par eq_choose_choose : eq.

(* ------------------------------------------------------------------------ *)

(* The monad laws. *)

(* [bind_ret] has been proved already. *)

Lemma bind_ret_right :
  ∀ {A E} (m : micro A E),
  bind m ret = m.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_ret_right :
  ∀ {A E} (m : micro A E),
  try m ret throw = m.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_bind {A B C E} (m : micro A E) (f : A → micro B E) (g : B → micro C E) :
  bind (bind m f) g =
  bind m (λ a, bind (f a) g).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_try {A B C E E'}
  m (f : A → micro B E) (z : E' → micro B E) (h : B → micro C E) :
  bind (try m f z) h =
  try m (λ a, bind (f a) h) (λ y, bind (z y) h).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_bind {A B C E E'}
  m (f : A → micro B E') (k : B → micro C E) (z : E' → micro C E) :
  try (bind m f) k z =
  try m (λ y, try (f y) k z) z.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_try {A B C E E' E''} (m : micro A E'') (f : A → micro B E') (k : B → micro C E) h z :
  try (try m f h) k z =
  try m (λ y, try (f y) k z) (λ y, try (h y) k z).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_bind : bind_bind.
Global Hint Extern 1 (_ = _) => rewrite bind_try : bind_try.
Global Hint Extern 1 (_ = _) => rewrite try_bind : try_bind.
Global Hint Extern 1 (_ = _) => rewrite try_try : try_try.

(* ------------------------------------------------------------------------ *)

(* The constructors [Stop], [Par], and [Choose] can be viewed as
   applications of [stop], [par], and [choose],
   wrapped in a [try] construct. *)

Lemma try_stop {A X Y E E'} c (x : X) (k : Y → micro A E) (z : E' → micro A E) :
  try (stop c x) k z = Stop c x k z.
Proof.
  simpl try. eauto using eq_stop_stop.
Qed.

Lemma try_par {A1 A2 A E E'} m1 m2 (k : A1 * A2 → micro A E) (z : E' → micro A E) :
  try (par m1 m2) k z = Par m1 m2 k z.
Proof.
  simpl try. eauto using eq_par_par.
Qed.

Lemma try_choose {A B E E'} m1 m2 (k : A → micro B E) (z : E' → micro B E) :
  try (choose m1 m2) k z = Choose m1 m2 k z.
Proof.
  simpl try. eauto using eq_choose_choose.
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
   of the form [try m _ _ = ret _], [try m _ _ = Stop _ _ _ _], and
   [try m _ _ = Par _ _ _ _]. They provide information about [m]. *)

(* These lemmas are written in a form where one assumes that [m] is
   not [ret _] or [throw _]. This allows the conclusion to be simple.
   Without this hypothesis, the conclusion of the lemma would have
   to be a 3-way disjunction. *)

Lemma invert_try_eq_ret {A B E E' m}
  {k : A → micro B E} {z : E' → micro B E} {b} :
  try m k z = ret b →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  False.
Proof.
  destruct m; simpl; solve [ congruence | eauto ].
Qed.

Lemma invert_try_eq_stop
  {A B E E' E'' m} {f : A → micro B E} {h : E' → micro B E}
  {X Y} {c : code X Y E''} {x k z} :
  try m f h = Stop c x k z →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k' z',
  m = Stop c x k' z' ∧
  k = (λ y, try (k' y) f h) ∧
  z = (λ y, try (z' y) f h).
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try_eq_stop :=
  match goal with
  | h: try _ _ _ = Stop _ _ ?k ?z |- _ =>
      apply invert_try_eq_stop in h; [| eauto | eauto ];
      let k' := fresh k in
      let z' := fresh z in
      destruct h as (k' & z' & ? & ? & ?);
      subst k; subst z; rename k' into k; rename z' into z
  | h: Stop _ _ _ _ = try _ _ _ |- _ =>
      symmetry in h;
      invert_try_eq_stop
  end.

Lemma invert_try_eq_par {A A1 A2 B E E' E''}
  {m : micro A E'} {f h}
  {m1 m2} {k : A1 * A2 → micro B E} {z : E'' → micro B E}
:
  try m f h = Par m1 m2 k z →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k' z',
  m = Par m1 m2 k' z' ∧
  k = (λ y, try (k' y) f h) ∧
  z = (λ y, try (z' y) f h).
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try_eq_par :=
  match goal with
  | h: try _ _ _ = Par _ _ ?k ?z |- _ =>
      apply invert_try_eq_par in h; [| eauto | eauto ];
      let k' := fresh k in
      let z' := fresh z in
      destruct h as (k' & z' & ? & ? & ?);
      subst k; subst z; rename k' into k; rename z' into z
  | h: Par _ _ _ _ = try _ _ _ |- _ =>
      symmetry in h;
      invert_try_eq_par
  end.

Lemma invert_try_eq_choose {A B C E E' E''}
  {m : micro A E'} {f h m1 m2} {k : C → micro B E} {z : E'' → micro B E}
:
  try m f h = Choose m1 m2 k z →
  (∀ a, m = ret a → False) →
  (∀ e, m = throw e → False) →
  ∃ k' z',
  m = Choose m1 m2 k' z' ∧
  k = (λ y, try (k' y) f h) ∧
  z = (λ y, try (z' y) f h).
Proof.
  destruct m; simpl; try solve [ congruence | intros; exfalso; eauto ].
  intros H. dependent destruction H.
  intros _ _. eauto.
Qed.

Ltac invert_try_eq_choose :=
  match goal with
  | h: try _ _ _ = Choose _ _ ?k ?z |- _ =>
      apply invert_try_eq_choose in h; [| eauto | eauto ];
      let k' := fresh k in
      let z' := fresh z in
      destruct h as (k' & z' & ? & ? & ?);
      subst k; subst z; rename k' into k; rename z' into z
  | h: Choose _ _ _ _ = try _ _ _ |- _ =>
      symmetry in h;
      invert_try_eq_choose
  end.

(* ------------------------------------------------------------------------ *)

End Make.
