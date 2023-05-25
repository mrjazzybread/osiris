From Coq.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.

(* This module defines a meta-language (a monad) within which one can
   implement an interpreter for an object language (such as OCaml). *)

(* ------------------------------------------------------------------------ *)

(* The monad is parameterized over a type constructor [code], which describes
   a set of services that a computation can request from the runtime system.
   These services can also be thought of as "system calls" that a computation
   can make. A value of type [code X Y] represents the name of a system call
   whose parameter has type [X] and whose result has type  [Y]. *)

Module Type CODE.
  Parameter code : Type → Type → Type.
End CODE.

Module Make (C : CODE).

Import C. (* We write [code] for [C.code]. *)

(* ------------------------------------------------------------------------ *)

(* The custom constructors of this free monad are:

   - [Crash], a hard failure, which represents a crash and cannot be
     caught;

   - [Next], a soft failure, which can be caught by a [try]
     combinator;

   - [Stop c x k ko], a request to evaluate a computation whose code is
     [c], with argument [x], producing either a normal result, which the
     success continuation [k] consumes, or [Next], in which case the
     failure continuation [ko] is invoked;

   - [Par m1 m2 k ko], a parallel evaluation construct, which
     evaluates [m1] and [m2] independently. If both computations
     succeed and return two results [v1] and [v2], then the
     continuation [k] is applied to the pair [(v1, v2)]. If either
     computation causes a hard failure, this hard failure is
     transmitted upwards. If either computation causes a soft failure,
     then the failure continuation [ko] is invoked.

   The code [c] carried in [Stop c x k ko] has type [code X Y], for some
   types [X] and [Y]. The parameter [x] has type [X], and the
   continuation [k] expects a value of type [Y]. Throughout this file,
   the type family [code] is a parameter. The constructor [Stop] is
   similar to the constructor [Vis] of interaction trees, and the type
   code is similar to an effect signature [E].

   The type [free A] is inductive: every computation terminates.
   Non-terminating computations can be represented, but must
   (infinitely often) pause by performing a [Stop] effect. *)

Inductive free A :=
  | Ret (a : A)
  | Crash
  | Next
  | Stop {X Y}
      (c : code X Y) (x : X) (k : Y → free A) (ko : unit → free A)
  | Par {A1 A2}
      (m1 : free A1) (m2 : free A2)
      (k : A1 * A2 → free A)
      (ko : unit → free A)
.

(* Make [A] an implicit argument of the constructors. *)

Arguments Ret  {A}.
Arguments Crash {A}.
Arguments Next {A}.
Arguments Stop {A X Y} c x k ko.
Arguments Par  {A A1 A2} m1 m2 k ko.

(* ------------------------------------------------------------------------ *)

(* Let the user view some of the constructors as combinators. *)

Notation ret :=
  (Ret).

Notation crash :=
  (Crash).

Notation next :=
  (λ tt, Next).

(* [stop c x] stops, and, once restarted, behaves like the computation
   denoted by the code [c] applied to the argument [x]. The mapping of
   codes to computations is not defined here; it must be supplied a
   posteriori (step.v). *)

Notation stop c x :=
  (Stop c x ret next).

(* [par m1 m2] runs the computations [m1] and [m2] in parallel,
   producing a pair of results. *)

Definition par {A1 A2} (m1 : free A1) (m2 : free A2) : free (A1 * A2) :=
  Par m1 m2 ret next.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators: [try] and [bind]. *)

(* [bind m f] sequences the computations [m] and [f]. *)

Fixpoint bind {A B} (m : free A) (f : A → free B) : free B :=
  match m with
  | Ret a =>
      f a
  | Crash =>
      (* A hard failure is transmitted. *)
      Crash
  | Next =>
      (* A soft failure is transmitted. *)
      Next
  | Stop c x k ko =>
      (* A [Stop] effect is transmitted. The handler [bind _ f] remains
         installed on top of the continuations. *)
      Stop c x (λ y, bind (k y) f) (λ y, bind (ko y) f)
  | Par m1 m2 k ko =>
      (* Same here. *)
      Par m1 m2 (λ y, bind (k y) f) (λ y, bind (ko y) f)
  end.

Global Arguments bind A B !m f : simpl nomatch.

(* [try m f g] runs the computation [m]. If [m] returns a result [v], then
   [f v] is executed. If [m] ends with a soft failure [Next], then [g()] is
   executed. *)

(* [g] must have type [unit → mon B], as opposed to just [mon B], because
   we execute monadic computations (in Coq) using call-by-value evaluation
   and we do not want to evaluate ALL branches in a [match] construct. *)

Fixpoint try {A B} (m : free A) (f : A → free B) (g : unit → free B) : free B :=
  match m with
  | Ret a =>
      f a
  | Crash =>
      Crash
  | Next =>
      (* A soft failure is handled by [g]. *)
      g()
  | Stop c x k ko =>
      (* A [Stop] effect is transmitted. The handler [try _ f g] remains
         installed on top of the continuations. *)
      Stop c x (λ y, try (k y) f g) (λ y, try (ko y) f g)
  | Par m1 m2 k ko =>
      (* Same here. The handler [try _ f g] remains installed on top of
         both continuations. *)
      Par m1 m2 (λ y, try (k y) f g) (λ y, try (ko y) f g)
  end.

(* [orelse m1 m2] runs [m1] first. If [m1] succeeds, its result is
   transmitted. If [m1] fails, then [m2] is run. *)

Definition orelse {A} (m1 m2 : free A) : free A :=
  try m1 ret (λ tt, m2).

(* This is a monad. *)

(* [bind] is in fact a special case of [try]. We prefer to give a direct
   definition of [bind] anyway, so as to prevent Coq from expanding uses
   of [bind] into more complex expressions that seem to involve [try]. *)

Lemma bind_as_try {A B} (m : free A) (f : A → free B) :
  bind m f =
  try m f next.
Proof.
  induction m; try solve [
    reflexivity
  | simpl; f_equal; extensionality v; eauto ].
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_as_try : bind_as_try.

(* ------------------------------------------------------------------------ *)

(* Paraphrase lemmas. *)

Lemma bind_ret {A B} (a : A) (f : A → free B) :
  bind (Ret a) f =
  f a.
Proof.
  reflexivity.
Qed.

Lemma bind_crash {A B} (f : A → free B) :
  bind Crash f =
  Crash.
Proof.
  reflexivity.
Qed.

Lemma bind_next {A B} (f : A → free B) :
  bind Next f =
  Next.
Proof.
  reflexivity.
Qed.

Lemma bind_stop {A B X Y} (c : code X Y) x k ko (f : A → free B) :
  bind (Stop c x k ko) f =
  Stop c x (λ y, bind (k y) f) (λ y, bind (ko y) f).
Proof.
  reflexivity.
Qed.

Lemma bind_par {A1 A2 A B} m1 m2 (k : A1 * A2 → free A) ko (f : A → free B) :
  bind (Par m1 m2 k ko) f =
  Par m1 m2 (λ v, bind (k v) f) (λ y, bind (ko y) f).
Proof.
  reflexivity.
Qed.

(* Analogous laws for [try]. *)

Lemma try_ret {A B} (a : A) (f : A → free B) (ko : unit → free B) :
  try (Ret a) f ko =
  f a.
Proof.
  reflexivity.
Qed.

Lemma try_crash {A B} (f : A → free B) (ko : unit → free B) :
  try Crash f ko =
  Crash.
Proof.
  reflexivity.
Qed.

Lemma try_next {A B} (f : A → free B) (ko : unit → free B) :
  try Next f ko =
  ko().
Proof.
  reflexivity.
Qed.

Lemma try_stop {A B X Y} (c : code X Y) x k ko (f : A → free B) ko' :
  try (Stop c x k ko) f ko' =
  Stop c x (λ y, try (k y) f ko') (λ y, try (ko y) f ko').
Proof.
  reflexivity.
Qed.

Lemma try_par {A1 A2 A B} m1 m2 (k : A1 * A2 → free A) ko (f : A → free B) ko' :
  try (Par m1 m2 k ko) f ko' =
  Par m1 m2 (λ v, try (k v) f ko') (λ y, try (ko y) f ko').
Proof.
  reflexivity.
Qed.

Global Hint Extern 1 (_ = _) => rewrite try_ret : try_ret.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This equality is just equality of trees whose internal nodes are the
   [Stop] nodes and whose leaves are [Ret], [Crash] and [Next]. *)

(* We could give an inductive definition of this equality. I prefer to
   accept the law of functional extensionality, which implies that
   the desired equality coincides with Coq's ordinary equality. *)

Lemma eq_stop_stop A X Y (k1 k2 : Y → free A) (c : code X Y) x ko1 ko2 :
  (∀ v, k1 v = k2 v) →
  (∀ y, ko1 y = ko2 y) →
  Stop c x k1 ko1 = Stop c x k2 ko2.
Proof.
  intros. f_equal; extensionality v; eauto.
Qed.

Lemma eq_par_par {A A1 A2} (m1 : free A1) (m2 : free A2)
  (k k' : A1 * A2 → free A) (ko ko' : unit → free A) :
  (∀ v, k v = k' v) →
  ko() = ko'() →
  Par m1 m2 k ko = Par m1 m2 k' ko'.
Proof.
  intros. f_equal.
  { extensionality v. eauto. }
  { extensionality tt. destruct tt. eauto. }
Qed.

Local Hint Resolve eq_stop_stop eq_par_par : eq.

(* ------------------------------------------------------------------------ *)

(* The monad laws. *)

(* [bind_ret] has been proved already. *)

Lemma bind_ret_right :
  ∀ {A} (m : free A),
  bind m Ret = m.
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_bind {A B C} (m : free A) (f : A → free B) (g : B → free C) :
  bind (bind m f) g =
  bind m (λ a, bind (f a) g).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma bind_try {A B C} (m : free A) (f : A → free B) (g : B → free C) ko :
  bind (try m f ko) g =
  try m (λ a, bind (f a) g) (λ y, bind (ko y) g).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_bind {A B C} (m : free A) (f : A → free B) (g : B → free C) ko :
  bind (try m f ko) g =
  try m (λ y, bind (f y) g) (λ y, bind (ko y) g).
Proof.
  induction m; simpl; eauto with eq.
Qed.

Lemma try_try {A B C} (m : free A) (f : A → free B) (g : B → free C) ko ko' :
  try (try m f ko) g ko' =
  try m (λ y, try (f y) g ko') (λ y, try (ko y) g ko').
Proof.
  induction m; simpl; eauto with eq.
Qed.

Global Hint Extern 1 (_ = _) => rewrite bind_bind : bind_bind.
Global Hint Extern 1 (_ = _) => rewrite bind_try : bind_try.
Global Hint Extern 1 (_ = _) => rewrite try_bind : try_bind.
Global Hint Extern 1 (_ = _) => rewrite try_try : try_try.

(* ------------------------------------------------------------------------ *)

End Make.
