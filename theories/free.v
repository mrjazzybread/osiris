From Coq.Logic Require Import FunctionalExtensionality.
Require Import base.

Section Free.

(* ------------------------------------------------------------------------ *)

(* A free monad. *)

(* The custom constructors of this free monad are:

   - [Fail], a hard failure, which represents a crash and cannot be
     caught;

   - [Next], a soft failure, which can be caught by a [try]
     combinator;

   - [Stop c x k], a request to evaluate a computation whose code is
     [c], with argument [x], producing a result which the continuation
     [k] consumes;

   - [Par m1 m2 k ko], a parallel evaluation construct, which
     evaluates [m1] and [m2] independently. If both computations
     succeed and return two results [v1] and [v2], then the
     continuation [k] is applied to the pair [(v1, v2)]. If either
     computation causes a hard failure, this hard failure is
     transmitted upwards. If either computation causes a soft failure,
     then the failure continuation [ko] is invoked.

   The code [c] carried in [Stop c x k] has type [code X Y], for some
   types [X] and [Y]. The parameter [x] has type [X], and the
   continuation [k] expects a value of type [Y]. Throughout this file,
   the type family [code] is a parameter. The constructor [Stop] is
   similar to the constructor [Vis] of interaction trees, and the type
   code is similar to an effect signature [E].

   The fact that [Stop] does not carry a second continuation
   (which would be a soft failure continuation) reflects
   a convention that the computation denoted by a code
   is not allowed to raise a soft failure.

   The type [free A] is inductive: every computation terminates.
   Non-terminating computations can be represented, but must
   (infinitely often) pause by performing a [Stop] effect. *)

Context {code : Type → Type → Type}.

Inductive free A :=
  | Ret (a : A)
  | Fail
  | Next
  | Stop {X Y} (c : code X Y) (x : X) (k : Y → free A)
  | Par {A1 A2} (m1 : free A1) (m2 : free A2)
                (k : A1 * A2 → free A)
                (ko : unit → free A)
.

(* Make [A] an implicit argument of the constructors. *)

Arguments Ret  {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A X Y} c x k.
Arguments Par  {A A1 A2} m1 m2 k ko.

(* ------------------------------------------------------------------------ *)

(* Let the user view some of the constructors as combinators. *)

Notation ret :=
  (Ret).

Notation fail :=
  (Fail).

Notation next :=
  (λ tt, Next).

(* [stop c x] stops, and, once restarted, behaves like the computation
   denoted by the code [c] applied to the argument [x]. The mapping of
   codes to computations is not defined here; it must be supplied a
   posteriori (step.v). *)

Definition stop {X Y} (c : code X Y) (x : X) : free Y :=
  Stop c x ret.

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
  | Fail =>
      (* A hard failure is transmitted. *)
      Fail
  | Next =>
      (* A soft failure is transmitted. *)
      Next
  | Stop c x k =>
      (* A [Stop] effect is transmitted. The handler [bind _ f] remains
         installed on top of the continuation. *)
      Stop c x (λ v, bind (k v) f)
  | Par m1 m2 k ko =>
      (* Same here. *)
      Par m1 m2 (λ v, bind (k v) f) (λ tt, bind (ko()) f)
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
  | Fail =>
      Fail
  | Next =>
      (* A soft failure is handled by [g]. *)
      g()
  | Stop c x k =>
      (* A [Stop] effect is transmitted. The handler [try _ f g] remains
         installed on top of the continuation. Because [eval η e] cannot
         cause a soft failure, there is only one continuation. TODO fix *)
      Stop c x (λ v, try (k v) f g)
  | Par m1 m2 k ko =>
      (* Same here. The handler [try _ f g] remains installed on top of
         both continuations. *)
      Par m1 m2 (λ v, try (k v) f g) (λ tt, try (ko()) f g)
  end.

(* [orelse m1 m2] runs [m1] first. If [m1] succeeds, its result is
   transmitted. If [m1] fails, then [m2] is run. *)

Definition orelse {A} (m1 m2 : free A) : free A :=
  try m1 ret (λ tt, m2).

(* This is a monad. *)

(* Global Instance free_mret : MRet free :=
  { mret := @Ret }.

Global Instance free_mbind : MBind free :=
   { mbind := λ {A B} (f : A → free B) (m : free A), bind m f }. *)


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

(* ------------------------------------------------------------------------ *)

(* Paraphrase lemmas. *)

Lemma bind_ret {A B} (a : A) (f : A → free B) :
  bind (Ret a) f =
  f a.
Proof.
  reflexivity.
Qed.

Lemma bind_fail {A B} (f : A → free B) :
  bind Fail f =
  Fail.
Proof.
  reflexivity.
Qed.

Lemma bind_next {A B} (f : A → free B) :
  bind Next f =
  Next.
Proof.
  reflexivity.
Qed.

Lemma bind_stop {A B X Y} (c : code X Y) x k (f : A → free B) :
  bind (Stop c x k) f =
  Stop c x (λ v, bind (k v) f).
Proof.
  reflexivity.
Qed.

Lemma bind_par {A1 A2 A B} m1 m2 (k : A1 * A2 → free A) ko (f : A → free B) :
  bind (Par m1 m2 k ko) f =
  Par m1 m2 (λ v, bind (k v) f) (λ tt, bind (ko()) f).
Proof.
  reflexivity.
Qed.

(* Special cases that involve the [par] combinator. *)

Lemma try_par_comb {A1 A2 A} (m1 : free A1) (m2 : free A2)
  (f : A1 * A2 → free A) (g : unit → free A) :
  try (par m1 m2) f g =
  Par m1 m2 f g.
Proof.
  simpl. f_equal. extensionality tt. destruct tt. reflexivity.
Qed.

Lemma bind_par_comb {A1 A2 A} (m1 : free A1) (m2 : free A2) (f : A1 * A2 → free A) :
  bind (par m1 m2) f =
  Par m1 m2 f next.
Proof.
  rewrite bind_as_try, try_par_comb. reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This equality is just equality of trees whose internal nodes are the
   [Stop] nodes and whose leaves are [Ret], [Fail] and [Next]. *)

(* We could give an inductive definition of this equality. I prefer to
   accept the law of functional extensionality, which implies that
   the desired equality coincides with Coq's ordinary equality. *)

Lemma eq_stop_stop A X Y (k1 k2 : Y → free A) (c : code X Y) x :
  (∀ v, k1 v = k2 v) →
  Stop c x k1 = Stop c x k2.
Proof.
  intros. f_equal. extensionality v. eauto.
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

Lemma ret_bind {A} (m : free A) :
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

(* ------------------------------------------------------------------------ *)

End Free.

(* Recreate some things that are lost when the section is closed. *)

Notation ret :=
  (Ret).

Notation fail :=
  (Fail).

Definition next {code A} : unit → @free code A :=
  (λ tt, @Next code A).

Arguments Ret  {code A}.
Arguments Fail {code A}.
Arguments Next {code A}.
Arguments Stop {code A X Y} c x k.
Arguments Par  {code A A1 A2} m1 m2 k ko.

(* ------------------------------------------------------------------------ *)

(* The left-arrow notation, analogous to Haskell's do notation. *)

Notation "x ← y ; z" :=
  (bind y (λ x, z)).

Notation "' x ← y ; z" :=
  (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200).
