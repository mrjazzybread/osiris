From Coq.Logic Require Import FunctionalExtensionality.
Require Import monads lang.

(* ------------------------------------------------------------------------ *)

(* A free monad in which the evaluator is expressed. *)

(* The custom constructors of this free monad are:

   - [Fail],
     a hard failure, which represents a crash and cannot be caught;

   - [Next],
     a soft failure, which can be caught by a [try] combinator;

   - [Stop η e k],
     a request to evaluate expression [e] under environment [η],
     producing a value, which the continuation [k] consumes;

   - [Flip k],
     a non-deterministic coin flip, producing a Boolean result,
     which the continuation [k] consumes;

   - [Par m1 m2 k ko],
     a parallel evaluation construct,
     which evaluates [m1] and [m2] independently.
     If both computations succeed and return two results [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)].
     If either computation causes a hard failure,
     this hard failure is transmitted upwards.
     If either computation causes a soft failure,
     then the failure continuation [ko] is invoked.

   The fact that [Stop] and [Flip] do not carry a second continuation
   (which would be a soft failure continuation) reflect the fact that
   [eval] and [flip] cannot raise a soft failure.

   The type [mon A] is inductive: every computation terminates.
   Non-terminating computations can be represented, but must
   (infinitely often) pause by performing a [Stop] effect. *)

Inductive free A :=
  | Ret (a : A)
  | Fail
  | Next
  | Stop (η : env) (e : expr) (k : val → free A)
  | Flip (k : bool → free A)
  | Par {A1 A2} (m1 : free A1) (m2 : free A2)
                (k : A1 * A2 → free A)
                (ko : unit → free A)
.

(* Make [A] an implicit argument of the constructors. *)

Arguments Ret  {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} η e k.
Arguments Flip {A} k.
Arguments Par  {A A1 A2} m1 m2 k ko.

(* ------------------------------------------------------------------------ *)

(* Let the user view some of the constructors as combinators. *)

Notation ret :=
  (Ret).

Notation fail :=
  (Fail).

Notation next :=
  (λ tt, Next).

(* [flip] flips a coin. *)

Definition flip : free bool :=
  Flip ret.

(* [choose m1 m2] is a non-deterministic choice between the
   computations [m1] and [m2]. *)

Definition choose {A} (m1 m2 : free A) : free A :=
  Flip $ λ b,
  if b then m1 else m2.

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
  | Stop η e k =>
      (* A [Stop] effect is transmitted. The handler [bind _ f] remains
         installed on top of the continuation. *)
      Stop η e (λ v, bind (k v) f)
  | Flip k =>
      (* Same here. *)
      Flip (λ v, bind (k v) f)
  | Par m1 m2 k ko =>
      (* Same here. *)
      Par m1 m2 (λ v, bind (k v) f) (λ tt, bind (ko()) f)
  end.

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
  | Stop η e k =>
      (* A [Stop] effect is transmitted. The handler [try _ f g] remains
         installed on top of the continuation. Because [eval η e] cannot
         cause a soft failure, there is only one continuation. *)
      Stop η e (λ v, try (k v) f g)
  | Flip k =>
      (* Same here. *)
      Flip (λ v, try (k v) f g)
  | Par m1 m2 k ko =>
      (* Same here. The handler [try _ f g] remains installed on top of
         both continuations. *)
      Par m1 m2 (λ v, try (k v) f g) (λ tt, try (ko()) f g)
  end.

(* This is a monad. *)

Global Instance free_mret : MRet free :=
  { mret := @Ret }.

Global Instance free_mbind : MBind free :=
  { mbind := λ {A B} (f : A → free B) (m : free A), bind m f }.

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
  bind (Ret a) f = f a.
Proof.
  reflexivity.
Qed.

Lemma bind_fail {A B} (f : A → free B) :
  bind Fail f = Fail.
Proof.
  reflexivity.
Qed.

Lemma bind_next {A B} (f : A → free B) :
  bind Next f = Next.
Proof.
  reflexivity.
Qed.

Lemma bind_stop {A B} η e k (f : A → free B) :
  bind (Stop η e k) f = Stop η e (λ v, bind (k v) f).
Proof.
  reflexivity.
Qed.

Lemma bind_flip {A B} k (f : A → free B) :
  bind (Flip k) f = Flip (λ v, bind (k v) f).
Proof.
  reflexivity.
Qed.

Lemma bind_par {A1 A2 A B} (m1 : free A1) (m2 : free A2) k ko (f : A → free B) :
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

Lemma eq_stop_stop A (k1 k2 : val → free A) η e :
  (∀ v, k1 v = k2 v) →
  Stop η e k1 = Stop η e k2.
Proof.
  intros. f_equal. extensionality v. eauto.
Qed.

Lemma eq_flip_flip A (k1 k2 : bool → free A) :
  (∀ v, k1 v = k2 v) →
  Flip k1 = Flip k2.
Proof.
  intros. f_equal. extensionality b. eauto.
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

#[export] Hint Resolve eq_stop_stop eq_flip_flip eq_par_par : eq.

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
