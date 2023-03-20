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
     which the continuation [k] consumes.

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
.

(* Make [A] an implicit argument of the constructors. *)

Arguments Ret  {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} η e k.
Arguments Flip {A} k.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators: [try] and [bind]. *)

(* [bind m f] sequences the computations [m] and [f]. *)

Fixpoint _bind {A B} (m : free A) (f : A → free B) : free B :=
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
      (* A [Stop] effect is transmitted. The handler [_bind _ f] remains
         installed on top of the continuation. *)
      Stop η e (λ v, _bind (k v) f)
  | Flip k =>
      (* Same here. *)
      Flip (λ v, _bind (k v) f)
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
         cause a soft failure, there is no need for the handler to monitor
         its execution. *)
      Stop η e (λ v, try (k v) f g)
  | Flip k =>
      (* Same here. *)
      Flip (λ v, try (k v) f g)
  end.

(* This is a monad. *)

Global Instance free_monad : Monad free :=
  { ret := @Ret; bind := @_bind }.

(* [bind] is in fact a special case of [try]. We prefer to give a direct
   definition of [bind] anyway, so as to prevent Coq from expanding uses
   of [bind] into more complex expressions that seem to involve [try]. *)

Lemma bind_as_try {A B} (m : free A) (f : A → free B) :
  bind m f =
  try m f (λ tt, Next).
Proof.
  induction m; try solve [
    reflexivity
  | simpl; f_equal; extensionality v; eauto ].
Qed.

(* ------------------------------------------------------------------------ *)

(* Paraphrase lemmas. *)

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

#[export] Hint Resolve eq_stop_stop eq_flip_flip : eq.

Global Instance eq1_free : Eq1 free :=
  λ (A : Type), @eq (free A).

Arguments eq1_free /.

(* ------------------------------------------------------------------------ *)

(* The monadic laws. *)

Global Instance monadlaws_free :
  MonadLaws _.
Proof.
  constructor; unfold bind, ret, eq1; simpl.
  { reflexivity. }
  { intros A m. induction m; simpl; eauto with eq. }
  { intros A B C m g h. induction m; simpl; eauto with eq. }
Qed.

(* We probably do not need the following variant, but prove it anyway. *)

Global Instance monadlawse_free :
  MonadLawsE free.
Proof.
  constructor; intros.
  { eapply bind_of_return; typeclasses eauto. }
  { eapply return_of_bind; typeclasses eauto. }
  { eapply bind_associativity; typeclasses eauto. }
  { unfold eq1, eq1_free.
    intros m m' ?. subst m'.
    unfold pointwise_relation, respectful.
    intros f1 f2 ?.
    f_equal. extensionality a. eauto. }
Qed.

(* ------------------------------------------------------------------------ *)

(* [mzero] is [Fail]. *)

Global Instance monadzero_free : MonadZero free :=
  { mzero := @Fail }.

Global Instance monadzerolaws_free :
  MonadZeroLaws _ _.
Proof.
  constructor. reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* [mflip] is [Flip] with a trivial continuation. *)

Global Instance monadflip_free : MonadFlip free :=
  { mflip := Flip ret }.

(* [choose] can be defined in terms of [Flip]. *)

Definition choose {A} (m1 m2 : free A) : free A :=
  Flip $ λ b,
  if b then m1 else m2.

(* [mplus] can be defined in terms of [Flip]. *)

Global Instance monadplus_free : MonadPlus free :=
  { mplus :=
      λ {A1 A2 :Type} (m1 : free A1) (m2 : free A2),
        Flip $ λ b,
        if b then
          bind m1 $ λ a1,
          ret (inl a1)
        else
          bind m2 $ λ a2,
          ret (inr a2)
  }.

(* coq-ext-lib does not seem to define MonadPlusLaws. *)
