From Coq.Logic Require Import FunctionalExtensionality.
Require Import monads lang.

(* ------------------------------------------------------------------------ *)

(* A free monad in which the evaluator is expressed. *)

(* The effects allowed by this free monad are:

   - [Fail], a hard failure, which represents a crash and must be avoided;
   - [Next], a soft failure, which represents a request to jump to the next
             branch in a [match] construct;
   - [Stop], an effect whose signature is [request → val];
             this effect can be viewed as consulting an oracle,
             which answers a request with a value.

   The definition of the type [mon A] is inductive:
   every computation must terminate.

   The requests allowed by this monad are:

   - [REval η e], a request to evaluate the expression [e]
                  under the environment [η]. *)

Inductive request :=
  | REval (η : env) (e : expr).

Inductive free A :=
  | Ret (a : A)
  | Fail
  | Next
  | Stop (req : request) (k : val → free A).

(* Make [A] an implicit argument. *)

Arguments Ret {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} req k.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators: [try] and [bind]. *)

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
      (* A hard failure is transmitted. *)
      Fail
  | Next =>
      g()
  | Stop req k =>
      (* An effect is transmitted. The combinator [try _ f g] remains
         installed on top of the continuation. *)
      Stop req (λ v, try (k v) f g)
  end.

(* [bind m f] sequences the computations [m] and [f]. *)

(* [bind] is a special case of [try]. If [m] ends with a soft failure,
   it is transmitted. *)

Definition free_bind {A B} (m : free A) (f : A → free B) : free B :=
  try m f (λ tt, Next).

(* This is a monad. *)

Global Instance free_monad : Monad free :=
  { ret := @Ret; bind := @free_bind }.

(* ------------------------------------------------------------------------ *)

(* Paraphrase lemmas. *)

Lemma fold_bind {A B} (m : free A) (f : A → free B) :
  try m f (λ tt, Next) = bind m f.
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

Lemma bind_stop {A B} req k (f : A → free B) :
  bind (Stop req k) f = Stop req (λ v, bind (k v) f).
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This equality is just equality of trees whose internal nodes are the
   [Stop] nodes and whose leaves are [Ret], [Fail] and [Next]. *)

(* We could give an inductive definition of this equality. I prefer to
   accept the axiom of functional extensionality, which implies that
   the desired equality coincides with Coq's ordinary equality. *)

Lemma eq_stop_stop A (k1 k2 : val → free A) req :
  (∀ v, k1 v = k2 v) →
  Stop req k1 = Stop req k2.
Proof.
  intros.
  assert (k1 = k2). { extensionality v. eauto. }
 congruence.
Qed.

#[export] Hint Resolve eq_stop_stop : eq.

Global Instance eq1_free : Eq1 free :=
  λ (A : Type), @eq (free A).

Arguments eq1_free /.

(* ------------------------------------------------------------------------ *)

(* The monadic laws. *)

Global Instance monadlaws_free :
  MonadLaws _.
Proof.
  constructor; unfold bind, ret, eq1; simpl; unfold free_bind.
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
