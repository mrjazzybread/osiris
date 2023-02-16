Require Import Coq.Logic.FunctionalExtensionality.
Require Import lang.

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

Inductive mon A :=
  | Ret (a : A)
  | Fail
  | Next
  | Stop (req : request) (k : val → mon A).

(* Make [A] an implicit argument. *)

Arguments Ret {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} req k.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators. *)

(* [try m f g] runs the computation [m]. If [m] returns a result [v], then
   [f v] is executed. If [m] ends with a soft failure [Next], then [g()] is
   executed. *)

(* [g] must have type [unit → mon B], as opposed to just [mon B], because
   we execute monadic computations (in Coq) using call-by-value evaluation
   and we do not want to evaluate ALL branches in a [match] construct. *)

Fixpoint try {A B} (m : mon A) (f : A → mon B) (g : unit → mon B) : mon B :=
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

Definition bind {A B} (m : mon A) (f : A → mon B) : mon B :=
  try m f (λ tt, Next).

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* Equality is needed to state the monad laws. *)

(* This equality is just equality of trees whose internal nodes are the
   [Stop] nodes and whose leaves are [Ret], [Fail] and [Next]. *)

(* We could give an inductive definition of this equality, as follows. *)

Section Unused.

Inductive eq {A} : mon A → mon A → Prop :=
| EqRet a :
    eq (Ret a) (Ret a)
| EqFail :
    eq Fail Fail
| EqNext :
    eq Next Next
| EqStop req k1 k2 :
    (∀ v, eq (k1 v) (k2 v)) →
    eq (Stop req k1) (Stop req k2)
.

Local Hint Constructors eq : eq.

Local Infix "~" := eq (at level 70, no associativity).

(* Equality is reflexive and transitive. *)

Lemma eq_reflexive {A} (m : mon A) :
  m ~ m.
Proof.
  induction m; constructor; eauto.
Qed.

Lemma eq_transitive {A} (m1 m2 : mon A) :
  m1 ~ m2 → ∀ m3, m2 ~ m3 → m1 ~ m3.
Proof.
  induction 1; inversion 1; subst; constructor; eauto.
Qed.

Local Hint Resolve eq_reflexive : eq.

End Unused.

(* I prefer to accept the axiom of functional extensionality, which implies
   that [eq] coincides with Coq's ordinary equality. *)

Lemma eq_stop_stop A (k1 k2 : val → mon A) req :
  (∀ v, k1 v = k2 v) →
  Stop req k1 = Stop req k2.
Proof.
  intros.
  assert (k1 = k2). { extensionality v. eauto. }
 congruence.
Qed.

#[export] Hint Resolve eq_stop_stop : eq.

(* ------------------------------------------------------------------------ *)

(* The monadic laws. *)

Lemma monad_law_left_unit A B (a : A) (f : A → mon B) :
  bind (Ret a) f = f a.
Proof.
  reflexivity.
Qed.

Lemma monad_law_right_unit A (m : mon A) :
  bind m Ret = m.
Proof.
  unfold bind. induction m; simpl try; eauto with eq.
Qed.

Lemma monad_law_associativity
  A B C (m : mon A) (g : A → mon B) (h : B → mon C) :
  bind (bind m g) h =
  bind m (λ a, bind (g a) h).
Proof.
  unfold bind. induction m; simpl; eauto with eq.
Qed.

#[export] Hint Rewrite
  monad_law_left_unit
  monad_law_right_unit
  monad_law_associativity
  : monad_laws.
