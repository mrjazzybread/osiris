From stdpp Require Import base.
Require Import monads.

(* ------------------------------------------------------------------------ *)

(* A divergence monad. *)

(* This type is co-inductive and offers a [Skip] constructor, as usual in
   a divergence monad. It also offers a hard failure constructor [Fail]. *)

CoInductive div A :=
  | Ret (a : A)
  | Fail
  | Skip (m : div A).

Arguments Ret {A} a.
Arguments Fail {A}.
Arguments Skip {A} m.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators. *)

CoFixpoint bind {A B} (m : div A) (f : A → div B) : div B :=
  match m with
  | Ret a =>
      f a
  | Fail =>
      Fail
  | Skip m =>
      Skip (bind m f)
  end.

Global Instance div_monad :
  Monad div.
Proof.
  constructor.
  exact @Ret.
  exact @bind.
Defined.

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

CoInductive eq {A} : div A → div A → Prop :=
| EqRet a :
    eq (Ret a) (Ret a)
| EqFail :
    eq Fail Fail
| EqSkip m1 m2 :
    eq m1 m2 →
    eq (Skip m1) (Skip m2)
.

Local Hint Constructors eq : eq.

Local Infix "~" := eq (at level 70, no associativity).

(* Equality is reflexive, symmetric, and transitive. *)

Lemma eq_reflexive {A} :
  ∀ (m : div A),
  m ~ m.
Proof.
  cofix CH. destruct m; constructor; eauto.
Qed.

Lemma eq_symmetric {A} :
  ∀ m1 m2 : div A,
  m1 ~ m2 →
  m2 ~ m1.
Proof.
  cofix CH. inversion 1; subst; constructor; eauto.
Qed.

Lemma eq_transitive {A} :
  ∀ m1 m2 m3 : div A,
  m1 ~ m2 → m2 ~ m3 → m1 ~ m3.
Proof.
Admitted.

Local Hint Resolve eq_reflexive : eq.

(* ------------------------------------------------------------------------ *)

(* The monadic laws. *)

Lemma monad_law_left_unit {A B} (a : A) (f : A → div B) :
  bind (Ret a) f ~ f a.
Proof.
  replace (bind (Ret a) f) with (f a). 2: admit.
  apply eq_reflexive.
Admitted.

Lemma monad_law_right_unit {A} :
  ∀ (m : div A),
  bind m Ret ~ m.
Proof.
  cofix CH. destruct m.
  { apply monad_law_left_unit. }
  { replace (bind Fail Ret) with (Fail : div A). 2: admit.
    apply eq_reflexive. }
  { replace (bind (Skip m) Ret) with (Skip (bind m Ret)). 2: admit.
    constructor. eauto. }
Admitted.

Lemma monad_law_associativity :
  ∀ {A B C} (m : div A) (g : A → div B) (h : B → div C),
  bind (bind m g) h ~
  bind m (λ a, bind (g a) h).
Proof.
Abort.

(* This does not work:

CoFixpoint mfix {T U} (ff : (T → div U) → (T → div U)) (t : T) : div U :=
  ff (λ t, Skip (mfix ff t)) t.

 *)
