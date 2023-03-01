From stdpp Require Import base.
Require Import monads.

(* ------------------------------------------------------------------------ *)

(* A divergence monad. *)

(* This type is co-inductive and offers a [Skip] constructor, as usual in
   a divergence monad. It also offers a hard failure constructor [Fail]. *)

(* This type COULD be viewed as an instance of the type [itree] offered by
   the Interaction Trees library. *)

CoInductive div A :=
  | Ret (a : A)
  | Fail
  | Skip (m : div A).

Arguments Ret {A} a.
Arguments Fail {A}.
Arguments Skip {A} m.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators. *)

(* [subst f m] is [bind m f]. Defining [subst] first allows us to point out
   to Coq that the argument [f] is invariant (i.e., it does not change as
   the cofixpoint is unfolded). This in turn allows Coq to accept more
   co-inductive definitions that involve [bind]; the definition of [iter]
   is an example. *)

Section Subst.

  Context {A B : Type}.
  Variable (f : A → div B).

  CoFixpoint subst (m : div A) : div B :=
    match m with
    | Ret a =>
        f a
    | Fail =>
        Fail
    | Skip m =>
        Skip (subst m)
    end.

End Subst.

(* [bind] is [subst] with its argument reversed. *)

Definition bind {A B} (m : div A) (f : A → div B) : div B :=
  subst f m.

Global Instance monad_div : Monad div :=
  { ret := @Ret; bind := @bind }.

Global Instance monadskip_div : MonadSkip div :=
  { skip := @Skip }.

Global Instance monadskiplaws_div :
  MonadSkipLaws _ _.
Proof.
  constructor; simpl. intros.
  unfold bind, skip, monadskip_div.
Admitted.

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

(* ------------------------------------------------------------------------ *)

(* We cannot define a general fixed point combinator. This definition
   is not accepted by Coq, as the function [ff] could deconstruct its
   argument:

   CoFixpoint mfix {T U} (ff : (T → div U) → (T → div U)) (t : T) : div U :=
     ff (λ t, Skip (mfix ff t)) t.

 *)

(* ------------------------------------------------------------------------ *)

(* We can however define an iteration combinator [iter]. *)

CoFixpoint div_iter {R I} (body : I → div (I + R)) (i : I) : div R :=
  (* Evaluate [body] out of the state [i]. *)
  bind (body i) (λ (signal : I + R),
    match signal with
    | inl i =>
        (* If the body yields a new state [i], continue. *)
        Skip (div_iter body i)
    | inr r =>
        (* If the body yields a result [r], return this result. *)
        Ret r
    end).

Global Instance monaditer_div : MonadIter div :=
  { iter := @div_iter }.

Global Instance monaditerlaws_div :
  MonadIterLaws _ _ _.
Proof.
  constructor. simpl.
Admitted.
