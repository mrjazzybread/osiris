Require Import lang eval monads.
Require free.

(* This file defines an interpretation (a transformation) of the [free]
   monad into a monad equipped with [mzero] and [mfix] combinators. *)

Section Handle.

Context {target : Type → Type}.
Context {M : Monad target}.
Context {ML : MonadLaws M}.
Context {MZ : MonadZero target}.
Context {MZL : MonadZeroLaws M MZ}.
Context {MS : MonadSkip target}.
Context {MSL : MonadSkipLaws M MS}.
Context {MI : MonadIter target}.
Context {MIL : MonadIterLaws M MI MS}.

Section A.

Context {A : Type}.

(* ------------------------------------------------------------------------ *)

(* An interpretation of our free monad into the target monad. *)

Definition handle_body (m : free.mon A) : target (free.mon A + A) :=
  match m with
  | free.Ret a =>
      (* Termination is mapped to termination. *)
      ret (inr a)
  | free.Fail =>
      (* Hard failure is mapped to hard failure. *)
      mzero
  | free.Next =>
      (* Soft failure is not expected to happen. *)
      mzero
  | free.Stop (free.REval η e) k =>
      (* A [Stop] effect is mapped to an invocation of [eval]. The call
         [eval η e] is composed with the continuation [k]. This computation
         is then transported from the free monad into the target monad via
         an (implicit) tail recursive call to [handle]. *)
      ret (inl (bind (eval η e) k))
  end.

Definition handle : free.mon A → target A :=
  iter handle_body.

Lemma handle_fixed_point (m : free.mon A) :
  handle m =
    bind (handle_body m) (fun (signal : free.mon A + A) =>
      match signal with
      | inl m =>
          skip (handle m)
      | inr r =>
          ret r
      end).
Proof.
  eapply unfold_iter. eauto.
Qed.

(* Paraphrase lemmas. *)

Lemma handle_ret (a : A) :
  handle (free.Ret a) = ret a.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_of_return by typeclasses eauto.
  reflexivity.
Qed.

Lemma handle_fail :
  handle (free.Fail : free.mon A) = mzero.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_zero by typeclasses eauto.
  reflexivity.
Qed.

Lemma handle_next :
  handle (free.Next : free.mon A) = mzero.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_zero by typeclasses eauto.
  reflexivity.
Qed.

Lemma handle_stop η e (k : val → free.mon A) :
  handle (free.Stop (free.REval η e) k) =
  skip (handle (bind (eval η e) k)).
Proof.
  rewrite (handle_fixed_point (free.Stop _ _)). unfold handle_body.
  rewrite bind_of_return by typeclasses eauto.
  reflexivity.
Qed.

End A.

(* ------------------------------------------------------------------------ *)

(* The composition of [handle] and [eval] is an interpreter of expressions
   in the target monad. *)

Definition run η e : target val :=
  handle (eval η e).

(* ------------------------------------------------------------------------ *)

(* [handle] commutes with [bind]. *)

(* In other words, [handle] is a monad morphism. *)

Lemma compatibility {A B} (m : free.mon A) :
  ∀ (f : A → free.mon B),
  bind (handle m) (λ v, handle (f v)) =
  handle (bind m f).
Proof.
  induction m as [ | | | [ η e] k IH ]; intros.
  { rewrite handle_ret.
    do 2 rewrite bind_of_return by typeclasses eauto.
    reflexivity. }
  { rewrite free.free_bind_fail.
    do 2 rewrite handle_fail.
    rewrite bind_zero by typeclasses eauto.
    reflexivity. }
  { rewrite free.free_bind_next.
    do 2 rewrite handle_next.
    rewrite bind_zero by typeclasses eauto.
    reflexivity. }
  { rewrite free.free_bind_stop.
    do 2 rewrite handle_stop.
    rewrite bind_skip by typeclasses eauto. f_equal.
    (* TODO We are in trouble: we are trying to establish something
       that looks like the initial goal,
       where [m] has been instantiated with [eval η e]. *)
    generalize (eval η e); intros m. clear η e.
    rewrite <- bind_associativity by typeclasses eauto.
    generalize (bind m k). clear m k IH. intros m.
    (* This is exactly the original goal... *)
    (* We may need some form of co-induction:
       we need to know that equality is co-inductive
       and that the co-induction hypothesis can be used
       once a pair of [skip]s have been peeled off. *)
Abort.

End Handle.

Global Opaque handle.
