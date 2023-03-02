From Paco Require Import paco.
From ITree Require Import Eq EqAxiom.
Require Import lang monads free eval.

(* This file defines an interpretation (a transformation) of the [free]
   monad into a monad that must be equipped with [mzero], [skip], and
   [iter]. *)

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

Definition handle_body (m : free A) : target (free A + A) :=
  match m with
  | Ret a =>
      (* Termination is mapped to termination. *)
      ret (inr a)
  | Fail =>
      (* Hard failure is mapped to hard failure. *)
      mzero
  | Next =>
      (* Soft failure is not expected to happen. *)
      mzero
  | Stop (REval η e) k =>
      (* A [Stop] effect is mapped to an invocation of [eval]. The call
         [eval η e] is composed with the continuation [k]. This computation
         is then transported from the free monad into the target monad via
         an (implicit) tail recursive call to [handle]. *)
      ret (inl (bind (eval η e) k))
  end.

Definition handle : free A → target A :=
  iter handle_body.

Lemma handle_fixed_point (m : free A) :
  handle m =
    bind (handle_body m) (fun (signal : free A + A) =>
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
  handle (Ret a) = ret a.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_of_return by eauto.
  reflexivity.
Qed.

Lemma handle_fail :
  handle Fail = mzero.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_zero by eauto.
  reflexivity.
Qed.

Lemma handle_next :
  handle Next = mzero.
Proof.
  rewrite handle_fixed_point. unfold handle_body.
  rewrite bind_zero by eauto.
  reflexivity.
Qed.

Lemma handle_stop η e (k : val → free A) :
  handle (Stop (REval η e) k) =
  skip (handle (bind (eval η e) k)).
Proof.
  rewrite (handle_fixed_point (Stop _ _)). unfold handle_body.
  rewrite bind_of_return by eauto.
  reflexivity.
Qed.

End A.

(* ------------------------------------------------------------------------ *)

(* The composition of [handle] and [eval] is an interpreter of expressions
   in the target monad. *)

Definition run η e : target val :=
  handle (eval η e).

End Handle.

Global Opaque handle.
