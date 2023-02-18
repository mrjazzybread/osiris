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
Context {MF : MonadFix target}.
Context {MFL : MonadFixLaws MF}.
Context {MFC : MonadFixCoinduction MF MFL}.

Section A.

Context {A : Type}.

(* ------------------------------------------------------------------------ *)

(* An interpretation of our free monad into the target monad. *)

Definition handle_pre
  (handle : free.mon A → target A)
  (m : free.mon A) : target A
:=
  match m with
  | free.Ret a =>
      (* Termination is mapped to termination. *)
      ret a
  | free.Fail =>
      (* Hard failure is mapped to hard failure. *)
      mzero
  | free.Next =>
      (* Soft failure is not expected to happen. *)
      mzero
  | free.Stop req k =>
      (* A [Stop] effect is mapped to an invocation of [eval]. The call
         [eval η e] is composed with the continuation [k]. This computation
         is (recursively) transported by [handle] from the free monad into
         the target monad. *)
      match req with
      | free.REval η e =>
          handle (bind (eval η e) k)
      end
  end.

Definition handle : free.mon A → target A :=
  mfix handle_pre.

Lemma handle_fixed_point :
  handle = handle_pre handle.
Proof.
  eapply mfix_fixed_point.
  (* We must check that [handle_pre] is monotonic. *)
  intros self1 self2 Hself m.
  destruct m; simpl;
  eauto using mleq_reflexive.
  destruct req; eauto.
Qed.

(* Paraphrase lemmas. *)

Lemma handle_ret (a : A) :
  handle (free.Ret a) = ret a.
Proof.
  rewrite handle_fixed_point. reflexivity.
Qed.

Lemma handle_fail :
  handle (free.Fail : free.mon A) = mzero.
Proof.
  rewrite handle_fixed_point. reflexivity.
Qed.

Lemma handle_next :
  handle (free.Next : free.mon A) = mzero.
Proof.
  rewrite handle_fixed_point. reflexivity.
Qed.

Lemma handle_stop η e (k : val → free.mon A) :
  handle (free.Stop (free.REval η e) k) = handle (bind (eval η e) k).
Proof.
  pattern handle at 1; rewrite handle_fixed_point.
  simpl.
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
  mleq
    (bind (handle m) (λ v, handle (f v)))
    (handle (bind m f)).
Proof.
  induction m as [ | | | [ η e] k IH ]; intros.
  { rewrite handle_ret.
    do 2 rewrite bind_of_return by typeclasses eauto.
    eapply mleq_reflexive. }
  { rewrite free.free_bind_fail.
    do 2 rewrite handle_fail.
    rewrite bind_zero by typeclasses eauto.
    eapply mleq_reflexive. }
  { rewrite free.free_bind_next.
    do 2 rewrite handle_next.
    rewrite bind_zero by typeclasses eauto.
    eapply mleq_reflexive. }
  { rewrite free.free_bind_stop.
    do 2 rewrite handle_stop.
    (* TODO We are in trouble: we are trying to establish something
       that looks like the initial goal,
       where [m] has been instantiated with [eval η e]. *)
    generalize (eval η e); intros m. clear η e.
    rewrite <- bind_associativity by typeclasses eauto.
    generalize (bind m k). clear m k IH. intros m.
    (* This is exactly the original goal... *)
    (* We may need some form of co-induction:
       we need to know that [handle] is a greatest fixed point,
       and it is OK to use a co-induction hypothesis here. *)
Abort.

End Handle.

Global Opaque handle.
