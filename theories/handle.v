From ExtLib.Structures Require Export Monads MonadLaws.
Require Import lang eval.
Require free.

Section Handle.

(* Suppose the target monad has [mzero] and [mfix]. *)

Variable target : Type → Type.
Variable M : Monad target.
Variable ML : MonadLaws M.
Variable MZ : MonadZero target.
Variable MZL : MonadZeroLaws M MZ.
Variable MF : MonadFix target.
Variable MFL : MonadFixLaws MF.

(* ------------------------------------------------------------------------ *)

(* An interpretation of our free monad into the target monad. *)

Definition handle_pre {A}
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

Definition handle {A} : free.mon A → target A :=
  mfix handle_pre.

Lemma fixed_point {A} (m : free.mon A) :
  mleq eq (handle m) (handle_pre handle m).
Proof.
  eapply mfix_monotonic. reflexivity.
Qed.

(* TODO we would like to deduce this: *)

Lemma fp {A} (m : free.mon A) :
  handle m = handle_pre handle m.
Proof.
Admitted.

(* Paraphrase lemmas. *)

Lemma handle_ret {A} (a : A) :
  handle (free.Ret a) = ret a.
Proof.
  rewrite fp. reflexivity.
Qed.

Lemma handle_fail {A} :
  handle (free.Fail : free.mon A) = mzero.
Proof.
  rewrite fp. reflexivity.
Qed.

Lemma handle_next {A} :
  handle (free.Next : free.mon A) = mzero.
Proof.
  rewrite fp. reflexivity.
Qed.

Lemma handle_stop {A} η e (k : val → free.mon A) :
  handle (free.Stop (free.REval η e) k) = handle (bind (eval η e) k).
Proof.
  rewrite fp. reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* The composition of [handle] and [eval] is an interpreter of expressions
   in the target monad. *)

Definition run η e : target val :=
  handle (eval η e).

(* ------------------------------------------------------------------------ *)

(* [handle] commutes with [bind]. *)

(* In other words, [handle] is a monad morphism. *)

Lemma compatibility {A B} (m : free.mon A) (k : A → free.mon B) :
  handle (bind m k) =
  bind (handle m) (λ v, handle (k v)).
Proof.
  destruct m.
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
    destruct req as (η & e).
    do 2 rewrite handle_stop.
    (* TODO We are in trouble: we are trying to establish something
       that looks like the initial goal,
       where [m] has been instantiated with [eval η e]. *)
    (* We may need some form of co-induction:
       we need to know that [handle] is a greatest fixed point,
       and it is OK to use a co-induction hypothesis here. *)
Abort.

End Handle.
