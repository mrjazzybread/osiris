Require Import lang monads free eval handle spec.

(* This file proves certain properties of [handle] in the special case
   where the target monad is [spec]. *)

(* ------------------------------------------------------------------------ *)

(* [handle] commutes with [bind]. *)

(* In other words, [handle] is a monad morphism. *)

Lemma handle_bind {A B} (m : free A) :
  ∀ (f : A → free B),
  handle (bind m f) =
  bind (handle m) (λ v, handle (f v)).
Proof.
  intros.
  (* TODO set up some form of coinductive argument? *)
  destruct m as [ | | | [ η e] k ]; intros.
  { rewrite handle_ret.
    do 2 rewrite bind_of_return by typeclasses eauto.
    apply reflexivity. }
  { rewrite bind_fail.
    do 2 rewrite handle_fail.
    rewrite bind_zero by typeclasses eauto.
    apply reflexivity. }
  { rewrite bind_next.
    do 2 rewrite handle_next.
    rewrite bind_zero by typeclasses eauto.
    apply reflexivity. }
  { rewrite bind_stop.
    do 2 rewrite handle_stop.
    rewrite bind_skip by typeclasses eauto.
    rewrite <- bind_bind.
    (* We are trying to establish something that looks like the initial goal
       under a pair of [skip]s. *)
    generalize (eval η e); intros m. clear η e.
    generalize (bind m k). clear m k. intros m.
    (* Descend under the [skip]s. *)
    f_equal.
    (* Apply the coinduction hypothesis. *)
Abort.
