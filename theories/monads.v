(* TODO define our own Monad class and remove the dependencies
   on coq-extlib and coq-itree? *)

From ExtLib.Structures Require Export Monads MonadLaws.
From ITree Require Export Monad.

(* Tactics. *)

Ltac false :=
  elimtype False.
