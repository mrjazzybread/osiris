From stdpp Require Export base strings.

(* Tactics. *)

Ltac false :=
  elimtype False.
