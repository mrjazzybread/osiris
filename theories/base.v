Require Export Coq.Program.Equality.
From stdpp Require Export base strings.

(* Tactics. *)

Ltac false :=
  elimtype False.
