From stdpp Require Import countable numbers gmap.

Local Open Scope Z_scope.

(* A thread handle is an integer. *)

(* We do not want Coq to think that [thread] and [Z] are the same type. Indeed,
   the function [encode] does not work in the same way at threads
   and at ordinary integers. For this reason, we use a record type. *)

Record thread :=
  Thread { id : Z }.

(* Equality. *)

Definition eqb (l1 l2 : thread) :=
  Z.eqb (id l1) (id l2).

(* These instances allow using locations as keys in sets and maps. *)

Global Instance thread_eq_decision : EqDecision thread.
Proof. solve_decision. Defined.

Global Instance thread_countable : Countable thread.
Proof. apply (inj_countable' id Thread). intros [?]. eauto. Defined.

(* This instance allows us to use [stdpp]'s fresh on [thread]. *)

Global Instance Infinite_thread : Infinite thread.
Proof.
  by apply infinite.inj_infinite with (f := Thread) (g := λ l, Some (id l)).
Defined.
