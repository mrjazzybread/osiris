From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
Local Open Scope nat_scope.
Local Set Warnings "-abstract-large-number".

Definition do_something (v : val) : micro val :=
  let η := [("v", v)] in
  v ← lookup_name η "v" ;
  let η := [("x", v)] in
  v ← lookup_name η "x" ;
  ret v.

(* -------------------------------------------------------------------------- *)

Fixpoint left_leaning_sequence_of_binds (n : nat) : micro val :=
  match n with
  | 0 =>
      ok
  | S n =>
      v ← left_leaning_sequence_of_binds n;
      do_something v
  end.

(* This seems to exhibit linear time complexity.
   Speed is roughly 2500 iterations per second. *)

Time Eval cbn in left_leaning_sequence_of_binds 2500.

(* This seems to exhibit linear time complexity.
   Speed is roughly 40,000 iterations per second. *)

Time Eval cbv in left_leaning_sequence_of_binds 20000.

(* -------------------------------------------------------------------------- *)

Fixpoint right_leaning_sequence_of_binds (n : nat) (v : val) : micro val :=
  match n with
  | 0 =>
      ok
  | S n =>
      v ← do_something v;
      right_leaning_sequence_of_binds n v
  end.

(* This seems to exhibit super-linear time complexity.
   The time spent appears to triple when [n] doubles. *)

(* 1500 iterations take roughly 1 second. *)
(* 3000 iterations take roughly 4 seconds. *)

Time Eval cbn in right_leaning_sequence_of_binds 1500 VUnit.
Time Eval cbn in right_leaning_sequence_of_binds 3000 VUnit.

(* This seems to exhibit linear time complexity.
   Speed is roughly 100,000 iterations per second. *)

Time Eval cbv in right_leaning_sequence_of_binds 100000 VUnit.
Time Eval cbv in right_leaning_sequence_of_binds 200000 VUnit.
