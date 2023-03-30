Require Import base lang free eval step safe wp wp_tactics.

Definition do_something (v : val) : free val :=
  let η := EnvCons "v" v EnvNil in
  eval η (ELet (PVar "x") (EVar "v") (EVar "x")).

(* -------------------------------------------------------------------------- *)

Fixpoint left_leaning_sequence_of_binds (n : nat) : free val :=
  match n with
  | 0 =>
      ok
  | S n =>
      v ← left_leaning_sequence_of_binds n;
      do_something v
  end.

(* This seems to exhibit linear time complexity.
   Speed is roughly 1400 iterations per second. *)

Time Eval cbn in left_leaning_sequence_of_binds 1400.

(* This seems to exhibit linear time complexity.
   Speed is roughly 60,000 iterations per second. *)

Time Eval cbv in left_leaning_sequence_of_binds 40000.

(* -------------------------------------------------------------------------- *)

Fixpoint right_leaning_sequence_of_binds (n : nat) (v : val) : free val :=
  match n with
  | 0 =>
      ok
  | S n =>
      v ← do_something v;
      right_leaning_sequence_of_binds n v
  end.

(* This seems to exhibit super-linear time complexity.
   The time spent appears to triple when [n] doubles. *)

(*  800 iterations take roughly 1 second. *)
(* 1600 iterations take roughly 2.8 seconds. *)

Time Eval cbn in right_leaning_sequence_of_binds 800 VUnit.
Time Eval cbn in right_leaning_sequence_of_binds 1600 VUnit.

(* This seems to exhibit linear time complexity.
   Speed is roughly 65,000 iterations per second. *)

Time Eval cbv in right_leaning_sequence_of_binds 65000 VUnit.
Time Eval cbv in right_leaning_sequence_of_binds 130000 VUnit.
