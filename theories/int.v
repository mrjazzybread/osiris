Require Import Integers.

(* Integers in OCaml have an unspecified size. The manual explicitly states
   that it can be 31, 32, or 63, and does not rule out other values. *)

Module Intsize.
  (* The constant [wordsize] corresponds to [Sys.int_size] in OCaml. *)
  Parameter wordsize : nat.
  (* This constant is not zero. *)
  Parameter wordsize_not_zero: wordsize <> 0%nat.
End Intsize.

Include Make(Intsize).
