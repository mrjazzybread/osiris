(* TEST *)

(* Tests RESUMETERM with extra_args != 0 in bytecode,
   by calling a handler with a tail-continue that returns a function *)

open Effect
open Effect.Deep

type _ t += E : int t

let handle comp =
  try comp () with effect E, k -> continue k 10

let () =
  handle (fun () ->
      print_int (perform E); print_newline ();
      print_int 42; print_newline ())
