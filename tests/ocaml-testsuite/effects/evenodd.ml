(* TEST *)

open Effect
open Effect.Deep

type _ t += E : unit t

let rec even n =
  if n = 0 then true
  else try odd (n-1) with effect E, k -> assert false
and odd n =
  if n = 0 then false
  else even (n-1)

let _ =
  let n = 1000 in
  print_string "even ";
  print_int n;
  print_string " is ";
  print_string (if even n then "true" else "false");
  print_newline ()
