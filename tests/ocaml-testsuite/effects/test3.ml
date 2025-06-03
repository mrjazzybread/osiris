(* TEST *)

open Effect
open Effect.Deep

type _ t += E : unit t
exception X

let () =
  print_int @@
  match print_string "in handler. raising X\n"; raise X with
  | v -> v
  | exception X -> 10
  | effect E, k -> 11
