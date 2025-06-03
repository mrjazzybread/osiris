(* TEST *)

open Effect
open Effect.Deep

type _ t += E : unit t

let () =
  print_int @@
    try (fun x -> x) 10 with effect E, k -> 11
