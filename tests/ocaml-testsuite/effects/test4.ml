(* TEST *)

open Effect
open Effect.Deep

type _ t += Foo : int -> int t

let r =
  try perform (Foo 3) with
  | effect (Foo i), k ->
    (try continue k (i+1) with
     | effect (Foo i), k -> failwith "NO")

let () = print_int r; print_newline ()
