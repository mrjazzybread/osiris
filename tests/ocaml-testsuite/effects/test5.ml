(* TEST *)

open Effect
open Effect.Deep

type _ t += Foo : int -> int t

let f () = (perform (Foo 3)) (* 3 + 1 *)
         + (perform (Foo 3)) (* 3 + 1 *)

let r =
  try f () with
  | effect (Foo i), k ->
    try continue k (i + 1) with
    | effect (Foo i), k -> failwith "NO"

let () = print_int r; print_newline ()
