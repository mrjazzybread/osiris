(* TEST *)

open Effect
open Effect.Deep

type _ t += E : unit t
exception Done

let handle_partial f =
  try f () with effect E, k -> assert false

let f () x = perform E

let () =
  match (handle_partial f) () with
  | x -> assert false
  | exception e ->
    (match e with
      | Done -> print_string "ok\n"
      | e -> raise e
    );
  | effect E, k -> discontinue k Done
