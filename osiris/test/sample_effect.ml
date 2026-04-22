open Effect
open Effect.Deep

type _ Effect.t += Ask : int t

let ask () = perform Ask

let run f =
  match f () with
  | x -> x
  | effect Ask, k -> continue k 42
