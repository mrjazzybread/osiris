open Effect
open Effect.Deep

(* [LocalMutVar] from [state.ml] with a local int cell. *)

type t = int
type _ Effect.t += Get : t Effect.t
type _ Effect.t += Set : t -> unit Effect.t

let get () = perform Get
let set y = perform (Set y)

let run (type a) init main : t * a =
  let var = ref init in
  match main () with
  | res -> (!var, res)
  | effect Get, k -> continue k (!var)
  | effect (Set y), k -> var := y; continue k ()
