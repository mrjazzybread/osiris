open Effect
open Effect.Deep

(* Delimited control using shift / reset. *)

(* N.B.: we have specialized the type with [int] *)
type _ Effect.t += Shift : (('a, int) continuation -> int) -> 'a t

let shift f = perform (Shift f)
let reset f = try f () with
  | effect (Shift g), k -> g k

let main = reset (fun _ -> shift (fun k -> continue k 0 + 1) + 3)
