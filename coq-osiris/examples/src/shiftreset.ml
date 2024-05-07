open Effect
open Effect.Deep

(* Delimited control using shift / reset. *)

(* N.B.: we have specialized the type with [int] *)
type _ Effect.t += Shift : (('a, int) continuation -> int) -> 'a t

let shift f = perform (Shift f)
let reset f = match_with f () {
  retc = (fun res -> res);
  exnc = (fun e -> raise e);
  effc =
    (fun (type a) (e : a Effect.t) ->
      match e with
      | Shift f -> Some (fun k -> f k)
      | _ -> None)
}

let main = reset (fun _ -> shift (fun k -> continue k 0 + 1) + 3)
