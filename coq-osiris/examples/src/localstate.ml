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
  match_with main ()
    {
      retc = (fun res -> (!var, res));
      exnc = raise;
      effc =
        (fun (type b) (e : b Effect.t) ->
          match e with
          | Get ->
              Some
                (fun (k : (b, t * a) continuation) -> continue k (!var : t))
          | Set y ->
              Some
                (fun k ->
                  var := y;
                  continue k ())
          | _ -> None);
    }
