open Effect
open Effect.Shallow

type _ Effect.t += Ask : int t

let ask () = perform Ask

let run f =
  let done_h = {
    retc = (fun x -> x);
    exnc = (fun e -> raise e);
    effc = fun _ -> None
  } in
  continue_with (fiber f) () {
    retc = (fun x -> x);
    exnc = (fun e -> raise e);
    effc = fun (type a) (eff : a Effect.t) ->
      match eff with
      | Ask -> Some (fun (k : (a, _) continuation) ->
          continue_with k 42 done_h)
      | _ -> None
  }
