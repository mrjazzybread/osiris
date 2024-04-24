open Effect.Deep

type b = unit

type _ Effect.t +=
        Callcc : 'a . (('a, b) continuation -> 'a) -> 'a Effect.t

let run tk : b =
  match_with tk ()
    {
      retc = (fun res -> res);
      exnc = (fun e -> raise e);
      effc =
        (fun (type a) (e : a Effect.t) ->
          match e with
          | Callcc (t : (a, b) continuation -> a) ->
              Some (fun (k : (a, b) continuation) -> (continue k (t k)))
          | _ -> None);
    }
