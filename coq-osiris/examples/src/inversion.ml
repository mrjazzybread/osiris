open Effect
open Effect.Deep

let invert (type elt) (iter : (elt -> unit) -> unit) : elt Seq.t =
  let open struct
        type _ Effect.t += Yield : elt -> unit Effect.t end
  in
  let yield x = perform (Yield x) in
  fun () ->
  match_with iter yield {
      retc = (fun _ -> Seq.Nil);
      exnc = (fun _ -> Seq.Nil);
      effc =
        (fun (type b) (e : b Effect.t) ->
          match e with
          | Yield x ->
             Some (fun (k : (b, _) continuation) ->
                 (* We currently have to eta-expand [continue k]
                    for it to be recognized by the translator. *)
                 Seq.Cons (x, fun () -> continue k ()))
          | _ -> None)
    }
