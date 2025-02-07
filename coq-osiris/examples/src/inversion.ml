open Effect
open Effect.Deep

let invert (type elt) (iter : (elt -> unit) -> unit) : elt Seq.t =
  let open struct
        type _ Effect.t += Yield : elt -> unit Effect.t end
  in
  let yield x = perform (Yield x) in
  fun () ->
  match iter yield with
  | _ -> Seq.Nil
  | exception _ -> Seq.Nil
  | effect (Yield x), k ->
      Seq.Cons (x, fun () -> continue k ())
      (* We have to eta-expand [continue k] to [fun () -> continue k ()] because continue is
	 translated to [EContinue e1 e2], and there is no representation for a partially applied continue. *)
