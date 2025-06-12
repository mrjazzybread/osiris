(* TEST *)

open Effect
open Effect.Deep

module Queue = struct
  type 'a t = 'a list ref
  let create () = ref []
  let push x q = q := x :: !q
  let pop q = match !q with [] -> invalid_arg "pop" | x :: l -> q := l; x
  let is_empty q = !q = []
end

exception E
type _ t += Yield : unit t
          | Fork : (unit -> string) -> unit t
          | Ping : unit t
exception Pong

let say = print_string

type finished = Finished

let run main =
  let run_q = Queue.create () in
  let enqueue k = Queue.push k run_q in
  let rec dequeue () =
    if Queue.is_empty run_q then Finished
    else continue (Queue.pop run_q) ()
  in
  let rec spawn f =
    match f () with
    | "ok" -> say "."; dequeue ()
    | s -> failwith ("Unexpected result: " ^ s)
    | exception E -> say "!"; dequeue ()
    | effect Yield, k -> say ","; enqueue k; dequeue ()
    | effect (Fork f), k -> say "+"; enqueue k; spawn f
    | effect Ping, k -> say "["; discontinue k Pong
  in
  spawn main

let test () =
  say "A";
  perform (Fork (fun () ->
     perform Yield; say "C"; perform Yield;
     begin match perform Ping; failwith "no pong?" with
     | x -> x
     | exception Pong -> say "]"
     | effect Yield, k -> failwith "what?"
     end;
     raise E));
  perform (Fork (fun () -> say "B"; "ok"));
  say "D";
  perform Yield;
  say "E";
  "ok"

let () =
  let Finished = run test in
  say "\n"
