(* Examples from https://ocaml.org/manual/effects.html  *)

open Effect
open Effect.Deep

type _ Effect.t += Xchg: int -> int t

let comp1 () = perform (Xchg 0) + perform (Xchg 1)

let () = print_int (
    try comp1 () with
      effect (Xchg n), k -> continue k (n+1)
  )

type 'a status =
  Complete of 'a
| Suspended of {msg: int; cont: (int, 'a status) continuation}

let step (f : unit -> 'a) () : 'a status =
  match f () with
  | v -> Complete v
  | effect (Xchg msg), cont -> Suspended {msg; cont}

let rec run_both a b =
  match a (), b () with
  | Complete va, Complete vb -> (va, vb)
  | Suspended {msg = m1; cont = k1},
    Suspended {msg = m2; cont = k2} ->
      run_both (fun () -> continue k1 m2)
               (fun () -> continue k2 m1)
  | _ -> failwith "Improper synchronization"


let comp2 () = perform (Xchg 21) * perform (Xchg 21)

let () =
  let (a, b) = run_both (step comp1) (step comp2) in
  assert (a = 42);
  assert (b = 0);
  print_int (a * 100 + b)

let () = print_newline ()

type _ Effect.t += Fork : (unit -> unit) -> unit t
                 | Yield : unit t
let fork f = perform (Fork f)
let yield () = perform Yield
let xchg v = perform (Xchg v)

module Queue = struct
  type 'a t = 'a list ref
  let create () = ref []
  let push x q = q := x :: !q
  let pop q = match !q with [] -> invalid_arg "pop" | x :: l -> q := l; x
  let is_empty q = !q = []
end


(* A concurrent round-robin scheduler *)
let run (main : unit -> unit) : unit =
  let exchanger : (int * (int, unit) continuation) option ref =
    ref None (* waiting exchanger *)
  in
  let run_q = Queue.create () in (* scheduler queue *)
  let enqueue k v =
    let task () = continue k v in
    Queue.push task run_q
  in
  let dequeue () =
    if Queue.is_empty run_q then () (* done *)
    else begin
      let task = Queue.pop run_q in
      task ()
    end
  in
  let rec spawn (f : unit -> unit) : unit =
    match f () with
    | () -> dequeue ()
    | exception e ->
        print_endline "Printexc.to_string e";
        dequeue ()
    | effect Yield, k -> enqueue k (); dequeue ()
    | effect (Fork f), k -> enqueue k (); spawn f
    | effect (Xchg n), k ->
        begin match !exchanger with
        | Some (n', k') -> exchanger := None; enqueue k' n; continue k n'
        | None -> exchanger := Some (n, k); dequeue ()
        end
  in
  spawn main

let _ = run (fun _ ->
  fork (fun _ ->
    print_endline "[t1] Sending 0";
    let v = xchg 0 in
    print_string "[t1] received "; print_int v; print_newline ());
  fork (fun _ ->
    print_endline "[t2] Sending 1";
    let v = xchg 1 in
    print_string "[t2] received "; print_int v; print_newline ()))

module Seq = struct
  type +'a node =  Nil | Cons of 'a * 'a t
  and 'a t = unit -> 'a node
  let to_dispenser xs =
    let s = ref xs in
    fun () ->
      match (!s)() with
      | Nil ->
        None
      | Cons (x, xs) ->
        s := xs;
        Some x
end

let invert (type a) (iter : (a -> unit) -> unit) : a Seq.t =
  let module M = struct
    type _ Effect.t += Yield : a -> unit t
  end in
  let yield v = perform (M.Yield v) in
  fun () -> match iter yield with
  | () -> Seq.Nil
  | effect M.Yield v, k -> Seq.Cons (v, fun x -> continue k x)


let rec map f = function [] -> [] | x :: l -> f x :: map f l
let rec sum = function [] -> 0 | x :: l -> x + sum l
let rec seq a b = if a > b then [] else a :: seq (a + 1) b
let rec iter f l = match l with [] -> () | x :: l -> f x; iter f l
let rec hash = function [] -> 0 | x :: l -> x + 7 * hash l

let lst_iter f = iter f [1;2;3]
let () = lst_iter (fun i -> print_int i)
let s = invert lst_iter
let next = Seq.to_dispenser s

let print_int_option o =
  match o with
  | None -> print_string "None"
  | Some n -> print_string "Some "; print_int n

let () =
  print_int_option (next ());
  print_int_option (next ());
  print_int_option (next ());
  print_int_option (next ());
  ()



type _ Effect.t += E : int t
                 | F : string t

let foo () = perform F

let bar () =
  try foo () with
  | effect E, k -> failwith "impossible"

let baz () =
  try bar () with
  | effect F, k -> continue k "Hello, world!"

let () = print_endline (baz ())
