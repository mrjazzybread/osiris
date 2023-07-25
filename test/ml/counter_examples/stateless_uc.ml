open Stateless

(* [ff] takes a function and an argument to pass it. Then, it executes the
   function twice (without sequencing the calls) and return the pair of the
   results. *)
let do2 (f : 'a -> 'b) (a : 'a) : 'b * 'b = (f a, f a)

let count_for n =
  (* First initialize two counters. *)
  let c, c' = do2 Counter.make () in
  (* !c = !c' = 0 *)

  Counter.set c' n ;

  for i = 1 to n do
    Counter.incr c;
    Counter.set c' (n + i)
  (* [c] stores i and [c'] stores (n + i). *)
  done;

  (* As [c] stores [n] and [c'] stores [n+n] after the for-loop, the difference
     is [n]. *)
  assert (Counter.get c' - Counter.get c = n) ;

  (* Return [n] *)
  Counter.get c


let count_rec n =
  (* First initialize a counter. *)
  let c = Counter.make () in

  let rec aux i =
    let () = assert (0 <= i) in
    match i with
    | 0 -> Counter.get c
    | _ -> Counter.incr c; aux (i - 1)
  in aux n

(* Quick test. *)

let () = assert (2 = count_for 2)
let () = assert (2 = count_rec 2)
