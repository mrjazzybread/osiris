open Stateful

(* As the counter is monotone, the function cannot be used twice. *)
let count_for n =
  assert (Counter.get () = 0) ;
  for _ = 1 to n do
    Counter.incr ()
  done;
  Counter.get ()

(* This alternative version can. *)
let count_for' n =
  let i = Counter.get () in
  for _ = 1 to n do Counter.incr () done;
  Counter.get () - i


let count_rec n =
  let i = Counter.get () in
  let rec aux j =
    let () = assert (0 <= j) in
    match i with
    | 0 -> Counter.get () - i
    | _ -> Counter.incr (); aux (j - 1)
  in aux n

(* Quick tests. *)

let () = assert (2 = count_for 2)
let () = assert (2 = count_for' 2)
let () = assert (2 = count_rec 2)
