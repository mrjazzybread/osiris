type nat =
  | O
  | S of nat


(* ------------------------------------------------------------------------- *)

module Recursion = struct
  (* Non-terminating recursion. *)
  let rec infinite (n : nat) : int =
    match n with
  | O -> 0
  | S n -> infinite (S n)

  (* Terminating recursion. *)
  let rec nat_to_int (n : nat) : int =
    match n with
  | O -> 0
  | S n -> nat_to_int n + 1

  (* [int_to_nat] converts a positive integer to a unary natural number. The
     function fails on negative inputs. *)
  let rec int_to_nat (i: int) : nat =
    let () = assert (0 <= i) in
    if i = 0
    then O
    else S (int_to_nat (i-1))
end

module Counter = struct
  type counter = int ref

  let init () = ref 0
  let get r = !r
  let incr r = r := !r + 1
  let set r i = r := i
end

let twelve = 12
(* let twelve' =
  for _i = 1 to 12 do
    Counter.incr ()
  done;
  Counter.get () *)
let twelve' = twelve

let twelve_nat = S (S (S
                (S (S (S
                (S (S (S
                (S (S (S O)))))))))))
let twelve_nat' = Recursion.int_to_nat twelve'

let twelve_int = Recursion.nat_to_int twelve_nat
let twelve_int' = Recursion.nat_to_int twelve_nat'


(* Should succeed:
let () = assert (Recursion.infinite O = 0
                 && twelve_int' = twelve_int
                 && twelve_nat' = twelve_nat
                 && twelve' = 12) *)
let () = assert true
