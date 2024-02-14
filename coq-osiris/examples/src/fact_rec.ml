(* [Recursion without Rec] example, from Cornell's CS 3110 course developed by
    Michael Clarkson. *)

(* Standard factorial function, defined as a recursive function. *)
let rec fact_rec n = if n = 0 then 1 else n * fact_rec (n - 1)

(* Definition of a factorial function using higher-order store *)
(* Instantiate a ref cell with a dummy function value *)
let fact0 = ref (fun x -> x + 0)

(* Factorial function that uses a ref cell for recursion *)
let fact n = if n = 0 then 1 else n * (!fact0 (n - 1))

(* Tying the recursive knot; now the [fact] function should implement the
   factorial function correctly. *)
let _ = fact0 := fact

(* Both should compute [120]. *)
let fact_rec_5 = fact_rec 5
let fact_5 = fact 5
