type t1 = A of int
type t2 = { a : int; b : int }

let rec list_iter f l = match l with [] -> () | x :: l -> f x; list_iter f l
let print_bool b = print_string (if b then "true" else "false")

(* testing expr constructs not tested before *)
let () =
  print_int ((fun _ -> 3) 1);
  let p = (1, 2) in
  print_int (snd p);
  let r = { a = 1; b = 2 } in
  let r = { r with a = 3 } in
  let r = { r with b = 4 } in
  print_int r.a;
  print_int r.b;
  print_bool (true && (print_int 1; false));
  print_bool (false && (print_int 2; false));
  print_bool (true || (print_int 3; false));
  print_bool (false || (print_int 4; false));
  list_iter print_bool [not true; 'a' = 'b'; 'a' <> 'b'; "a" = "b"; "a" <> "b"];
  let r1 = ref 0 in
  let r2 = ref 0 in
  list_iter print_bool [r1 == r1; r1 != r1; r1 == r2; r1 != r2];
  let a = 1 and c = 2 and b = let x = 3 in x and d = let A x = A 4 in x in
  list_iter print_int [a; b; c; d];
  assert true;
  assert (r1 == r1);
  print_newline ();
  let rec f = fun x y -> g (x - 1) (y + 2)
  and g x y = if x = 0 then y else g (x - 1) (y + 3)
  in
  print_int (f 100 1);
  let _x = 1. in
  print_newline ()


(* excerpt from stdlib.ml *)
let max_int = (-1) lsr 1
let min_int = max_int + 1
(* TODO: remove them from the grammar of expressions and simply use the stdlib
   definition as above -- or actually make the translator recognize it *)

let () = print_int min_int; print_newline ()
let () = print_int max_int; print_newline ()
