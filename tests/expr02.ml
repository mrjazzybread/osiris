type t1 = A of (int * int)

type t2 = ..
type t2 += B of int

type t3 = { a : int; b : int }

type t4 = C of t4 | D of (int * t4) | E

(* Testing [pat] *)
let () =
  print_int (let x = 2 in x);
  print_int (let _x = 1 in let _x = 2 in _x);
  print_int (let _x = 1 in let (_x, _) = (2, 3) in _x);
  let x = 1 in
  print_int (let _ as x = 2 in x);
  print_int (match [2] with [] -> 0 | [x] | _ :: x :: _ -> x);
  print_int (match A (2, 3) with A (_, x) -> x);
  print_int (match A (2, 3) with A (_, _x) -> x);
  print_int (match B 2 with B x -> x | _ -> -1);
  print_int (match {a=2; b=3} with {b=c; a=d} -> c + d);
  print_int (match {a=2; b=3} with {b=c; a} -> c + a);
  print_int (match {a=2; b=3} with {a} -> a);
  print_int (match 123 with 123 -> 2 | _ -> 1);
  print_int (match 'c' with 'c' -> 2 | _ -> 1);
  print_int (match "ab" with "ab" -> 2 | _ -> 1);
  print_int (match C (C (C (D (2, C (D (3, C E))))))
             with  C (C (C (D (x, C (D (y, C E)))))) -> x + y | _ -> 1);
  print_newline ()

type 'a t = I : int t | F : float t
let f : int t -> int = function I -> 1 | _ -> .
let () = print_int (f I)

exception Ex1
exception Ex2 of (int * exn)
type exn += Ex3 of (char * exn)

(* Testing [cpat] *)
let () =
  let e1 = Ex2 (1, Ex1) in
  let e2 = Ex3 ('a', e1) in
  let e3 = Ex2 (2, e2) in
  print_int (match e1 with Ex2 (n, _) -> n | _ -> 0);
  print_int (match e2 with Ex1 -> 0 | Ex2 (n, _) -> n | _ -> 1);
  print_int (match e3 with Ex2 (n, Ex3 ('a', _)) -> n | _ -> 0);
  print_int (match raise e3 with exception Ex2 (n, Ex3 ('a', _)) -> n | _ -> 0);
  print_int (match e3 with exception Ex2 (_n, Ex3 ('a', _)) -> 0 | _ -> 2);
  print_int (match Ex2 (1, raise Ex1) with exception Ex1 -> 2 | Ex1 -> 1 | _ -> 0);
  print_int (match raise e1 with (exception Ex1 | exception (Ex2 _)) -> 2 | _ -> 0);
  print_int (match raise e1 with exception (Ex1 | Ex2 _) -> 2 | _ -> 0);
  print_newline ()
