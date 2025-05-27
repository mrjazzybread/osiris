let x =
  let r = ref 1 in
  try
    1 / !r
  with
    _ -> 42

let () = assert (x = 1)

let () = print_int x

exception A
exception B

let () =
  print_int (try raise A + 2 with A -> 4);
  print_int (try (if true then raise A; 3) with A -> 4);
  print_int (try (if false then raise A; 3) with A -> 4);
  ()




let rec map f = function [] -> [] | x :: l -> f x :: map f l
let rec sum = function [] -> 0 | x :: l -> x + sum l
let rec seq a b = if a > b then [] else a :: seq (a + 1) b
let rec iter f = function [] -> () | x :: l -> f x; iter f l
let rec hash = function [] -> 0 | x :: l -> x + 7 * hash l

type exn += Found

let mem x l =
  try iter (fun y -> if x = y then raise Found) l; false
  with Found -> true

let int_of_bool b = if b then 1 else 0

let l = [1; 3; 7]

let () = print_int (hash (map int_of_bool (map (fun x -> mem x l) (seq 0 5))))
