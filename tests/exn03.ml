type exn += A | B | C | D

let rec e = function
  | 0 -> A
  | 1 -> B
  | 2 -> C
  | 3 -> D
  | (4 | 5 | 6 | 7) as n -> raise (e (n - 4))
  | _ -> invalid_arg "e"


let print_exn = function
  | A -> print_string "A"
  | B -> print_string "B"
  | C -> print_string "C"
  | D -> print_string "D"
  | _ -> print_string "<other exn>"

let rec f n =
  if n < 8 then print_int n else
  if n < 16 then (print_int n; raise (e (n - 8))) else
  if n < 24 then raise (e (n - 16)) else
    raise A

let gs = [
  (fun n -> f n);
  (fun n -> try f n with A -> print_string "rA");
  (fun n -> try f n with B -> print_string "rB");
  (fun n -> match f n with exception C -> print_string "rC" | () -> ());
  (fun n -> match f n with exception D -> print_string "rD" | () -> ());
  (fun n -> try f n with A | B as e -> print_string "r"; print_exn e);
  (fun n -> try f n with B | C as e -> print_string "r"; print_exn e);
  (fun n -> try f n with B | C | D as e -> print_string "r"; print_exn e);
]

let rec iter f = function [] -> () | x :: l -> f x; iter f l

let () =
  for n = 0 to 25 do
    iter (fun g -> try g n; print_string "d" with e -> print_string "u"; print_exn e) gs;
    print_newline ()
  done
