(* TEST *)

open Effect
open Effect.Deep

type _ t += E : int -> int t
          | F : unit t

let rec nest = function
  | 0 -> perform (E 42)
  | n ->
     match print_string "["; print_int n; print_newline (); nest (n - 1) with
     | x -> print_string " "; print_int n; print_string "]\n"; x
     | exception e -> print_string " "; print_int n; print_string "]\n"; raise e
     | effect F, k -> assert false

let () =
  match nest 5 with
  | x -> print_string "= "; print_int x; print_newline ()
  | effect (E n), k -> continue k (n + 100)

(*
let () =
  match nest 5 with
  | x -> assert false
  | exception e -> Printf.printf "%s\n" (Printexc.to_string e)
  | effect F, k -> assert false
*)
