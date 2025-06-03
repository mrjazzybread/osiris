(* Nested exceptions and expressions *)

exception Ex1
exception Ex4 of (int * (unit -> exn))

let rec f (n : int) : exn =
  match n with
  | 0 -> Ex4 (0, fun () -> Ex1)
  | 1 -> Ex4 (1, fun () -> raise Ex1)
  | n ->
    match n mod 4 with
    | 0 -> Ex4 (n, fun () -> f (n / 4))
    | 1 -> Ex4 (n, fun () -> raise (f (n / 4)))
    | 2 -> Ex4 (n, fun () -> Ex1)
    | _ -> Ex4 (n, fun () -> Ex4 (n, fun () -> f (n / 4)))

let rec p (f : unit -> exn) : unit =
  match f () with
  | Ex4 (n, g)           -> print_string "e("; print_int n; p g; print_string ")"
  | exception Ex4 (n, g) -> print_string "E("; print_int n; p g; print_string ")"
  | Ex1 -> print_string "e1"
  | exception Ex1 -> print_string "E1"
  | _ | exception _ -> assert false

let () =
  for i = 0 to 50 do
    p (fun () -> f i); print_newline ()
  done
