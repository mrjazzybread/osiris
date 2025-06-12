(* TEST *)

open Effect
open Effect.Deep

type _ t += E : int -> int t

let f () =
  print_string "perform effect (E 0)\n";
  let v = perform (E 0) in
  print_string "perform returns "; print_int v; print_string "\n";
  v + 1


let v =
  match f () with
  | v -> print_string "done "; print_int v; print_newline (); v + 1
  | effect (E v), k ->
      print_string "caught effect (E ";
      print_int v;
      print_string "). continuing..\n";
      let v = continue k (v + 1) in
      print_string "continue returns ";
      print_int v;
      print_string "\n";
      v + 1

let () = print_string "result="; print_int v; print_string "\n"
