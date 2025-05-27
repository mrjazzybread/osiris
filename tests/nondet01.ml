let x =
  let r = ref 0 in
  assert (r := !r + 1; true);
  !r

let () = print_int x

exception A
exception B

let () =
  print_int (try raise A + raise B with A -> 1 | B -> 2);
  ()


(* ocamlc/opt print BA but the osiris interpreter prints AB
-- probably because it did not choose the order
indeed with:
./interp.exe --detcheck nondet01.ml
we can see that there are different possible outputs
type s = { a : unit; b : unit }
let _ = { a = print_string "A"; b = print_string "B" }
*)


(* ocamlc/opt print ABBA but the osiris interpreter prints BABA:
let () = match (print_string "A", print_string "B") with _ -> ()
let () = match (print_string "A", print_string "B") with _ -> () | exception _ -> ()
*)
