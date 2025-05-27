(* fails. TODO detect this
let r = ref 1
let ((), a) = ((r := 2), !r)
let () = print_int a
*)

(* fails. But the behavior is actually different between ocamlopt (prints A) and
   flambda/bytecode (print B)
let () =
  let r = ref false in
  let s = if snd ((r := true), !r) then "A" else "B" in
  print_endline s

let () =
  let r = ref 1 in
  let p = ((r := 2), !r) in
  print_int (snd p)

*)
