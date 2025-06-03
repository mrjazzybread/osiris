(* Testing non-determinism resolution. Non-determinism in the specification is
   sometimes consistently implemented in implementations. For example most cases
   of function application are right-to-left, at least in the bytecode and
   flambda compilers. Asserts are always run except if the [-noassert] option is
   set. *)

(* We fail some other cases of non-determinism because implementations are not
   compositional and inconsistent across implementations (e.g. tuples, see
   below), or are too complicated for us to support yet (e.g. records, depending
   on the order of labels in the type definition)

   Such cases of non-determinism can be detected with the --detcheck option
   e.g.:

   ./interp.exe --detcheck nondet01.ml
*)

(** Right-to-left function application *)

exception A
exception B
let () =
  print_int (try raise A + raise B with A -> 1 | B -> 2);
  ()

let p n = print_int n; n
let () =
  let f a b c d = () in
  f (p 0) (p 1) (p 2) (p 3);
  f (p (p 0 + 1)) (p (1 + p 2)) (1 + p 2) (p 3 + p 4);
  print_newline ()


(** Execution of asserts *)
let () =
  assert (print_string "A"; true);
  let r = ref 0 in
  assert (r := !r + 1; true);
  print_int !r;
  print_newline ()


(** Tuples evaluation order is context-dependent *)

(* ocamlc/opt print ABBA
let () = match (print_string "A", print_string "B") with _ -> ()
let () = match (print_string "A", print_string "B") with _ -> () | exception _ -> ()

(the osiris interpreter prints BABA in this case)
*)

(** Tuples evaluation order is implementation-dependent *)

(* The following behaves differently between ocamlopt (prints A) and
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

(* Because we implement tuples with normal par, our default evaluation order
   does not coincide with the most frequent OCaml one, it would be better to
   change this. An example, where we print 123123 instead of 321321.

let _ = (print_int 1, print_int 2, print_int 3)
let _ = [print_int 1; print_int 2; print_int 3]
let () = print_newline ()
*)


(** Records *)

(* ocamlc/opt print BA but the osiris interpreter prints AB *)

(*
type s = { a : unit; b : unit }
let _ = { a = print_string "A"; b = print_string "B" }
*)
