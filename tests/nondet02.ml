(* from eval_order_xx.ml in ocaml's testsuite *)

let ignore _ = ()
let incr i = i := !i + 1
module Fun = struct let id x = x end

(* eval_order_1.ml *)

let f x y = print_int x; print_int y

let i = ref 0
let () = f (incr i; !i) !i


(* eval_order_2.ml *)

(* PR#6136 *)

exception Ok

let first () =
  let f g x = ignore (failwith "called f"); g in
  let g x = x in
  f g 2 (raise Ok)

let second () =
  let f g x = ignore (failwith "called f"); g in
  let g x = x in
  let h f = f g 2 (raise Ok) in
  ignore (h f)

let () =
  try
    ignore (first ());
    assert false
  with Ok ->
    try
      ignore (second ());
      assert false
    with Ok -> ()


(* eval_order_3.ml *)

let i = ref 0

let f x y = print_int x; print_int y; 0
[@@inline never]

let foo _ = ()

let foobar baz =
  let incr_i _ =
    incr i;
    !i
  in
  let b = !i in
  let z = foo 42 in
  let a = (incr_i [@inlined never]) z in
  let x = f a b in
  x + 1

let () =
  ignore ((foobar 0) : int)

(* eval_order_4.ml *)

(* PR#7531 *)

let f =
  (let _i = print_endline "first"
   in fun q -> fun i -> "") (print_endline "x")

let _ =
  let k =
    (let _i = print_int 1
     in fun q -> fun i -> "") ()
  in k (print_int 0)

let () =
  print_endline "foo";
  ignore ((f ()) : string);
  ignore ((f ()) : string);
  print_endline "bar"

(* (no file eval_order_5.ml) *)

(* eval_order_6.ml: unsupported: mutable record *)

(* eval_order_7.ml *)

let p i x =
  print_int i;
  print_newline ();
  x

let _ =
  for i = (p 13 0) to (p 25 3) do
    p i ()
  done


(* eval_order_8.ml *)

(* closed, inlined *)
let[@inline always] f () () = print_endline "4"
let () = (let () = print_string "3" in f) (print_string "2") (print_string "1")

(* closed, not inlined *)
let[@inline never] f () () = print_endline "4"
let () = (let () = print_string "3" in f) (print_string "2") (print_string "1")

(* closure, inlined *)
let[@inline never] g x =
  (let () = print_string "3" in fun () () -> print_endline x)
    (print_string "2") (print_string "1")
let () = g "4"

(* closure, not inlined *)
let[@inline never] g x =
  (let () = print_string "3" in
   let[@inline never] f () () = print_endline x in f)
    (print_string "2") (print_string "1")
let () = g "4"

(* eval_order_9.ml *)

(* From #12440, by Jeremy Yallop --> this one fails on ocamlopt, in fact *)
(*
let _ =
  let r = ref true in
  match Fun.id ((r := false), !r) with
  | _, true  -> print_endline "Ok"
  | _, false -> print_endline "ERROR"
*)


(* eval_order_pr10283.ml *)

(* Slightly modified version of an example from github user @Ngoguey42,
   submitted as issue number 10283. *)

let[@inline never][@local never] g () =
  let[@local always] f a b = print_int a; print_int b in

  let i = ref 0 in
  f (incr i; !i) (incr i; !i)

let () = g ()

(* float_physical_equality.ml -- unsupported *)
(* float.ml -- unsupported *)
