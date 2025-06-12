(* Testing shadowing of common operators *)

let () =
  let ( + ) a b = 1
  and ( - ) a b = 2
  and ( * ) a b = 3
  and ( / ) a b = 4
  and ( ~- ) a = 5
  and ( ~+ ) b = 6
  in
  let x = 0 in
  print_int (x + 0);
  print_int (x - 0);
  print_int (x * 0);
  print_int (x / 0);
  print_int (- x);
  print_int (+ x);
  print_newline ()

let () =
  print_int (5 + (-4));
  print_int (5 - 3);
  print_int (1 * 3);
  print_int (12 / 3);
  let x = - 5 in
  print_int (- x);
  print_int (1 - (+ x));
  print_newline ()

let ( + ) a b = 1
let ( - ) a b = 2
let ( * ) a b = 3
let ( / ) a b = 4
let ( ~- ) a = 5
let ( ~+ ) a = 6

let () =
  let x = 0 in
  print_int (x + 0);
  print_int (x - 0);
  print_int (x * 0);
  print_int (x / 0);
  print_int (- x);
  print_int (+ x);
  print_newline ()

let print_bool b = print_string (if b then "true" else "false")

(* testing shortcut evaluation for boolean operators *)
let () = print_bool (false || (print_int 1; false))
let () = print_bool (true || assert false)
let () = print_bool (true && (print_int 1; false))
let () = print_bool (false && assert false)

(* the following looks like, but is not really, a function application *)
let () = print_bool ((&&) true (print_int 1; false))
let () = print_bool ((&&) false (assert false))

let () = print_newline ()
