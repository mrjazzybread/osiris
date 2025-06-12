let print n = print_int n; print_newline ()

let () =
  let r = ref 0 in
  r := !r + 2;
  r := !r * 3;
  print !r


let r = ref 0
let () =
  r := !r + 2;
  r := !r * 3;
  print !r

let () =
  let f = ref (fun x -> x + 2) in
  print (!f 2);
  print (!f 3);
  let g = !f in
  f := (fun x -> x + 9);
  print (g 2);
  print (g 3);
  print (!f 2);
  print (!f 3)

let x =
  let r = ref 1 in
  assert (!r = 1);
  r := !r + !r;
  assert (!r = 2);
  r := !r + !r;
  assert (!r = 4);
  print (!r * !r)

let r = ref 1
let s = ref 2

let x = !r + !s
let () = print x

let r = ref 1
let x = !r + !r + !r
let () = print x
