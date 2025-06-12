(* TEST *)

module Random = struct
  let r = ref 0
  let int n = r := !r + 1; (!r * 1299709) mod n
end

let rec list_make n c = if n = 0 then [] else c :: list_make (n - 1) c
let rec list_for_all f = function [] -> true | x :: l -> f x && list_for_all f l

let opaque_identity f x = print_string ""; f x

let f x =
  let a0 = ref 1 in
  let a1 = ref 1 in
  let a2 = ref 1 in
  let a3 = ref 1 in
  let a4 = ref 1 in
  let a5 = ref 1 in
  let a6 = ref 1 in
  let a7 = ref 1 in
  let a8 = ref 1 in
  let a9 = ref 1 in
  let a10 = ref 1 in
  let a11 = ref 1 in
  let a12 = ref 1 in
  if x then raise Not_found;
  [ a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12 ]

let () =
  for i = 1 to 100 do
    let rs = opaque_identity f false in
    assert (list_for_all (fun x -> !x = 1) rs);
    let _ = list_make (Random.int 30) 'a' in ()
  done;
  print_string "ok\n"
