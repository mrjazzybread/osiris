(* Redefinition of addition and multiplication, which should be used on small
   positive integers. *)

let rec add x y =
  if y = 0
  then mult x 1
  else 1 + (add x (y - 1))

and mult x y =
  if y = 0
  then 0
  else if y = 1
  then x
  else add x (mult x (y - 1))


(* Tests *)
let i3 = add 1 (add 2 0)

let i17 = add (mult 2 2) (add 1 (mult 2 (add 4 2)))
