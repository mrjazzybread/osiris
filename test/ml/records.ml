type r = {
    i: int;
    b: bool;
  }

let r_elt: r = {
    i = 10;
    b = true;
  }

let flip r =
  { r with b = not r.b }

let lily = [ r_elt; flip r_elt ]

(* let revlily = List.rev lily *)

let r_val r =
  match r.b with
  | true -> r.i * 2 - 1
  | false -> r.i

let sum r1 r2 =
  r_val r1 + r_val r2

let rec is_odd_naive n =
  assert (n >= 0);
  if n > 1 then
    is_odd_naive (n-2)
  else
    begin
      if n = 0
      then false
      else true
    end

let is_odd n = n mod 2 = 0

type nat =
  | O
  | S of nat

let rec is_odd' = function
  | O -> true
  | S n -> not (is_odd' n)

(*
let res =
  match lily with
  | [e1; e2] -> sum e1 e2
  | _ -> assert false *)

(* let my_true =
  let s =
    List.fold_left
      (fun s e -> s + r_val e)
      0 lily in
  let s' =
    match lily with
    | r1 :: r2 :: nil -> sum r1 r2
    | _ -> assert false
  in
  is_odd_naive s = is_odd s' *)
