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
