let head l =
  match l with
  | [] -> raise Not_found
  | x :: _ -> x

let catch_head l =
  match head l with
  | exception Not_found -> None
  | x -> Some x

let catch_head2 l =
  try Some (head l) with
  | Not_found -> None
