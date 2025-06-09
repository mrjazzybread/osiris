let rec iter f = function
  | [] -> ()
  | x :: l ->
    f x; iter f l

let find_first (type a) l pred =
  let open struct type exn += Found of a end in
  match
    iter (fun x -> if pred x then raise (Found x)) l
  with
  | () -> None
  | exception Found x -> Some x
