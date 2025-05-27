let rec iter f = function
  | [] -> ()
  | x :: l ->
    f x; iter f l

let find_elem (type a) l pred =
  let open struct type exn += Found of a end in
  try
    iter (fun x ->
        if pred x then raise (Found x)
      ) l;
    None
  with
  | Found x -> Some x
