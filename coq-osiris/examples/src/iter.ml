let rec iter f = function
  | [] -> ()
  | x :: l ->
    f x; iter f l
