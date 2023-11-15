let rec merge (l1, l2) =
  match l1, l2 with
  | [], l | l, [] -> l
  | h1::t1, h2::t2 ->
     if h1 <= h2 then
       h1 :: (merge (t1, l2))
     else
       h2 :: (merge (l1, t2))

let rec merge2 l1 l2 =
  match l1, l2 with
  | [], l | l, [] -> l
  | h1::t1, h2::t2 ->
     if h1 <= h2 then
       h1 :: (merge2 t1 l2)
     else
       h2 :: (merge2 l1 t2)

let rec split l =
  match l with
  | [] -> [], []
  | [x] -> [x], []
  | x1::x2::t ->
     let (l1, l2) = split t in
                 x1::l1, x2::l2

let rec merge_sort l =
  match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
     let l1, l2 = split l in
     let l1' = merge_sort l1 in
     let l2' = merge_sort l2 in
     merge2 l1' l2'

