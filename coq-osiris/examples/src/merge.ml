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

