type 'a bst =
  | Node of 'a bst * 'a * 'a bst
  | Leaf

let rec insert (x, v) =
  match v with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, y, r) ->
      if x < y then
        Node (insert (x, l), y, r)
      else if x > y then
        Node (l, y, insert (x, r))
      else
        Node (l, y, r)

let rec member (x, v) =
  match v with
  | Leaf -> false
  | Node (l, y, r) ->
      if x < y then
        member (x, l)
      else if x > y then
        member (x, r)
      else
        true
