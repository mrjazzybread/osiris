type 'a t =
  | Leaf of 'a
  | Node of 'a * 'a t list

let init (a: 'a) : 'a t = Leaf a

let rec map (f: 'a -> 'b) : 'a t -> 'b t = function
  | Leaf a -> Leaf (f a)
  | Node (a, l) ->
     Node (f a, List.map (map f) l)

let rec flat_map (f: 'a -> 'b t) (g: 'a t) : 'b t =
  match g with
  | Leaf a -> f a
  | Node (a, l) ->
     let l: 'b t list = List.map (flat_map f) l in
     match f a with
     | Leaf a -> Node (a, l)
     | Node (a, l') -> Node (a, l' @ l)

let rec size : 'a t -> int = function
  | Leaf _ -> 1
  | Node (_, l) -> 1 + List.fold_right (fun g i -> i + size g) l 0

let rec to_list = function
  | Leaf a -> [a]
  | Node (a, []) -> [a]
  | Node (a, h :: t) ->
     to_list h @ to_list (Node (a, t))

let add l a =
  match a with
  | Leaf a -> Node (a, l)
  | Node (a, l') -> Node (a, l' @ l)
