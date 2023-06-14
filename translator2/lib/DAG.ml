type 'a t =
  | Root of 'a
  | Node of 'a * 'a t list

let init (a: 'a) : 'a t = Root a

let add (g: 'a t) (l: 'a list) : 'a t =
  match g with
  | Root a -> Node (a, List.map init l)
  | Node (n, l') -> Node (n, List.map init l @ l')

let rec size : 'a t -> int = function
  | Root _ -> 1
  | Node (_, l) -> 1 + List.fold_right (fun g i -> i + size g) l 0

let rec to_list = function
  | Root a -> [a]
  | Node (a, []) -> [a]
  | Node (a, h :: t) ->
     to_list h @ to_list (Node (a, t))

let rec map (f: 'a -> 'b) : 'a t -> 'b t = function
  | Root a -> Root (f a)
  | Node (a, l) ->
     Node (f a, List.map (map f) l)
