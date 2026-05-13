type vector = { mutable x : int; mutable y : int }

let vec = { x = 1; y = 1 }

let length v =
  (v.x * v.x) + (v.y * v.y)

let update_x v x =
  v.x <- x
