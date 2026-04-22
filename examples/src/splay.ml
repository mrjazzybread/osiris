(* Code taken from "FP2: Fully in-Place Functional Programming"
   by Anton Lorenzen, Daan Leijen, and Wouter Swierstra (2023). *)

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

type 'a zipper =
  | Root
  | NodeL of 'a zipper * 'a * 'a tree
  | NodeR of 'a tree * 'a * 'a zipper

let rec splay (l, x, r, ctx) =
  match ctx with
  | Root ->
      Node (l, x, r)
  | NodeL (Root, y, ry) ->
      Node (l, x, Node (r, y, ry))
  | NodeL (NodeL (up, z, rz), y, ry) ->
      splay (l, x, Node (r, y, Node (ry, z, rz)), up)
  | NodeL (NodeR (lz, z, up), y, ry) ->
      splay (Node (lz, z, l), x, Node (r, y, ry), up)
  | NodeR (ly, y, Root) ->
      Node (Node (ly, y, l), x, r)
  | NodeR (ly, y, NodeL (up, z, rz)) ->
      splay (Node (ly, y, l), x, Node (r, z, rz), up)
  | NodeR (ly, y, NodeR (lz, z, up)) ->
      splay (Node (Node (lz, z, ly), y, l), x, r, up)

let splay_leaf ctx =
  match ctx with
  | Root ->
      Leaf
  | NodeL (up, x, r) ->
      splay (Leaf, x, r, up)
  | NodeR (l, x, up) ->
      splay (l, x, Leaf, up)

let rec zlookup (t, x, ctx) : 'a option * 'a tree =
  match t with
  | Leaf ->
      (None, splay_leaf ctx) (* not found, but splay anyway *)
  | Node (l, y, r) ->
      let c = compare x y in
      if c < 0 then
        zlookup (l, x, NodeL (ctx, y, r)) (* go down left *)
      else if c > 0 then
        zlookup (r, x, NodeR (l, y, ctx)) (* go down right *)
      else
        (Some y, splay (l, y, r, ctx))

let lookup t x =
  zlookup (t, x, Root)
