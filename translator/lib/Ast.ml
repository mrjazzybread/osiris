type expr =
  | EPlain of string
  | EConstr of string * expr list

(* A file is a list of bindings.
   [ [let a = e; ...] ] is translated by [ [ (Some "a", «translation of e») ]; ... ].
   The [None] case is used when unit or PAny appear. *)
type ast = (string option * expr) list
