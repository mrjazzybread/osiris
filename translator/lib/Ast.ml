type expr =
  | EPlain of string
  | EConstr of string * expr list

let string_literal x =
  EPlain (Printf.sprintf "\"%s\"" x)

let rec list nil cons (xs : expr list) : expr =
  match xs with
  | [] ->
      EConstr (nil, [])
  | x :: xs ->
      EConstr (cons, [x; list nil cons xs])
