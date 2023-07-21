open PPrint
open Fresh

(* -------------------------------------------------------------------------- *)

(* A block with indentation. *)

let block opening contents closing =
  group (opening ^^ nest 2 (contents) ^^ closing)

(* -------------------------------------------------------------------------- *)

(* Parentheses with indentation. *)

(* We allow breaking a parenthesized thing into several lines by leaving the
   opening and closing parentheses alone on a line and indenting the content. *)

let parens d =
  block
    lparen
    (break 0 ^^ d)
    (break 0 ^^ rparen)

(* -------------------------------------------------------------------------- *)

let rec pretty_printer (expr : Preprint.expression) =
  match expr with
  | EPlain s -> string s
  | EConstr (c, []) -> string c
  | EConstr (c, es) ->
     parens (
         string c ^^ space ^^
           separate_map (break 1) pretty_printer es
       )
  | EList (c, []) -> parens (string c ^^ string "[]")
  | EList (c, es) ->
     parens (
         string c ^^ space ^^
           brackets (
               separate_map semi pretty_printer es
             )
       )

let pretty_printer (name, ty, expr) : document =
  let name =
    match name with
    | None -> fresh_name ty
    | Some name -> name
  in
  flow space [string "Definition"; string name; colon; string ty; string ":="]
  ^^ hardline
  ^^ align (group (pretty_printer expr)) ^^ dot
  ^^ hardline

let pretty_printer _verbose _debug graph =
  DAG.map pretty_printer graph
