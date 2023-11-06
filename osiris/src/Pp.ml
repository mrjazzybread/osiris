open PPrint
open Coq

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

(* TODO enable all warnings *)
let rec pretty_printer (expr : expression) =
  match expr with
  | EPlain s -> string s
  | EConstr (c, []) -> string c
  | EConstr (c, es) ->
     parens (
         string c ^^ space ^^
           separate_map (break 1) pretty_printer es
       )
  | EList [] ->
      string "[]"
  | EList es ->
      brackets (
        separate_map semi pretty_printer es
      )
  | ETuple [] ->
      string "()"
  | ETuple es ->
      parens (
        separate_map comma pretty_printer es
      )
  | EMark e ->
      (* A remaining mark is ignored. *)
      pretty_printer e

let print_def def =
  string "Definition " ^^ string def.lhs ^^ string " :="
  ^^ hardline
  ^^ group (pretty_printer def.rhs)
  ^^ dot
  ^^ hardline
  ^^ hardline

let print_defs defs =
  concat_map print_def defs
