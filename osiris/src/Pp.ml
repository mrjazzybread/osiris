open PPrint
open Coq

(* -------------------------------------------------------------------------- *)

(* A block with indentation. *)

let block opening contents closing =
  group (opening ^^ nest 2 contents ^^ closing)

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

let semibreak =
  semi ^^ break 1

let commabreak =
  comma ^^ break 1

let lbracket, rbracket =
  lbracket ^^ break 1,
  break 1 ^^ rbracket

let brackets doc =
  nest 2 (lbracket ^^ doc) ^^ rbracket

let rec pretty_printer (expr : expression) =
  group @@ match expr with
  | CAtom s ->
      string s
  | CCon (c, []) ->
      string c
  | CCon (c, es) ->
      parens (
        string c ^^ space ^^
        separate_map (break 1) pretty_printer es
      )
  | CList [] ->
      string "[]"
  | CList es ->
      brackets (
        separate_map semibreak pretty_printer es
      )
  | CTuple [] ->
      string "()"
  | CTuple es ->
      parens (
        separate_map commabreak pretty_printer es
      )
  | CMark e ->
      (* A remaining mark is ignored. *)
      pretty_printer e

let print_def def =
  string "Definition " ^^ string def.lhs ^^ string " :=" ^^ nest 2 (group (
    break 1 ^^
    pretty_printer def.rhs ^^
    dot
  )) ^^
  hardline ^^
  hardline

let print_defs defs =
  concat_map print_def defs
