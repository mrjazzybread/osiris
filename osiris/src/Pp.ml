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

let rec expr0 (e : expression) =
  group @@ match e with
  | CAtom s ->
      string s
  | CCon (c, []) ->
      string c
  | CCon (_, _) ->
      parens (expr1 e)
  | CList [] ->
      string "[]"
  | CList es ->
      brackets (
        separate_map semibreak expr1 es
      )
  | CTuple [] ->
      string "()"
  | CTuple es ->
      parens (
        separate_map commabreak expr1 es
      )
  | CMark e ->
      expr0 e

and expr1 e =
  match e with
  | CCon (c, []) ->
      string c
  | CCon (c, es) ->
      string c ^^ space ^^ separate_map space expr0 es
  | CMark e ->
      expr1 e
  | _ ->
      expr0 e

let print_def def =
  string "Definition " ^^ string def.lhs ^^ string " :=" ^^ nest 2 (group (
    break 1 ^^
    expr1 def.rhs ^^
    dot
  )) ^^
  hardline ^^
  hardline

let print_defs defs =
  concat_map print_def defs
