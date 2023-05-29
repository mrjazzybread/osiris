open Ast
open PPrint

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

let rec document_of_expr e =
  match e with
  | EPlain s ->
      string s
  | EConstr (c, []) ->
      string c
  | EConstr (c, es) ->
      parens (
        string c ^^ space ^^
        separate_map (break 1) document_of_expr es
      )

let print fmt (e: expr) =
  PPrint.ToFormatter.pretty 0.5 100 fmt (document_of_expr e)

let print fmt module_name headers (a: expr) : unit =
  Format.fprintf fmt
                 "%s@.@.\
                  (* Generated code: *)@.\
                  Definition %s : mexpr := @.\
                  %a.@.\
                  @.(* END. *)"
                 headers module_name
                 print a
