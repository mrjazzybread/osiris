open PPrint
open Rocq

(* This is a pretty-printer for Rocq terms and definitions. *)

(* -------------------------------------------------------------------------- *)

(* Parentheses and brackets with indentation. *)

(* We allow breaking a parenthesized thing into several lines by leaving the
   opening and closing parentheses alone on a line and indenting the content. *)

let parens doc =
  group (lparen ^^ nest 2 (break 0 ^^ doc) ^^ break 0 ^^ rparen)

let brackets doc =
  nest 2 (lbracket ^^ break 1 ^^ doc) ^^ break 1 ^^ rbracket

(* -------------------------------------------------------------------------- *)

(* Punctuation followed with a breakable space. *)

let semibreak =
  semi ^^ break 1

let commabreak =
  comma ^^ break 1

(* -------------------------------------------------------------------------- *)

(* Terms. *)

(* We organize Rocq terms in two precedence levels. Level 0 contains the
   atoms, that is, everything except constructor applications. Level 1
   contains everything. *)

(* No cut marks [CCut] should remain at this stage, but if any marks do
   remain, they are ignored. *)

let rec expr0 (e : expression) =
  match e with
  | CAtom s ->
      string s
  | CCon (c, []) ->
      string c
  | CCon (_, _) ->
      (* A constructor application of arity 1 (or greater) cannot be
         printed at level 0. Insert parentheses and go to level 1. *)
      parens (expr1 e)
  | CList [] ->
      string "[]"
  | CList es ->
      brackets (separate_map semibreak expr1 es)
  | CTuple [] ->
      string "()"
  | CTuple es ->
      parens (separate_map commabreak expr1 es)
  | CCut (_, e) ->
      expr0 e

and expr1 e =
  match e with
  | CCon (c, []) ->
      string c
  | CCon (c, es) ->
      (* A constructor application of arity 1 (or greater) can be
         printed at level 1. *)
      string c ^^ space ^^ separate_map space expr0 es
  | CCut (_, e) ->
      expr1 e
  | _ ->
      expr0 e

(* -------------------------------------------------------------------------- *)

(* Definitions. *)

let def def =
  string ("Definition " ^ def.lhs ^ " :=") ^^ nest 2 (group (
    break 1 ^^
    expr1 def.rhs ^^
    dot
  )) ^^
  hardline ^^
  hardline

let defs defs =
  concat_map def defs
