open Ast
open PPrint

(* [document_of_expr] translates an expression into a document. *)
let rec document_of_expr e =
  match e with
  | EPlain s ->
      string s
  | EConstr (c, es) ->
      parens (flow space (string c :: List.map document_of_expr es))

let print fmt (e: expr) =
  PPrint.ToFormatter.pretty 0.5 100 fmt (document_of_expr e)

let print fmt module_name headers (a: expr) : unit =
  Format.fprintf fmt
                 "%s@.@.\
                  (* Generated code: *)@.\
                  Definition %s : mexpr := @.\
                  \  @.%a.@.\
                  @.(* END. *)"
                 headers module_name
                 print a
