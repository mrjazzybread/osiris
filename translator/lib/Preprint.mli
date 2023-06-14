type expression =
  | EPlain of string
  | EConstr of string * expression list
  | EList of string * expression list

val definition_of_ast : (string -> unit) ->
                        (string -> unit) ->
                        OsirisAst.ast -> (string * expression)
