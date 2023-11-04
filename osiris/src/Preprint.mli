type expression =
  | EPlain of string
  | EConstr of string * expression list
  | EList of string * expression list

val definition_of_ast : OsirisAst.ast_body -> (string * expression)
