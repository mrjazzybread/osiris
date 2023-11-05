(**A highly minimalistic abstract syntax of Coq expressions. *)
type expression =

  (* A plain string; printed literally (without quotes). *)
  | EPlain of string

  (* An application of a data constructor to a list of arguments;
     printed by preceding each argument with a space. *)
  | EConstr of string * expression list

  (* A Coq list; printed with square brackets and semicolons. *)
  | EList of string * expression list
