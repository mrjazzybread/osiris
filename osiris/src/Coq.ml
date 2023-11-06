(* -------------------------------------------------------------------------- *)

(**A highly minimalistic abstract syntax of Coq expressions. *)
type expression =

  (* A plain string; printed literally (without quotes). *)
  | EPlain of string

  (* An application of a data constructor to several arguments;
     printed by preceding each argument with a space. *)
  | EConstr of string * expression list

  (* A Coq list; printed with square brackets and semicolons. *)
  | EList of expression list

  (* A Coq tuple; printed with parentheses and commas. *)
  | ETuple of expression list

  (* A mark that suggests that this node should be isolated in a Coq
     toplevel definition. This mark is otherwise meaningless. *)
  | EMark of expression

(**Coq toplevel definitions. *)
type def = {
  lhs : string;
  rhs : expression;
}

(* -------------------------------------------------------------------------- *)

(* Abbreviations for the constructors. *)

let plain s =
  EPlain s

let c s es =
  EConstr (s, es)

let list es =
  EList es

let clist s es =
  c s [list es]

let tuple es =
  ETuple es

let pair e1 e2 =
  ETuple [e1; e2]

let mark e =
  EMark e
