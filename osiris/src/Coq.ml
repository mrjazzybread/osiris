(* -------------------------------------------------------------------------- *)

(**A highly minimalistic abstract syntax of Coq expressions. *)
type expression =

  (* A plain string; printed literally (without quotes). *)
  | CAtom of string

  (* An application of a data constructor to several arguments;
     printed by preceding each argument with a space. *)
  | CCon of string * expression list

  (* A Coq list; printed with square brackets and semicolons. *)
  | CList of expression list

  (* A Coq tuple; printed with parentheses and commas. *)
  | CTuple of expression list

  (* A mark that suggests that this node should be isolated in a Coq
     toplevel definition. This mark is otherwise meaningless. *)
  | CMark of expression

(**Coq toplevel definitions. *)
type def = {
  lhs : string;
  rhs : expression;
}

(* -------------------------------------------------------------------------- *)

(* Abbreviations for the constructors. *)

let plain s =
  CAtom s

let c s es =
  CCon (s, es)

let list es =
  CList es

let clist s es =
  c s [list es]

let tuple es =
  CTuple es

let pair e1 e2 =
  CTuple [e1; e2]

let mark e =
  CMark e
