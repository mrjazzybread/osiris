(* The Osiris AST. *)

(* This file should be in sync with coq-osiris/theories/lang/syntax.v. *)

(* There are a few minor differences between the Coq Osiris AST (syntax.v)
   and this OCaml Osiris AST. In particular, while the Coq AST uses ad hoc
   lists, this AST uses ordinary lists. *)

(* -------------------------------------------------------------------------- *)

(* Variables. *)

type var =
  string

(* Variables and module names. *)

type name =
  string

(* -------------------------------------------------------------------------- *)

(* Module paths. *)

(* A module path is a possibly-empty list of module names [M], followed with
   a final name, which can be a variable [x] or a module name [M]. *)

type path =
  name list (* must be nonempty *)

(* -------------------------------------------------------------------------- *)

(* Data constructors. *)

type data =
  string

(* Record fields. *)

type field =
  string

(* -------------------------------------------------------------------------- *)

(* Patterns. *)

type pat =
  (* A placeholder for as-yet-unsupported constructs. *)
  | PUnsupported
  (* The wildcard pattern. *)
  | PAny
  (* A variable. *)
  | PVar of var
  (* An alias pattern [p as x]. *)
  | PAlias of pat * var
  (* A tuple pattern. *)
  | PTuple of pats
  (* A data constructor pattern. *)
  | PData of data * pat
  (* A data constructor pattern of an extensible type. *)
  | PXData of data * pat
  (* A record pattern. *)
  | PRecord of fpats
  (* A literal integer pattern. *)
  | PInt of int
  (* A literal character pattern. *)
  | PChar of char
  (* A literal string pattern. *)
  | PString of string
  (* A disjunction pattern [p1 | p2]. *)
  | POr of pat * pat

(* Computation patterns. *)

and cpat =
  | CVal of pat
  | CExc of pat
  | CEff of pat
  (* A disjunction pattern [p1 | p2]. *)
  | COr of cpat * cpat

(* Lists of patterns. *)

and pats =
  pat list

(* Lists of field-pattern pairs. *)

and fpats =
  (field * pat) list

(* -------------------------------------------------------------------------- *)

(* Module coercions. *)

type coercion =

  (* The coercion [CIdentity] has no effect. *)
  | CIdentity

  (* The coercion [CStruct cs] expects to be applied to a structure. The
     fields named in the list [xcs] are retained, and the corresponding
     coercions in the list [xcs] are applied to them. All other fields are
     dropped. *)
  | CStruct of fcoercions

and fcoercions =
  (field * coercion) list
      (* A field-coercion list [xcs] must have no duplicate names. *)

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

type expr =

  (* This pseudo-node carries a decoration, a piece of text extracted
     from the OCaml source code. *)
  | EDecorate of string * expr

  (* A placeholder for as-yet-unsupported constructs. *)
  | EUnsupported

  (* Path: [x] or [π.x]. *)
  | EPath of path

  (* An anonymous function [fun x -> e]. *)
  | EAnonFun of anonfun

  (* Function application: [e1 e2]. *)
  (* Every function is considered unary. *)
  | EApp of expr * expr

  (* Tuple construction: [(e1, e2, ...)]. *)
  | ETuple of exprs

  (* Data constructor application: [A (e)]. *)
  (* Every data constructor is considered unary. *)
  | EData of data * expr

  | EXData of data * expr

  (* Record construction: [{ fs = es }]. *)
  | ERecord of fexprs
  (* Record update: [{ e and fs = es }]. *)
  | ERecordUpdate of expr * fexprs
  (* Record access: [ef]. *)
  | ERecordAccess of expr * field

  (* Boolean conjunction, disjunction, and negation. *)
  | EBoolConj of expr * expr
  | EBoolDisj of expr * expr
  | EBoolNeg of expr

  (* Integer literals. *)
  | EInt of int (* TODO is this integer representable? *)
  | EMaxInt
  | EMinInt
  (* Integer arithmetic. *)
  | EIntNeg of expr
  | EIntAdd of expr * expr
  | EIntSub of expr * expr
  | EIntMul of expr * expr
  | EIntDiv of expr * expr
  | EIntMod of expr * expr

  (* Floating-point literals. *)
  | EFloat of string

  (* Character literals. *)
  | EChar of char

  (* String literals. *)
  | EString of string

  (* Polymorphic comparison operators. *)
  | EOpPhysEq of expr * expr
  | EOpEq of expr * expr
  | EOpNe of expr * expr
  | EOpLt of expr * expr
  | EOpLe of expr * expr
  | EOpGt of expr * expr
  | EOpGe of expr * expr

  (* Non-recursive local definition: [let bs in e]. *)
  | ELet of bindings * expr

  (* Recursive local definition: [let rbs in e]. *)
  | ELetRec of rec_bindings * expr

  (* Local module definition: [let module M = me in e]. *)
  | ELetModule of name * mexpr * expr

  (* Local [open] directive: [let open me in e]. *)
  | ELetOpen of mexpr * expr

  (* Sequence: [e1; e2]. *)
  | ESeq of expr * expr

  (* Conditional: [if e then e1] and [if e then e1 else e2]. *)
  | EIfThen of expr * expr
  | EIfThenElse of expr * expr * expr

  (* Pattern matching: [match e with bs]. *)
  | EMatch of expr * branches

  (* Exception catching: [try e with bs]. *)
  | ETryWith of expr * branches
  (* Exception raising: [raise e]. *)
  | ERaise of expr

  (* Loop: [while e do body done] .*)
  | EWhile of expr * expr
  (* Loop: [for x = e1 to e2 do e done]. *)
  | EFor of var * expr * expr * expr

  (* Fatal error: [assert false]. *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)]. *)
  | EAssert of expr

  (* Reference allocation: [ref e]. *)
  | ERef of expr
  (* Reference lookup: [!e]. *)
  | ELoad of expr
  (* Reference assignment: [e1 := e2]. *)
  | EStore of expr * expr

(* Lists of expressions. *)

and exprs =
  expr list

(* Lists of field-expression pairs. *)

and fexpr =
  | Fexpr of field * expr

and fexprs =
  fexpr list

(* A branch is of the form [p -> e]. *)

and branch =
  | Branch of cpat * expr

(* Lists of branches. *)

and branches =
  branch list

(* A binding is of the form [p = e], or a meta-level reference. *)

and binding =
  | Binding of pat * expr

(* Lists of bindings. *)

and bindings =
  binding list

(* A recursive binding is of the form [f = a], or a meta-level reference. *)

and rec_binding =
  | RecBinding of var * anonfun

(* Lists of recursive bindings *)

and rec_bindings =
  rec_binding list

(* An anonymous function is of the form [fun x -> e] or [function bs].
   The first form is primitive; the second form is sugar. *)

and anonfun =
  | AnonFun of var * expr
  | AnonFunction of branches

(* -------------------------------------------------------------------------- *)

(* Module expressions. *)

and mexpr =

  (* A placeholder for as-yet-unsupported constructs. *)
  | MUnsupported

  (* A module path. *)
  | MPath of path

  (* A structure [struct ... end]. *)
  | MStruct of sitems

  (* A coercion, that is, a shape restriction operation. This operation is
     written [M : S] in OCaml surface syntax, and is sometimes implicit: for
     example, a functor application [F(M)] must be understood as [F(M : S)]
     where [S] is the expected shape of the argument of the functor [F]. *)
  | MCoercion of mexpr * coercion

(* Lists of structure items. *)

and sitems =
  sitem list

(* Structure items. *)

and sitem =

  (* A non-recursive toplevel definition [let bs]. *)
  | ILet of bindings

  (* A recursive toplevel definition [let rec rbs]. *)
  | ILetRec of rec_bindings

  (* A module definition [M = me]. *)
  | IModule of name * mexpr

  (* An [open] directive [open me]. *)
  | IOpen of mexpr

  (* An [include] directive [include me]. *)
  | IInclude of mexpr
