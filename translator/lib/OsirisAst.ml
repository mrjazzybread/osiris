(* ------------------------------------------------------------------------ *)

(* Variables *)

type variable = string

type coqdef = string

(* Module names: use [name] *)

(* We place variables and module names in the same namespace (This creates
   no conflicts because OCaml variables begin and a lowercase letter while
   OCaml module names begin and an uppercase letter) Thus, variables and
   module names appear together in environments, structures, etc *)

type name = string (* A variable or module name *)

(* ------------------------------------------------------------------------ *)

(* Module paths *)

(* A module path is a possibly-empty list of module names [M], followed and
   a final name, which can be a variable [x] or a module name [M] *)

type path =
  (* An unqualified name *)
  | PathBase of name
  (* A qualified name *)
  | PathDot of path * name

(* ------------------------------------------------------------------------ *)

(* Data constructors *)

type data =
  string

(* Record fields *)

type field =
  string

(* Data constructors and record fields are not treated like variables and
   module names They are never considered "bound" and never looked up in
   an environment They are regarded as constants *)

(* ------------------------------------------------------------------------ *)

(* Machine integers are... well machine integers.
type int = int
*)

(* ------------------------------------------------------------------------ *)

(* Patterns *)

type pat =
  (* The wildcard pattern *)
  | PAny
  (* A variable *)
  | PVar of variable
  (* An alias pattern [p as x] *)
  | PAlias of pat * variable
  (* A disjunction pattern [p1 | p2] *)
  | POr of pat * pat
  (* A tuple pattern *)
  | PTuple of pats
  (* A data constructor pattern *)
  | PData of data * pat
  (* A record pattern *)
  | PRecord of fpats
  (* A literal integer pattern *)
  | PInt of int
  (* Punit is added to simplify the translator. *)
  | PUnit

(* Lists of patterns *)

and pats = pat list

(* Lists of field-pattern pairs *)

and fpats = (field * pat) list

(* ------------------------------------------------------------------------ *)

(* Module coercions *)

(* Module coercions can be understood as a very impoverished form of module
   types They play a role in the dynamic semantics of the shape restriction
   operation on modules *)

type coercion =

  (* The coercion [CIdentity] has no effect *)
  | CIdentity

  (* The coercion [CStruct cs] expects to be applied to a structure The
     fields named in the list [xcs] are retained, and the corresponding
     coercions in the list [xcs] are applied to them All other fields are
     dropped *)
  | CStruct of coercion list

(* ------------------------------------------------------------------------ *)

(* Expressions *)

type expr =
  | EUnit
  | EConstant of string

  (* Path: [x] or [πx] *)
  | EPath of path

  (* An anonymous function *)
  | EAnonFun of anonfun

  (* Function application: [e1 e2] *)
  (* Every function is considered unary *)
  | EApp of expr * expr

  (* Tuple construction: [(e1, e2, )] *)
  | ETuple of exprs

  (* Data constructor application: [A (e)] *)
  (* Every data constructor is considered unary *)
  | EData of data * expr

  (* Record construction: [{ fs = es }] *)
  | ERecord of fexprs
  (* Record update: [{ e and fs = es }] *)
  | ERecordUpdate of expr * fexprs
  (* Record access: [ef] *)
  | ERecordAccess of expr * field

  (* Boolean conjunction, disjunction, and negation *)
  | EBoolConj of expr * expr
  | EBoolDisj of expr * expr
  | EBoolNeg of expr

  (* Strings *)
  | EString of string

  (* Integer literals *)
  | EInt of int
  | EMaxInt
  | EMinInt
  (* Integer arithmetic *)
  | EIntNeg of expr
  | EIntAdd of expr * expr
  | EIntSub of expr * expr
  | EIntMul of expr * expr
  | EIntDiv of expr * expr
  | EIntMod of expr * expr

  (* Polymorphic comparison operators *)
  | EOpEq of expr * expr
  | EOpNe of expr * expr
  | EOpLt of expr * expr
  | EOpLe of expr * expr
  | EOpGt of expr * expr
  | EOpGe of expr * expr

  (* Non-recursive local definition: [let bs in e] *)
  | ELet of bindings * expr

  (* Recursive local definition: [let rbs in e] *)
  | ELetRec of rec_bindings * expr

  (* Local module definition: [let module M = me in e] *)
  | ELetModule of name * mexpr * expr

  (* Local [open] directive: [let open π in e] *)
  | ELetOpen of path * expr

  (* Sequence: [e1; e2] *)
  | ESeq of expr * expr

  (* Conditional: [if e then e1] and [if e then e1 else e2] *)
  | EIfThen of expr * expr
  | EIfThenElse of expr * expr * expr

  (* Pattern matching: [match e and bs] *)
  | EMatch of expr * branches

  (* Loop: [while e do body done] *)
  | EWhile of expr * expr
  (* Loop: [for x = e1 to e2 do e done] *)
  | EFor of variable * expr * expr * expr

  (* Fatal error: [assert false] *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)] *)
  | EAssert of expr

  (* store-related constructors *)
  | ERef of expr
  | ELoad of expr
  | EStore of expr * expr

  | EDef of coqdef

(* Lists of expressions *)

and exprs = expr list

(* Lists of field-expression pairs *)

and fexprs = (field * expr) list

(* A branch is of the form [p -> e] *)

and branch =
  | Branch of pat * expr

(* Lists of branches *)

and branches = branch list

(* A binding is of the form [p = e] *)

and binding =
  | Binding of pat * expr
  | BDef of coqdef

(* Lists of bindings *)

and bindings = binding list

(* A recursive binding is of the form [f = a] *)

and rec_binding =
  | RecBinding of variable * anonfun
  | RecBDef of coqdef

(* Lists of recursive bindings *)

and rec_bindings = rec_binding list

(* An anonymous function is of the form [fun x -> e] We allow only
   this form as a primitive construct, because this simplifies the
   evaluator The constructs [function bs], where [bs] is a list of
   branches, and [fun ps -> e], where [ps] is a list of patterns, are
   regarded as sugar: see [EFunction] and [EFunMultiPat] *)

and anonfun =
  | AnonFun of variable * expr

(* ------------------------------------------------------------------------ *)

(* Module expressions *)

and mexpr =

  (* A module path *)
  | MPath of path

  (* A structure [struct  end] *)
  | MStruct of sitems

  (* A coercion, that is, a shape restriction operation This operation is
     written [M : S] in OCaml surface syntax, and is sometimes implicit: for
     example, a functor application [F(M)] must be understood as [F(M : S)]
     where [S] is the expected shape of the argument of the functor [F] *)
  | MCoercion of mexpr * coercion

  | MDef of coqdef

(* Lists of structure items *)

and sitems = sitem list

(* Structure items *)

and sitem =

  (* A non-recursive toplevel definition [let bs] *)
  | ILet of bindings

  (* A recursive toplevel definition [let rec rbs] *)
  | ILetRec of rec_bindings

  (* A module definition [M = me] *)
  | IModule of name * mexpr

  (* An [open] directive [open π] *)
  | IOpen of path

  (* An [include] directive [include me] *)
  | IInclude of mexpr

  (* A topèlevel Coq definition *)
  | CDef of coqdef

(* ------------------------------------------------------------------------ *)

(* Values *)

(* These values serve as values both for expressions and for module
   expressions Similarly, environments map both variables to values
   and modules to values *)

type value =
  (* A simple (non-recursive) closure *)
  | VClo of environment * anonfun
  (* A recursive closure *)
  (* [η] is the environment at the closure creation site It does not include
     entries for the functions defined by the recursive bindings [rbs] *)
  (* The recursive bindings [rbs] are those of the closure creation site *)
  (* The name [f] is the closure's entry point *)
  | VCloRec of environment * rec_bindings * variable
  (* A string *)
  | VString of string
  (* A machine integer *)
  | VInt of int
  (* A tuple *)
  | VTuple of values
  (* A data constructor value *)
  | VData of data * value
  (* A record *)
  (* A list of field-value pairs is the same thing as an environment,
     so, for the moment at least, we identify these concepts *)
  (* The fields in a record are always pairwise distinct (this is checked
     by OCaml, not by us) and alphabetically sorted *)
  | VRecord of environment
  (* A location will never appear in the translation of a non evaluated program.
  | VLoc of loc *)
  (* A module *)
  | VStruct of environment

(* Lists of values *)

and values = value list

(* Environments are association lists *)

and environment = (variable * value) list

(* ------------------------------------------------------------------------- *)

type tyname = string

type tytype =
  | TRecord of (name * tyname) list

type types = tytype list

(* ------------------------------------------------------------------------- *)

type ast_body =
  | OModule of mexpr
  | OExpr of expr
  | ORecBinding of rec_binding
  | OBinding of binding
  | OSItem of sitem

type ast =
  string option * ast_body
