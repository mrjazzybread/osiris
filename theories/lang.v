Require int.
Require Import base locations.

(* ------------------------------------------------------------------------ *)

(* Variables. *)

Definition var :=
  string.

(* Module names. *)

Definition module :=
  string.

(* We place variables and module names in the same namespace. (This creates
   no conflicts because OCaml variables begin with a lowercase letter while
   OCaml module names begin with an uppercase letter.) Thus, variables and
   module names appear together in environments, structures, etc. *)

Definition name :=
  string. (* A variable or module name. *)

(* ------------------------------------------------------------------------ *)

(* Module paths. *)

(* A module path is a possibly-empty list of module names [M], followed with
   a final name, which can be a variable [x] or a module name [M]. *)

Inductive path :=
  (* An unqualified name. *)
  | PathBase (n : name)
  (* A qualified name. *)
  | PathDot (π : path) (n : name).

(* ------------------------------------------------------------------------ *)

(* Data constructors. *)

Definition data :=
  string.

(* Record fields. *)

Definition field :=
  string.

(* Data constructors and record fields are not treated like variables and
   module names. They are never considered "bound" and never looked up in
   an environment. They are regarded as constants. *)

(* ------------------------------------------------------------------------ *)

(* Machine integers. *)

Definition int :=
  int.int.

(* ------------------------------------------------------------------------ *)

(* Patterns. *)

Inductive pat :=
  (* The wildcard pattern. *)
  | PAny
  (* A variable. *)
  | PVar (x : var)
  (* An alias pattern [p as x]. *)
  | PAlias (p : pat) (x : var)
  (* A disjunction pattern [p1 | p2]. *)
  | POr (p1 p2 : pat)
  (* A tuple pattern. *)
  | PTuple (ps : pats)
  (* A data constructor pattern. *)
  | PData (c : data) (p : pat)
  (* A record pattern. *)
  | PRecord (fps : fpats)
  (* A literal integer pattern. *)
  | PInt (i : Z)

(* Lists of patterns. *)

with pats :=
  | PNil
  | PCons (p : pat) (ps : pats)

(* Lists of field-pattern pairs. *)

with fpats :=
  | FPNil
  | FPCons (f : field) (p : pat) (fps : fpats).

(* ------------------------------------------------------------------------ *)

(* Expressions. *)

Inductive expr :=

  (* Path: [x] or [π.x]. *)
  | EPath (x : path)

  (* An anonymous function. *)
  | EAnonFun (a : anonfun)

  (* Function application: [e1 e2]. *)
  (* Every function is considered unary. *)
  | EApp (e1 e2 : expr)

  (* Tuple construction: [(e1, e2, ...)]. *)
  | ETuple (es : exprs)

  (* Data constructor application: [A (e)]. *)
  (* Every data constructor is considered unary. *)
  | EData (c : data) (e : expr)

  (* Record construction: [{ fs = es }]. *)
  | ERecord (fes : fexprs)
  (* Record update: [{ e with fs = es }]. *)
  | ERecordUpdate (e : expr) (fes : fexprs)
  (* Record access: [e.f]. *)
  | ERecordAccess (e : expr) (f : field)

  (* Boolean conjunction, disjunction, and negation. *)
  | EBoolConj (e1 e2 : expr)
  | EBoolDisj (e1 e2 : expr)
  | EBoolNeg (e : expr)

  (* Integer literals. *)
  | EInt (i : Z)
  | EMaxInt
  | EMinInt
  (* Integer arithmetic. *)
  | EIntNeg (e : expr)
  | EIntAdd (e1 e2 : expr)
  | EIntSub (e1 e2 : expr)
  | EIntMul (e1 e2 : expr)
  | EIntDiv (e1 e2 : expr)
  | EIntMod (e1 e2 : expr)

  (* Polymorphic comparison operators. *)
  | EOpEq (e1 e2 : expr)
  | EOpNe (e1 e2 : expr)
  | EOpLt (e1 e2 : expr)
  | EOpLe (e1 e2 : expr)
  | EOpGt (e1 e2 : expr)
  | EOpGe (e1 e2 : expr)

  (* Non-recursive local definition: [let bs in e]. *)
  | ELet (bs : bindings) (e : expr)

  (* Recursive local definition: [let rbs in e]. *)
  | ELetRec (rbs : rec_bindings) (e : expr)

  (* Local module definition: [let module M = me in e]. *)
  | ELetModule (M : module) (me : mexpr) (e : expr)

  (* Sequence: [e1; e2]. *)
  | ESeq (e1 e2 : expr)

  (* Conditional: [if e then e1] and [if e then e1 else e2]. *)
  | EIfThen (e e1 : expr)
  | EIfThenElse (e e1 e2 : expr)

  (* Pattern matching: [match e with bs]. *)
  | EMatch (e : expr) (bs : branches)

  (* Loop: [while e do body done]. *)
  | EWhile (e body : expr)
  (* Loop: [for x = e1 to e2 do e done]. *)
  | EFor (x : var) (e1 e2 e : expr)

  (* Fatal error: [assert false]. *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)]. *)
  | EAssert (e : expr)

  (* store-related constructors. *)
  | ERef (e: expr)
  | ELoad (e: expr)
  | EStore (e1 e2: expr)

(* Lists of expressions. *)

with exprs :=
  | ENil
  | ECons (e : expr) (es : exprs)

(* Lists of field-expression pairs. *)

with fexprs :=
  | FENil
  | FECons (f : field) (e : expr) (fes : fexprs)

(* A branch is of the form [p -> e]. *)

with branch :=
  | Branch (p : pat) (e : expr)

(* Lists of branches. *)

with branches :=
  | BrNil
  | BrCons (b : branch) (bs : branches)

(* A binding is of the form [p = e]. *)

with binding :=
  | Binding (p : pat) (e : expr)

(* Lists of bindings. *)

with bindings :=
  | BiNil
  | BiCons (b : binding) (bs : bindings)

(* A recursive binding is of the form [f = a]. *)

with rec_binding :=
  | RecBinding (f : var) (a : anonfun)

(* Lists of recursive bindings. *)

with rec_bindings :=
  | RecBiNil
  | RecBiCons (rb : rec_binding) (rbs : rec_bindings)

(* An anonymous function is of the form [fun x -> e]. *)

with anonfun :=
  | AnonFun (x : var) (e : expr)

(* ------------------------------------------------------------------------ *)

(* Module expressions. *)

with mexpr :=

  (* A module path. *)
  | MPath (π : path)

  (* A structure [struct ... end]. *)
  | MStruct (items : sitems)

(* Lists of structure items. *)

with sitems :=
  | INil
  | ICons (item : sitem) (items : sitems)

(* Structure items. *)

with sitem :=

  (* A non-recursive toplevel definition [let bs]. *)
  | ILet (bs : bindings)

  (* A recursive toplevel definition [let rec rbs]. *)
  | ILetRec (rbs : rec_bindings)

  (* A module definition [M = me]. *)
  | IModule (m : module) (me : mexpr)

  (* An [open] directive [open π]. *)
  | IOpen (π : path)

  (* An [include] directive [include me]. *)
  | IInclude (me : mexpr)

.

(* ------------------------------------------------------------------------ *)

(* Values. *)

(* These values serve as values both for expressions and for module
   expressions. Similarly, environments map both variables to values
   and modules to values. *)

Inductive val :=
  (* A simple (non-recursive) closure. *)
  | VClo (η : env) (a : anonfun)
  (* A recursive closure. *)
  (* [η] is the environment at the closure creation site. It does not include
     entries for the functions defined by the recursive bindings [rbs]. *)
  (* The recursive bindings [rbs] are those of the closure creation site. *)
  (* The name [f] is the closure's entry point. *)
  | VCloRec (η : env) (rbs : rec_bindings) (f : var)
  (* A machine integer. *)
  | VInt (i : int)
  (* A tuple. *)
  | VTuple (vs : vals)
  (* A data constructor value. *)
  | VData (c : data) (v : val)
  (* A record. *)
  (* A list of field-value pairs is the same thing as an environment,
     so, for the moment at least, we identify these concepts. *)
  | VRecord (fvs : env)
  (* A location. *)
  | VLoc (l: loc)
  (* A module. *)
  (* This is very much like a record. We use two distinct tags for clarity. *)
  | VStruct (fvs : env)

(* Lists of values. *)

with vals :=
  | VNil
  | VCons (v : val) (vs : vals)

(* Environments are association lists. *)

with env :=
  | EnvNil
  | EnvCons (x : var) (v : val) (η : env).

(* ------------------------------------------------------------------------ *)

(* Sugar for patterns and expressions. *)

(* Variables. *)

Notation EVar x :=
  (EPath (PathBase x)).

(* Unit. *)

Notation PUnit :=
  (PTuple PNil).

Notation EUnit :=
  (ETuple ENil).

Notation VUnit :=
  (VTuple VNil).

(* Constant constructors, that is, constructors of arity 0. *)

Notation PConstant c :=
  (PData c PUnit).

Notation EConstant c :=
  (EData c EUnit).

Notation VConstant c :=
  (VData c VUnit).

(* The Boolean constants. *)

Definition BoolConstructor (b : bool) :=
  if b then "true" else "false".

Notation PBool b :=
  (PConstant (BoolConstructor b)).

Notation EBool b :=
  (EConstant (BoolConstructor b)).

Notation EFalse :=
  (EBool false).

Notation ETrue :=
  (EBool true).

Notation VBool b :=
  (VConstant (BoolConstructor b)).

Notation VFalse :=
  (VConstant "false").

Notation VTrue :=
  (VConstant "true").

(* Pairs. *)

Notation PPair p1 p2 :=
  (PTuple (PCons p1 (PCons p2 PNil))).

Notation EPair e1 e2 :=
  (ETuple (ECons e1 (ECons e2 ENil))).

Notation VPair v1 v2 :=
  (VTuple (VCons v1 (VCons v2 VNil))).

(* Options. *)

Notation VNone :=
  (VConstant "None").

Notation VSome v :=
  (VData "Some" v).

(* Lists. *)

(* TODO would like to use VNil and VCons, but this causes a name clash *)

Notation pNil :=
  (PConstant "[]").

Notation pCons p1 p2 :=
  (PData "::" (PPair p1 p2)).

Notation eNil :=
  (EConstant "[]").

Notation eCons e1 e2 :=
  (EData "::" (EPair e1 e2)).

Notation vNil :=
  (VConstant "[]").

Notation vCons v1 v2 :=
  (VData "::" (VPair v1 v2)).

(* [p = e]. *)

Definition Binding1 (p : pat) (e : expr) : bindings :=
  let binding := Binding p e in
  BiCons binding BiNil.

(* [let p = e1 in e2]. *)

Definition ELet1 (p : pat) (e1 e2 : expr) :=
  ELet (Binding1 p e1) e2.

(* [let x = e1 in e2]. *)

Definition ELet1Var (x : var) (e1 e2 : expr) :=
  ELet1 (PVar x) e1 e2.

(* [rec f x = e1]. *)

Definition RecBinding1 (f x : var) (e1 : expr) : rec_bindings :=
  let rb := RecBinding f (AnonFun x e1) in
  RecBiCons rb RecBiNil.

(* [let rec f x = e1 in e2]. *)

Definition ELetRec1 (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1 f x e1) e2.

(* [fun x -> e]. *)

Definition EFun (x : var) (e : expr) :=
  EAnonFun (AnonFun x e).

(* ------------------------------------------------------------------------ *)

(* Sugar for module expressions. *)

Fixpoint MkSItems (items : list sitem) : sitems :=
  match items with
  | [] =>
      INil
  | item :: items =>
      ICons item (MkSItems items)
  end.

Definition MkStruct (items : list sitem) : mexpr :=
  MStruct (MkSItems items).

Fixpoint MkPathRev (xs : list name) : path :=
  match xs with
  | [] =>
      (* Not supposed to happen. *)
      PathBase "<error in MkPath>"
  | [x] =>
      PathBase x
  | x :: xs =>
      PathDot (MkPathRev xs) x
  end.

Definition MkPath (xs : list name) : path :=
  MkPathRev (rev xs).

Notation EMkPath xs :=
  (EPath (MkPath xs)).

Notation IOpenMkPath xs :=
  (IOpen (MkPath xs)).

Notation IIncludeMkPath xs :=
  (IInclude (MPath (MkPath xs))).
