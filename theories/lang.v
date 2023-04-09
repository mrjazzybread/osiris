Require int.
Require Import base.

(* ------------------------------------------------------------------------ *)

(* Variables. *)

Definition var :=
  string.

(* ------------------------------------------------------------------------ *)

(* Data constructors. *)

Definition data :=
  string.

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
  (* A tuple pattern. *)
  | PTuple (ps : pats)
  (* A data constructor pattern. *)
  | PData (c : data) (p : pat)

(* Lists of patterns. *)

with pats :=
  | PNil
  | PCons (p : pat) (ps : pats).

(* ------------------------------------------------------------------------ *)

(* Expressions. *)

Inductive expr :=

  (* Variable: [x]. *)
  | EVar (x : var)

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

  (* Non-recursive local definition: [let bs in e]. *)
  | ELet (bs : bindings) (e : expr)

  (* Recursive local definition: [let rbs in e]. *)
  | ELetRec (rbs : rec_bindings) (e : expr)

  (* Sequence: [e1; e2]. *)
  | ESeq (e1 e2 : expr)

  (* Conditional: [if e then e1] and [if e then e1 else e2]. *)
  | EIfThen (e e1 : expr)
  | EIfThenElse (e e1 e2 : expr)

  (* Pattern matching: [match e with bs]. *)
  | EMatch (e : expr) (bs : branches)

  (* Loop: [while e do body done]. *)
  | EWhile (e body : expr)

  (* Fatal error: [assert false]. *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)]. *)
  | EAssert (e : expr)

(* Lists of expressions. *)

with exprs :=
  | ENil
  | ECons (e : expr) (es : exprs)

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

.

(* ------------------------------------------------------------------------ *)

(* Values. *)

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

(* Lists of values. *)

with vals :=
  | VNil
  | VCons (v : val) (vs : vals)

(* Environments are association lists. *)

with env :=
  | EnvNil
  | EnvCons (x : var) (v : val) (η : env).

(* ------------------------------------------------------------------------ *)

(* Sugar. *)

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

(* [let p = e1 in e2]. *)

Definition ELet1 (p : pat) (e1 e2 : expr) :=
  let binding := Binding p e1 in
  let bindings := BiCons binding BiNil in
  ELet bindings e2.

(* [let x = e1 in e2]. *)

Definition ELet1Var (x : var) (e1 e2 : expr) :=
  ELet1 (PVar x) e1 e2.

(* [let rec f x = e1 in e2]. *)

Definition RecBinding1 (f x : var) (e1 : expr) :=
  let rb := RecBinding f (AnonFun x e1) in
  RecBiCons rb RecBiNil.

Definition ELetRec1 (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1 f x e1) e2.

(* [fun x -> e]. *)

Definition EFun (x : var) (e : expr) :=
  EAnonFun (AnonFun x e).
