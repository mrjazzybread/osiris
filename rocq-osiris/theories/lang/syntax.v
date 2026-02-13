From osiris Require Import base.
From osiris.lang Require Import float int char locations thread_ids.

(* This file should be in sync with osiris/src/Syntax.ml. *)

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

Definition path := list name.

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

(* In OCaml, a data constructor or field can be a qualified name. Here, only
   a short (unqualified) name is retained; the rest is irrelevant. *)

(* ------------------------------------------------------------------------ *)

(* First-class continuations. *)

Definition cont :=
  tc_opaque loc.

(* ------------------------------------------------------------------------ *)

(* Machine integers. *)

Notation int :=
  int.int.

(* Characters. *)

Definition char :=
  Ascii.ascii.

(* ------------------------------------------------------------------------ *)

(* Patterns. *)

(* An ordinary pattern, or value pattern, has type [pat].
   Such a pattern is used in a case analysis on a value. *)

Inductive pat :=
  (* A placeholder for as-yet-unsupported constructs. *)
  | PUnsupported
  (* The wildcard pattern. *)
  | PAny
  (* A variable. *)
  | PVar (x : var)
  (* An alias pattern [p as x]. *)
  | PAlias (p : pat) (x : var)
  (* A disjunction pattern [p1 | p2]. *)
  | POr (p1 p2 : pat)
  (* A tuple pattern. *)
  | PTuple (ps : list pat)
  (* A data constructor pattern in an ordinary algebraic data type. *)
  | PData (c : data) (ps : list pat)
  (* A data constructor pattern in an extensible algebraic data type.
     In [PXData (π, ps)], the path [π] is expected to denote a memory
     location, which serves as a dynamically-allocated name. *)
  | PXData (π : path) (ps : list pat)
  (* A record pattern. *)
  | PRecord (fps : list (field * pat))
  (* A literal integer pattern. *)
  | PInt (i : Z)
  (* A literal character pattern. *)
  | PChar (c: char)
  (* A literal string pattern. *)
  | PString (s : string).

(* Computation patterns. *)

(* A computation pattern [cp] has type [cpat]. Such a pattern is used
   in a case analysis on a three-branch outcome, which represents a
   value, an exception, or an effect. *)

Inductive cpat :=
  (* This pattern matches a normal termination outcome. It guards the
     "return branch" in an effect handler. In OCaml's concrete syntax,
     it corresponds to the absence of an [exception] or [effect]
     keyword in a [match] construct. *)
  | CVal (p : pat)
  (* This pattern matches an exceptional outcome. In OCaml's concrete
     syntax, it corresponds to the presence of the [exception] keyword
     in a [match] branch. *)
  | CExc (p : pat)
  (* This pattern matches an effect. In OCaml's concrete syntax, it
     corresponds to the presence of the [effect] keyword in a [match]
     branch. *)
  | CEff (p : pat) (k : pat)
  (* A disjunction pattern [cp1 | cp2]. *)
  | COr (cp1 : cpat) (cp2 : cpat).

(* ------------------------------------------------------------------------ *)

(* Module coercions. *)

(* Module coercions can be understood as a very impoverished form of module
   types. They play a role in the dynamic semantics of the shape restriction
   operation on modules. *)

Inductive coercion :=
  (* The coercion [CIdentity] has no effect. *)
  | CIdentity

  (* The coercion [CStruct cs] expects to be applied to a structure. The
     fields named in the list [xcs] are retained, and the corresponding
     coercions in the list [xcs] are applied to them. All other fields are
     dropped. *)
| CStruct (xcs : list (field * coercion)).

Definition fcoercion :=
  (var * coercion)%type.

Definition fcoercions :=
  list fcoercion.
      (* A field-coercion list [xcs] must have no duplicate names. *)

(* ------------------------------------------------------------------------ *)

(* Expressions. *)

Inductive expr :=

  (* A placeholder for as-yet-unsupported constructs. *)
  | EUnsupported

  (* Path: [x] or [π.x]. *)
  | EPath (x : path)

  (* An anonymous function. *)
  | EAnonFun (a : anonfun)

  (* Function application: [e1 e2]. *)
  (* Every function is considered unary. *)
  | EApp (e1 e2 : expr)

  (* Tuple construction: [(e1, e2, ...)]. *)
  | ETuple (es : list expr)

  (* Data constructor application: [A (e)]. *)
  (* Every data constructor is considered unary. *)
  | EData (c : data) (e : list expr)
  | EXData (π : path) (e : list expr)

  (* Record construction: [{ fs = es }]. *)
  | ERecord (fes : list fexpr)
  (* Record update: [{ e with fs = es }]. *)
  | ERecordUpdate (e : expr) (fes : list fexpr)
  (* Record access: [e.f]. *)
  | ERecordAccess (e : expr) (f : field)

  (* An array literal: [ [|1;2;3|] ] *)
  | EArrayLit (es : list expr)
  (* Length of an array: [Array.length a] *)
  | EArrayLength (e : expr)
  (* Array access with bounds check: [Array.get a n] *)
  | EArrayGet (e1 e2 : expr)
  (* Array update with bounds check: [Array.set a n v] *)
  | EArraySet (e1 e2 e3 : expr)
  (* Array creation: [Array.make n v] *)
  | EArrayMake (e1 e2 : expr)

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
  (* Integer logical operations. *)
  | EIntLand (e1 e2 : expr)
  | EIntLor  (e1 e2 : expr)
  | EIntLxor (e1 e2 : expr)
  | EIntLnot (e : expr)
  | EIntLsl  (e1 e2 : expr)
  | EIntLsr  (e1 e2 : expr)
  | EIntAsr  (e1 e2 : expr)

  (* Floating-point literals. *)
  | EFloat (f : float)

  (* Character literals. *)
  | EChar (c: char)

  (* String literals. *)
  | EString (s: string)

  (* Polymorphic comparison operators. *)
  | EOpPhysEq (e1 e2 : expr)
  | EOpEq (e1 e2 : expr)
  | EOpNe (e1 e2 : expr)
  | EOpLt (e1 e2 : expr)
  | EOpLe (e1 e2 : expr)
  | EOpGt (e1 e2 : expr)
  | EOpGe (e1 e2 : expr)

  (* Non-recursive local definition: [let bs in e]. *)
  | ELet (bs : list binding) (e : expr)

  (* Recursive local definition: [let rbs in e]. *)
  | ELetRec (rbs : list rec_binding) (e : expr)

  (* Local module definition: [let module M = me in e]. *)
  | ELetModule (M : module) (me : mexpr) (e : expr)

  (* Local [open] directive: [let open me in e]. *)
  | ELetOpen (me : mexpr) (e : expr)

  (* Sequence: [e1; e2]. *)
  | ESeq (e1 e2 : expr)

  (* Conditional: [if e then e1] and [if e then e1 else e2]. *)
  | EIfThen (e e1 : expr)
  | EIfThenElse (e e1 e2 : expr)

  (* Pattern matching: [match e with bs]. *)
  | EMatch (e : expr) (bs : list branch)
  (* Pattern matching with shallow handling of effects. *)
  | EShallowMatch (e : expr) (bs : list branch)

  (* Raising an exception: [raise e]. *)
  | ERaise (e : expr)

  (* Performing an effect: [perform e]. *)
  | EPerform (e : expr)
  (* Continuing a continuation: [continue e1 e2]. *)
  | EContinue (e1 : expr) (e2 : expr)
  (* Discontinuing a continuation: [discontinue e1 e2]. *)
  | EDiscontinue (e1 : expr) (e2 : expr)

  (* Loop: [while e do body done]. *)
  | EWhile (e body : expr)
  (* Loop: [for x = e1 to e2 do e done]. *)
  | EFor (x : var) (e1 e2 e : expr)

  (* Fatal error: [assert false]. *)
  (* We model OCaml's unreachable construct [.] in this way, too. *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)]. *)
  | EAssert (e : expr)

  (* Reference allocation: [ref e]. *)
  | ERef (e : expr)
  (* Reference lookup: [!e]. *)
  | ELoad (e : expr)
  (* Reference assignment: [e1 := e2]. *)
  | EStore (e1 e2: expr)

  (* Creating a thread: ≈ [Thread.create f arg]. *)
  | EFork (e1 e2 : expr)
  (* Waiting for another thread to terminate: ≈ [Domain.join th]. *)
  | EJoin (e : expr)

(* Field-expression pairs. *)

with fexpr :=
  | Fexpr (f : field)  (e : expr)

(* A branch is of the form [cp -> e],
   where [cp] is a computation pattern. *)

with branch :=
  | Branch (cp : cpat) (e : expr)

(* A binding is of the form [p = e]. *)

with binding :=
  | Binding (p : pat) (e : expr)

(* A recursive binding is of the form [f = a]. *)

with rec_binding :=
  | RecBinding (f : var) (a : anonfun)

(* An anonymous function is of the form [fun x -> e]. We allow only
   this form as a primitive construct, because this simplifies the
   evaluator. The constructs [function bs], where [bs] is a list of
   branches, and [fun ps -> e], where [ps] is a list of patterns, are
   regarded as sugar: see [EFunction] and [EFunMultiPat]. *)

with anonfun :=
  | AnonFun (x : var) (e : expr)

(* ------------------------------------------------------------------------ *)

(* Module expressions. *)

with mexpr :=

  (* A placeholder for as-yet-unsupported constructs. *)
  | MUnsupported

  (* A module path. *)
  | MPath (π : path)

  (* A structure [struct ... end]. *)
  | MStruct (items : list sitem)

  (* A functor [functor _ -> struct ... end]. *)
  | MFunctor (x : var) (items : list sitem)

  (* A coercion, that is, a shape restriction operation. This operation is
     written [M : S] in OCaml surface syntax, and is sometimes implicit: for
     example, a functor application [F(M)] must be understood as [F(M : S)]
     where [S] is the expected shape of the argument of the functor [F]. *)
  | MCoercion (me : mexpr) (c : coercion)

(* Structure items. *)

with sitem :=

  (* A non-recursive toplevel definition [let bs]. *)
  | ILet (bs : list binding)

  (* A recursive toplevel definition [let rec rbs]. *)
  | ILetRec (rbs : list rec_binding)

  (* A module definition [M = me]. *)
  | IModule (m : module) (me : mexpr)

  (* An [open] directive [open me]. *)
  | IOpen (me : mexpr)

  (* An [include] directive [include me]. *)
  | IInclude (me : mexpr)

  (* An extensible variant type extension [type t += cs]. *)
  | IExtend (cs : list name)

.

(* ------------------------------------------------------------------------ *)

(* A handler is a list of branches. *)

Definition handler := list branch.

(* ------------------------------------------------------------------------ *)

(* Values. *)

(* These values serve as values both for expressions and for module
   expressions. Similarly, environments map both variables to values
   and modules to values. *)

Inductive val : Type :=
  (* A simple (non-recursive) closure. *)
  | VClo (η : list (var * val)) (a : anonfun)
  (* A recursive closure. *)
  (* [η] is the environment at the closure creation site. It does not include
     entries for the functions defined by the recursive bindings [rbs]. *)
  (* The recursive bindings [rbs] are those of the closure creation site. *)
  (* The name [f] is the closure's entry point. *)
  | VCloRec (η : list (var * val)) (rbs : list rec_binding) (f : var)
  (* A string. *)
  | VString (s: string)
  (* A machine integer. *)
  | VInt (i : int)
  (* A floating-point number. *)
  | VFloat (f : float)
  (* A tuple. *)
  | VTuple (vs : list val)
  (* A data constructor value. *)
  | VData (c : data) (v : list val)
  (* A data constructor value for an extensible type. *)
  (* Extension constructors are dynamically alocated to the heap.
     [l] is the location of the constructor. Extensible types can
     alias by having two constructors point to the same location. *)
  | VXData (l : loc) (v : list val)
  (* A record. *)
  (* A list of field-value pairs is the same thing as an environment,
     so, for the moment at least, we identify these concepts. *)
  (* The fields in a record are always pairwise distinct (this is checked
     by OCaml, not by us) and alphabetically sorted. *)
  | VRecord (fvs : list (var * val))
  (* An array is represented as the list of locations of its elements. *)
  | VArray (l : list loc)
  (* A location. *)
  | VLoc (l: loc)
  (* A thread id. *)
  | VThread (t: thread)
  (* A continuation; more precisely, a location which stores a continuation. *)
  | VCont (k: cont)
  (* A module. *)
  | VStruct (xvs : list (var * val))
  (* A functor. *)
  | VFunctor (η : list (var * val)) (x : var) (xvs : list sitem)
  | VChar (c: char)
.

Definition env := list (var * val).


(* ------------------------------------------------------------------------ *)

(* Core sugar, used in eval.v. *)

(* More sugar is defined in sugar.v. *)

(* Unit. *)

Notation PUnit :=
  (PData "()" $ []).

Notation EUnit :=
  (EData "()" $ []).

Notation VUnit :=
  (VData "()" $ []).

(* Constant constructors, that is, constructors of arity 0. *)

Notation PConstant c :=
  (PData c $ []).

Notation EConstant c :=
  (EData c $ []).

Notation VConstant c :=
  (VData c $ []).

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

(* ------------------------------------------------------------------------ *)

(* Lemmas about the auxiliary function [BoolConstructor]. *)

Lemma BoolConstructor_injective b1 b2 :
  BoolConstructor b1 = BoolConstructor b2 →
  b1 = b2.
Proof.
  destruct b1, b2; simpl; congruence.
Qed.

Lemma BoolConstructor_congruent_contrapositive b1 b2 :
  BoolConstructor b1 ≠ BoolConstructor b2 →
  b1 ≠ b2.
Proof.
  congruence.
Qed.
