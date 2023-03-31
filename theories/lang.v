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

  (* A (recursive) closure construction expression. *)
  (* TODO does not exist in OCaml *)
  | ERec (f x : var) (e : expr)

  (* Function application: [e1 e2]. *)
  (* Every function is considered unary. *)
  | EApp (e1 e2 : expr)

  (* Tuple construction: [(e1, e2, ...)]. *)
  | ETuple (es : exprs)

  (* Data constructor application: [A (e)]. *)
  (* Every data constructor is considered unary. *)
  | EData (c : data) (e : expr)

  (* Local definition: [let p = e1 in e2]. *)
  | ELet (p : pat) (e1 e2 : expr)

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
  | Branch (pat : pat) (e : expr)

(* Lists of branches. *)

with branches :=
  | BNil
  | BCons (b : branch) (bs : branches).

(* ------------------------------------------------------------------------ *)

(* Values. *)

Inductive val :=
  (* A (recursive) closure. *)
  | VRec (η : env) (f x : var) (e : expr)
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

Notation PFalse :=
  (PConstant "false").

Notation PTrue :=
  (PConstant "true").

Notation EFalse :=
  (EConstant "false").

Notation ETrue :=
  (EConstant "true").

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

(* Local definition constructs. *)

Definition ELetVar x e1 e2 :=
  ELet (PVar x) e1 e2.
