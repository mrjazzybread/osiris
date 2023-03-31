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

  (* A variable. *)
  | EVar (x : var)

  (* A (recursive) closure construction expression. *)
  | ERec (f x : var) (e : expr)
  (* A function call. *)
  | EApp (e1 e2 : expr)

  (* A tuple construction expression. *)
  | ETuple (es : exprs)

  (* A data constructor application expression. *)
  | EData (c : data) (e : expr)

  (* Conditionals. *)
  | EIfThen (e e1 : expr)
  | EIfThenElse (e e1 e2 : expr)
  (* A pattern-matching construct. *)
  | EMatch (e : expr) (bs : branches)

  (* A fatal error. *)
  | EAssertFalse
  (* A runtime assertion. *)
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

Definition ELet p e1 e2 :=
  EMatch e1 (BCons (Branch p e2) BNil).

Definition ELetVar x e1 e2 :=
  ELet (PVar x) e1 e2.

(* Sequencing. *)

(* Sequencing is defined using a wildcard pattern, as opposed to a unit
   pattern, because this removes a runtime test, therefore removes a static
   proof obligation as well. This proof obligation would always succeed (in
   a well-typed program) but would be noisy. *)

Definition ESeq e1 e2 :=
  ELet PAny e1 e2.
