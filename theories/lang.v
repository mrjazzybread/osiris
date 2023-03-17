From stdpp Require Export strings.

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

Scheme my_pat_ind :=
  Induction for pat Sort Prop
with my_pats_ind :=
  Induction for pats Sort Prop.

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
  (* A pattern-matching construct. *)
  | EMatch (e : expr) (bs : branches)
  (* A fatal error. *)
  | EAssertFalse

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

Scheme my_expr_ind :=
  Induction for expr Sort Prop
with my_exprs_ind :=
  Induction for exprs Sort Prop
with my_branch_ind :=
  Induction for branch Sort Prop
with my_branches_ind :=
  Induction for branches Sort Prop.

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

Scheme my_val_ind :=
  Induction for val Sort Prop
with my_vals_ind :=
  Induction for vals Sort Prop
with my_env_ind :=
  Induction for env Sort Prop.
