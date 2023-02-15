From stdpp Require Export strings.

(* Variables. *)

Definition var :=
  string.

(* Data constructors. *)

Definition tag :=
  string.

Inductive pat :=
  | PAny
  | PVar (x : var)
  | PTup (ps : pats)
  | PInj (c : tag) (p : pat)

with pats :=
  | PNil
  | PCons (p : pat) (ps : pats).

Scheme my_pat_ind :=
  Induction for pat Sort Prop
with my_pats_ind :=
  Induction for pats Sort Prop.

Inductive expr :=
  (* λ-calculus *)
  | Var (x : var)
  | Rec (f x : var) (e : expr)
  | App (e1 e2 : expr)
  (* Tuples *)
  | Tup (es : exprs)
  (* Sums *)
  | Inj (c : tag) (e : expr)
  (* Match *)
  | Match (e : expr) (bs : branches)

with exprs :=
  | ENil
  | ECons (e : expr) (es : exprs)

with branch :=
  | Branch (pat : pat) (e : expr)

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

Inductive val :=
  | VRec (η : env) (f x : var) (e : expr)
  | VTup (vs : vals)
  | VInj (c : tag) (v : val)

with vals :=
  | VNil
  | VCons (v : val) (vs : vals)

with env :=
  | EnvNil
  | EnvCons (x : var) (v : val) (η : env).

Scheme my_val_ind :=
  Induction for val Sort Prop
with my_vals_ind :=
  Induction for vals Sort Prop
with my_env_ind :=
  Induction for env Sort Prop.
