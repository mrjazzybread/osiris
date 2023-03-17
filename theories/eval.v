Require Import lang monads free.

(* Conventional metavariables. *)

Implicit Type f x : var.
Implicit Type c : data.
Implicit Type p : pat.
Implicit Type ps : pats.
Implicit Type e : expr.
Implicit Type es : exprs.
Implicit Type b : branch.
Implicit Type bs : branches.
Implicit Type v : val.
Implicit Type vs : vals.
Implicit Type η : env.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

Local Notation fail :=
  Fail.

Local Notation stop :=
  Stop.

Local Notation ok :=
  (ret VUnit).

(* ------------------------------------------------------------------------ *)

(* [lookup η x] looks up the variable [x] in the environment [env].
   The result is normally a value. A hard failure occurs if [x] is
   unbound. *)

Fixpoint lookup η x : free val :=
  match η with
  | EnvCons x' v η =>
      if decide (x = x') then ret v else lookup η x
  | EnvNil =>
      fail (* unbound variable *)
  end.

(* ------------------------------------------------------------------------ *)

(* [extend η p v] matches the value [v] against the pattern [p].

   In case of success, the result is an extension of the environment
   [η] with bindings for the bound variables of the pattern [p].

   A soft failure takes place if [p] does not match [v], e.g., if [p]
   selects a data constructor [c] but [v] carries a distinct data
   constructor [c'].

   A hard failure takes place if [p] and [v] have incompatible types,
   e.g., if [p] is a tuple pattern and [v] is not a tuple value or
   is a tuple value of an incorrect arity. *)

Fixpoint extend η p v : free env :=
  match p, v with
  | PAny, _ =>
      (* A wildcard pattern always succeeds. *)
      ret η
  | PVar x, _ =>
      (* A variable pattern always succeeds, and causes the environment
         to be extended. *)
      ret (EnvCons x v η)
  | PTuple ps, VTuple vs =>
      (* A tuple pattern matches a tuple value. *)
      (* A hard failure occurs when [length ps ≠ length vs]. *)
      extends η ps vs
  | PData c p, VData c' v =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a soft failure takes
         place. *)
      if decide (c = c') then extend η p v else Next
  | PTuple _, _
  | PData _ _, _ =>
      (* A type mismatch between pattern and value causes a hard failure. *)
      fail (* type mismatch *)
  end

(* [extends η ps vs] matches the values [vs] against the patterns [ps].

   In case of success, the result is an extension of the environment
   [η] with bindings for the bound variables of the patterns [ps].

   A hard failure occurs when [length ps ≠ length vs]. *)

with extends η ps vs : free env :=
  match ps, vs with
  | PNil, VNil =>
      ret η
  | PCons p ps, VCons v vs =>
      bind (extend η p v) $ λ η,
      bind (extends η ps vs) $ λ η,
      ret η
  | _, _ =>
      fail (* length mismatch *)
  end.

(* ------------------------------------------------------------------------ *)

(* [call v1 v2] evaluates the function call [v1 v2]. *)

Definition call v1 v2 : free val :=
  match v1 with
  | VRec η f x e =>
      (* The environment of the closure is extended with bindings
         for the variables [f] and [x]. *)
      let η := EnvCons f v1 η in
      let η := EnvCons x v2 η in
      (* In this extended environment, the function body [e] must
         be evaluated. A recursive call to [eval] cannot be used,
         so we request the evaluation of [e] via a [stop] effect. *)
      stop η e $ λ v,
      ret v
 | _ =>
     fail (* type mismatch: closure expected *)
 end.

(* ------------------------------------------------------------------------ *)

(* [as_bool v] checks that the value [v] is a language-level Boolean value
   and returns its meta-level Boolean value. *)

Definition as_bool (v : val) : free bool :=
  match v with
  | VFalse =>
      ret false
  | VTrue =>
      ret true
  | _ =>
      fail (* type mismatch: Boolean value expected *)
  end.

(* ------------------------------------------------------------------------ *)

(* [eval η e] evaluates the expression [e] in environment [η].

   In case of success, the result is a value.

   A hard failure reflects a dynamic type error (a crash).

   A soft failure is impossible.

   No substitutions are involved; this is an environment-based semantics.

   [eval] is inductively defined. In some cases, it invokes itself
   recursively on a subexpression of [e]. When an expression must be
   evaluated but is not a subexpression of [e], a [stop] effect is
   used instead of a recursive call to [eval]. *)

Fixpoint eval η e : free val :=
  match e with
  | EVar x =>
      (* A variable [x] is looked up in the environment [η]. *)
      lookup η x
  | ERec f x e =>
      (* The creation of a closure captures the environment [η]. *)
      ret (VRec η f x e)
  | EApp e1 e2 =>
      (* The left-hand side of an application must evaluate
         to a closure. *)
      bind (eval η e1) $ λ v1,
      bind (eval η e2) $ λ v2,
      call v1 v2
  | ETuple es =>
      bind (evals η es) $ λ vs,
      ret (VTuple vs)
  | EData c e =>
      bind (eval η e) $ λ v,
      ret (VData c v)
  | EMatch e bs =>
      bind (eval η e) $ λ v,
      eval_match η v bs
  | EAssertFalse =>
      mzero
  end

(* [evals η es] evaluates the expressions in the list [es], from left
   to right, producing a list of values [vs]. *)

with evals η es : free vals :=
  match es with
  | ENil =>
      ret VNil
  | ECons e es =>
      bind (eval η e) $ λ v,
      bind (evals η es) $ λ vs,
      ret (VCons v vs)
  end

(* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)

with eval_match η v bs :=
  match bs with
  | BNil =>
      (* A nonexhaustive [match] construct causes a hard failure. *)
      fail
  | BCons (Branch p e) bs =>
      (* Match the value [v] against the pattern [p]. *)
      try
        (extend η p v)
      (* Success: commit to this branch. Evaluate its body. *)
      (λ η, eval η e)
      (* Soft failure: abandon this branch. Try the following branches. *)
      (λ tt, eval_match η v bs)
  end.
