Require Import lang base free.

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

(* Codes for effects. *)

(* The code [Eval (η, e)] is a request for a recursive call [eval η e]. *)

(* The code [Flip] is a request to flip a Boolean coin. *)

Inductive code : Type → Type → Type :=
| Eval : code (env * expr) val
| Flip : code unit bool
.

(* We fix this particular type of codes. *)

Notation free :=
  (@free.free code).

(* [flip] flips a coin. *)

Definition flip : free bool :=
  stop Flip ().

(* [choose m1 m2] is a non-deterministic choice between the
   computations [m1] and [m2]. *)

Definition choose {A} (m1 m2 : free A) : free A :=
  b ← flip ;
  if (b : bool) then m1 else m2.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

(* [ok] is an inert computation. It produces the value [VUnit]. *)

Notation ok :=
  (ret VUnit).

(* ------------------------------------------------------------------------ *)

(* [lookup η x] looks up the variable [x] in the environment [env].
   The result is normally a value. A hard failure occurs if [x] is
   unbound. *)

Fixpoint lookup η x : free val :=
  match η with
  | EnvCons x' v η =>
      if x =? x' then ret v else lookup η x
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

(* We assume that the pattern [p] is linear: that is, no variable is
   bound twice. This property is enforced by the OCaml type-checker. *)

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
      if c =? c' then extend η p v else next()
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
      η ← extend η p v ;
      η ← extends η ps vs ;
      ret η
  | _, _ =>
      fail (* length mismatch *)
  end.

(* ------------------------------------------------------------------------ *)

(* [call v1 v2] evaluates the function call [v1 v2]. *)

Definition call v1 v2 : free val :=
  (* The value [v1] must be a closure. *)
  match v1 with
  | VRec η f x e =>
      (* The environment of the closure is extended with bindings
         for the variables [f] and [x]. *)
      let η := EnvCons f v1 η in
      let η := EnvCons x v2 η in
      (* In this extended environment, the function body [e] must
         be evaluated. A recursive call to [eval] cannot be used,
         so we request the evaluation of [e] via a [stop] effect. *)
      stop Eval (η, e)
 | _ =>
     fail (* type mismatch: closure expected *)
 end.

(* ------------------------------------------------------------------------ *)

(* [val_as_bool v] checks that the value [v] is a language-level Boolean
   value and returns its meta-level Boolean value. *)

Definition val_as_bool (v : val) : free bool :=
  match v with
  | VFalse =>
      ret false
  | VTrue =>
      ret true
  | _ =>
      fail (* type mismatch: Boolean value expected *)
  end.

Definition as_bool (m : free val) : free bool :=
  bind m val_as_bool.

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

(* In a binary application [e1 e2], the expressions [e1] and [e2] are
   evaluated in parallel. This allows an interleaving of steps inside [e1]
   and steps inside [e2]. This is more permissive than a choice between the
   sequence [e1; e2] and the sequence [e2; e1]. As a result, in an n-ary
   application [e1 e2 ... en], the expressions [e1], [e2], ... [en] can be
   evaluated in an arbitrary order. That is, an arbitrary permutation of
   these expressions is possible: the evaluation order is not necessarily
   left-to-right or right-to-left. *)

Fixpoint eval η e : free val :=
  match e with
  | EVar x =>
      (* A variable [x] is looked up in the environment [η]. *)
      lookup η x
  | ERec f x e =>
      (* The creation of a closure captures the environment [η]. *)
      ret (VRec η f x e)
  | EApp e1 e2 =>
      (* The expressions [e1] and [e2] are evaluated in parallel. *)
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      call v1 v2
  | ETuple es =>
      (* The tuple components are evaluated in parallel. *)
      vs ← evals η es ;
      ret (VTuple vs)
  | EData c e =>
      v ← eval η e ;
      ret (VData c v)
  | EIfThen e e1 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else ok
  | EIfThenElse e e1 e2 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else eval η e2
  | EMatch e bs =>
      v ← eval η e ;
      eval_match η v bs
  | EAssertFalse =>
      fail (* assertion failure *)
  | EAssert e =>
      (* OCaml runtime assertions are erased when a module is compiled with
         the compiler flag [-noassert]; they are retained otherwise. We do not
         wish to depend on this flag, so we make a non-deterministic choice:
         either the runtime test is executed, or it is skipped. This forces
         the user to prove that the program is safe in both scenarios. *)
      let test : free val :=
        success ← as_bool (eval η e) ;
        if (success : bool) then ok else fail (* assertion failure *)
      in
      choose ok test
  end

(* [evals η es] evaluates the expressions in the list [es] in parallel,
   producing a list of values [vs]. *)

with evals η es : free vals :=
  match es with
  | ENil =>
      ret VNil
  | ECons e es =>
      '(v, vs) ← par (eval η e) (evals η es) ;
      ret (VCons v vs)
  end

(* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)

with eval_match η v bs :=
  match bs with
  | BNil =>
      (* A nonexhaustive [match] construct causes a hard failure. *)
      (* Because the proof system forbids hard failures, the user of
         the system will have to prove that this cannot happen, i.e.,
         every case analysis is exhaustive. *)
      fail (* nonexhaustive case analysis *)
  | BCons (Branch p e) bs =>
      (* Match the value [v] against the pattern [p]. *)
      try
        (extend η p v)
      (* Success: commit to this branch. Evaluate its body. *)
      (λ η, eval η e)
      (* Soft failure: abandon this branch. Try the following branches. *)
      (λ tt, eval_match η v bs)
  end.
