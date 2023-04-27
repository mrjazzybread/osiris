Require Import lang base free.

(* Conventional metavariables. *)

Implicit Type g x : var.
Implicit Type c : data.
Implicit Type f : field.
Implicit Type p : pat.
Implicit Type ps : pats.
Implicit Type e : expr.
Implicit Type es : exprs.
Implicit Type fes : fexprs.
Implicit Type a : anonfun.
Implicit Type v : val.
Implicit Type vs : vals.
Implicit Type fvs : env.
Implicit Type η δ : env.
Implicit Type rbs : rec_bindings.
Implicit Type i : int.

(* ------------------------------------------------------------------------ *)

(* Codes for effects. *)

(* The code [Eval (η, e)] is a request for the computation [eval η e]. *)

(* The code [Loop (η, x, i1, i2, e)] is a request for the computation
   [loop η x v1 v2 e]. *)

(* The code [Flip] is a request to flip a Boolean coin. *)

Inductive code : Type → Type → Type :=
| Eval : code (env * expr) val
| Loop : code (env * var * int * int * expr) val
| Flip : code unit bool
.

(* We fix this particular type of codes. *)

Notation free :=
  (@free.free code).

Notation ret :=
  (@free.ret code).

(* [flip] flips a coin. *)

Definition flip : free bool :=
  stop Flip ().

(* [choose m1 m2] is a non-deterministic choice between the
   computations [m1] and [m2]. *)

Definition choose {A} (m1 m2 : free A) : free A :=
  b ← flip ;
  if (b : bool) then m1 else m2.

(* ------------------------------------------------------------------------ *)

(* Crashes. *)

(* Most kinds of crashes cannot occur in well-typed code, but some can,
   namely, pattern matching failures (caused by nonexhaustive case analyses)
   and assertion failures. *)

Definition crash {A} (msg : string) : free A :=
  fail.

Definition assertion_failure {A} : free A :=
  fail.

Definition match_failure {A} (tt : unit) : free A :=
  fail.

Definition missing_field {A} (f : field) : free A :=
  fail.

Definition unbound_variable {A} (x : var) : free A :=
  fail.

Global Opaque
  crash
  assertion_failure
  match_failure
  missing_field
  unbound_variable
.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

(* [ok] is an inert computation. It produces the value [VUnit]. *)

Notation ok :=
  (ret VUnit).

(* ------------------------------------------------------------------------ *)

(* [lookup η x] looks up the variable [x] in the environment [env].
   The result is normally a value. A hard failure occurs if [x] is
   unbound. *)

(* [lookup] is also used to look up fields in records. In that case,
   the [unbound_variable] error should really be a [missing_field]
   error. TODO FIX? *)

Fixpoint lookup η x : free val :=
  match η with
  | EnvCons x' v η =>
      if x =? x' then ret v else lookup η x
  | EnvNil =>
      unbound_variable x
  end.

Global Arguments lookup !η !x : simpl nomatch.

(* ------------------------------------------------------------------------ *)

(* [concat δ η] concatenates the environment fragment [δ] in front of the
   environment [η], yielding an extended environment. *)

Fixpoint concat δ η : env :=
  match δ with
  | EnvNil =>
      η
  | EnvCons x v δ =>
      EnvCons x v (concat δ η)
  end.

Global Arguments concat !δ η : simpl nomatch.

(* ------------------------------------------------------------------------ *)

(* [remove f fvs] removes field [f] from the field-value list [fvs]. *)

Fixpoint remove f fvs : free env :=
  match fvs with
  | EnvCons f' v fvs =>
      if f =? f' then
        ret fvs
      else
        fvs ← remove f fvs ;
        ret (EnvCons f' v fvs)
  | EnvNil =>
      missing_field f
  end.

Global Arguments remove !f !fvs : simpl nomatch.

(* ------------------------------------------------------------------------ *)

(* [update fvs fvs'] updates the existing record fields [fvs] with the new
   record fields [fvs']. *)

Fixpoint update fvs fvs' : free env :=
  match fvs' with
  | EnvNil =>
      ret fvs
  | EnvCons f v' fvs' =>
      fvs ← remove f fvs ;
      let fvs := EnvCons f v' fvs in
      update fvs fvs'
  end.

Global Arguments update !fvs !fvs' : simpl nomatch.

(* ------------------------------------------------------------------------ *)

(* A [sort] function for lists of string-value pairs, also known as
   environments. *)

(* A painful difficulty is that [env] is a custom type of lists, so the
   standard [sort] function cannot be applied directly to it. We extract a
   list of keys, sort this list, then reconstruct a sorted environment by
   performing lookups in the original environment. This has quadratic cost,
   but all of operations on environments and records have quadratic cost
   anyway. *)

Require Import Orders Sorting.

Module StringOrder <: TotalLeBool.
  Definition t := string.
  Definition leb := String.leb.
  Definition leb_total := String.leb_total.
End StringOrder.

Module Import StringSort := Sort StringOrder.

Fixpoint domain (η : env) : list string :=
  match η with
  | EnvNil =>
      []
  | EnvCons x v η =>
      x :: domain η
  end.

Fixpoint build (η : env) (xs : list string) : free env :=
  match xs with
  | [] =>
      ret EnvNil
  | x :: xs =>
      v ← lookup η x ;
      xs ← build η xs ;
      ret (EnvCons x v xs)
  end.

Definition sort (η : env) : free env :=
  build η (sort (domain η)).

(* ------------------------------------------------------------------------ *)

(* [eval_rec_bindings_aux η rbs rbs'] transforms the bindings [rbs'] into an
   environment fragment. Each name [g] is mapped to a recursive closure that
   captures the environment [η] and the bindings [rbs]. *)

(* The parameters [η] and [rbs] are invariant. At the beginning, [rbs']
   is [rbs], so, in general, [rbs'] is a suffix of [rbs]. *)

Fixpoint eval_rec_bindings_aux η rbs rbs' : env :=
  match rbs' with
  | RecBiNil =>
      EnvNil
  | RecBiCons (RecBinding g _a) rbs' =>
      EnvCons g (VCloRec η rbs g) (eval_rec_bindings_aux η rbs rbs')
  end.

(* [eval_rec_bindings η rbs] transforms the bindings [rbs] into an environment
   fragment. Each name [g] is mapped to a recursive closure that captures the
   environment [η] and the bindings [rbs]. *)

Definition eval_rec_bindings η rbs : env :=
  eval_rec_bindings_aux η rbs rbs.

(* ------------------------------------------------------------------------ *)

(* [lookup_rec_bindings rbs g] looks up the function [g] in the recursive
   bindings [rbs]. The right-hand side is an anonymous function [a]. *)

Fixpoint lookup_rec_bindings rbs g : free anonfun :=
  match rbs with
  | RecBiCons (RecBinding g' a) rbs =>
      if g =? g' then ret a else lookup_rec_bindings rbs g
  | RecBiNil =>
      unbound_variable g
  end.

(* ------------------------------------------------------------------------ *)

(* [extend δ p v] matches the value [v] against the pattern [p].

   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of the pattern [p].

   A soft failure takes place if [p] does not match [v], e.g., if [p]
   selects a data constructor [c] but [v] carries a distinct data
   constructor [c'].

   A hard failure takes place if [p] and [v] have incompatible types,
   e.g., if [p] is a tuple pattern and [v] is not a tuple value or
   is a tuple value of an incorrect arity. *)

(* We assume that the pattern [p] is linear: that is, no variable is
   bound twice. This property is enforced by the OCaml type-checker. *)

Fixpoint extend δ p v : free env :=
  match p, v with
  | PAny, _ =>
      (* A wildcard pattern always succeeds. *)
      ret δ
  | PVar x, _ =>
      (* A variable pattern always succeeds, and causes the environment
         to be extended. *)
      ret (EnvCons x v δ)
  | PAlias p x, _ =>
      (* An alias pattern [p as x] is an intersection pattern: the value
         [v] must match both the pattern [p] and the pattern [x]. *)
      δ ← extend δ p v ;
      ret (EnvCons x v δ)
  | POr p1 p2, _ =>
      (* A disjunction pattern [p1 | p2] requires that the value [v]
         match either [p1] or [p2]. *)
      orelse (extend δ p1 v) (extend δ p2 v)
  | PTuple ps, VTuple vs =>
      (* A tuple pattern matches a tuple value. *)
      (* A hard failure occurs when [length ps ≠ length vs]. *)
      extends δ ps vs
  | PData c p, VData c' v =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a soft failure takes
         place. *)
      if c =? c' then extend δ p v else next()
  | PRecord fps, VRecord fvs =>
      (* A record pattern matches a record value. *)
      (* The pattern may have fewer fields than the value. *)
      (* A hard failure occurs if a field is present in the pattern
         but absent in the value. *)
      extendfs δ fps fvs
  | PInt z, VInt i' =>
      let i := int.repr z in
      if int.eq i i' then ret δ else next()
  | PTuple _, _ =>
      crash "type mismatch (tuple expected)"
  | PData _ _, _ =>
      crash "type mismatch (algebraic data expected)"
  | PRecord _, _ =>
      crash "type mismatch (record expected)"
  | PInt _, _ =>
      crash "type mismatch (integer expected)"
  end

(* [extends δ ps vs] matches the values [vs] against the patterns [ps].

   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of the patterns [ps].

   A hard failure occurs when [length ps ≠ length vs]. *)

(* For now, pattern matching is sequential. Parallel evaluation would
   make sense once we enable pattern matching on mutable state. *)

with extends δ ps vs : free env :=
  match ps, vs with
  | PNil, VNil =>
      ret δ
  | PCons p ps, VCons v vs =>
      δ ← extend δ p v ;
      δ ← extends δ ps vs ;
      ret δ
  | PCons _ _, VNil =>
      crash "pattern matching: length mismatch (longer tuple expected)"
  | PNil, VCons _ _ =>
      crash "pattern matching: length mismatch (shorter tuple expected)"
  end

(* [extendfs δ fps fvs] matches the field-indexed values [fvs] against the
   field-indexed patterns [fps].

   In case of success, the result is an extension of the environment fragment
   [δ] with bindings for the bound variables of the patterns [fps].

   A hard failure occurs if a field is present in [fps] but absent in [fvs]. *)

with extendfs δ fps fvs : free env :=
  match fps with
  | FPNil =>
      ret δ
  | FPCons f p fps =>
      v ← lookup fvs f ;
      δ ← extend δ p v ;
      δ ← extendfs δ fps fvs ;
      ret δ
  end.

Global Arguments extend δ !p v.
Global Arguments extends δ !ps !vs.
Global Arguments extendfs δ !fps !fvs.

(* ------------------------------------------------------------------------ *)

(* [acall η a v] evaluates the application of the anonymous function [a]
   to the value [v] in the environment [η]. *)

Definition acall η a v : free val :=
  (* An anonymous function [a] is of the form [fun x -> e]. *)
  let '(AnonFun x e) := a in
  (* Extend the environment [η] with a binding of the variable [x]
     to the value [v]. *)
  let η := EnvCons x v η in
  (* Then, evaluate the function body [e]. A recursive call to [eval] cannot
     be used, so evaluation of [e] is requested via a [stop] effect. *)
  stop Eval (η, e).

(* [call v1 v2] evaluates the function call [v1 v2]. *)

(* The value [v1] is expected to be either a non-recursive closure [VClo η a]
   or a recursive closure [VCloRec η rbs g]. *)

Definition call v1 v2 : free val :=
  (* The value [v1] must be a closure. *)
  match v1 with
  | VClo η a =>
      acall η a v2
  | VCloRec η rbs g =>
      (* Extend the environment [η] found in the closure with bindings
         for the recursive functions in [rbs]. *)
      let δ := eval_rec_bindings η rbs in
      let η := concat δ η in
      (* Look up the entry point [g] in [rbs], yielding an anonymous
         function [a]. *)
      a ← lookup_rec_bindings rbs g ;
      (* Then, proceed as in the case of a non-recursive closure. *)
      acall η a v2
   | _ =>
      crash "type mismatch (closure expected)"
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
      crash "type mismatch (Boolean value expected)"
  end.

Definition as_bool (m : free val) : free bool :=
  bind m val_as_bool.

(* ------------------------------------------------------------------------ *)

(* [val_as_int v] checks that the value [v] is a language-level integer
   value and returns its meta-level value. *)

Definition val_as_int (v : val) : free int :=
  match v with
  | VInt i =>
      ret i
  | _ =>
      crash "type mismatch (integer value expected)"
  end.

Definition as_int (m : free val) : free int :=
  bind m val_as_int.

(* [check_div_by_zero i] checks that the divisor [i] is nonzero. *)

Definition check_div_by_zero i : free unit :=
  if int.eq i int.zero then
    crash "division by zero" (* TODO raise an exception *)
  else
    ret ().

(* ------------------------------------------------------------------------ *)

(* [val_as_record v] checks that the value [v] is a language-level record
   value and returns its content, a list of field-value pairs, which can
   also be viewed as an environment fragment. *)

Definition val_as_record (v : val) : free env :=
  match v with
  | VRecord fvs =>
      ret fvs
  | _ =>
      crash "type mismatch (record value expected)"
  end.

Definition as_record (m : free val) : free env :=
  bind m val_as_record.

(* ------------------------------------------------------------------------ *)

(* [eq_val v1 v2] implements OCaml's structural equality operator [=]. *)

(* This operator cannot be applied to closures or to mutable data, but can be
   applied to values of base type (e.g., integers) and to composite immutable
   data structures (tuples, algebraic data, etc.). *)

Fixpoint eq_val v1 v2 : free bool :=
  match v1, v2 with
  | VInt i1, VInt i2 =>
      ret (int.eq i1 i2)
  | VTuple vs1, VTuple vs2 =>
      eq_vals vs1 vs2
  | VData c1 v1, VData c2 v2 =>
      let b := c1 =? c2 in
      b' ← eq_val v1 v2 ;
      ret (b && b')
  | _, _ =>
      crash "structural equality: invalid or unsupported arguments"
  end

with eq_vals vs1 vs2 : free bool :=
  match vs1, vs2 with
  | VNil, VNil =>
      ret true
  | VCons v1 vs1, VCons v2 vs2 =>
      b ← eq_val v1 v2 ;
      b' ← eq_vals vs1 vs2 ;
      ret (b && b')
  | VCons _ _, VNil
  | VNil, VCons _ _ =>
      crash "structural equality: tuple length mismatch"
  end.

Definition ne_val v1 v2 :=
  b ← eq_val v1 v2 ;
  ret (negb b).

(* [lt_val v1 v2] implements OCaml's structural ordering operator [<]. *)

(* This operator can be applied to values of base type (e.g., integers). *)

(* It currently cannot be applied to tuples, but this could be changed if
   desired. *)

(* It cannot be applied to algebraic data, because our model of algebraic
   data (where data constructors are strings) does not allow defining an
   order that is compatible with the reality of OCaml's semantics.
   Attempting to rely on an unspecified order on data constructors would
   still allow the user to draw invalid conclusions. In OCaml, the outcome
   of the comparison between two data constructors A and B depends on their
   type; but, in our model of values, type information is absent. *)

Definition lt_val v1 v2 : free bool :=
  match v1, v2 with
  | VInt i1, VInt i2 =>
      (* A signed integer comparison. *)
      ret (int.lt i1 i2)
  | _, _ =>
      crash "structural ordering: invalid or unsupported arguments"
  end.

(* The other three structural ordering operators. *)

(* [le] is defined as the negation of [gt]. This may surprise the user: when
   the user writes [0 <= x], the proof system produces [¬(x < 0)]. It may be
   preferable to give a direct definition of [le] that relies on [int.le].
   However, for the moment, [int.le] itself does not exist. *)

Definition gt_val v1 v2 :=
  lt_val v2 v1.

Definition le_val v1 v2 :=
  b ← gt_val v1 v2 ;
  ret (negb b).

Definition ge_val v1 v2 :=
  b ← lt_val v1 v2 ;
  ret (negb b).

(* ------------------------------------------------------------------------ *)

(* [concatenating eval η e δ] first extends the environment [η] with the
   environment fragment [δ], then evaluates the expression [e]. *)

(* The auxiliary function [concatenating] is used when the environment is
   extended with potentially "interesting" bindings, including [let], [let
   rec], and [match] constructs. This allows the user to get a chance to
   inspect the new bindings, possibly prove something about them, such as a
   function specification, and possibly abstract them away. *)

(* [concatenating] is not used when the environment is extended with
   uninteresting bindings, e.g., when a function is invoked (see [acall])
   and when the body of a loop is executed (see [loop]). *)

Definition concatenating eval η e δ : free val :=
  let η := concat δ η in
  eval η e.

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
  | EAnonFun a =>
      (* The creation of a closure captures the environment [η]. *)
      ret (VClo η a)
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
  | ERecord fes =>
      (* The record components are evaluated in parallel. *)
      fvs ← evalfs η fes ;
      fvs ← sort fvs ;
      ret (VRecord fvs)
  | ERecordUpdate e fes =>
      (* The existing record and the new record components are evaluated in
         parallel. *)
      '(fvs, fvs') ← par (as_record (eval η e)) (evalfs η fes) ;
      (* The new components override existing components by the same name. *)
      fvs ← update fvs fvs' ;
      fvs ← sort fvs ;
      ret (VRecord fvs)
  | ERecordAccess e f =>
      fvs ← as_record (eval η e) ;
      lookup fvs f
  | EBoolConj e1 e2 =>
      b1 ← as_bool (eval η e1) ;
     if (b1 : bool) then eval η e2 else ret VFalse
  | EInt i =>
      (* An integer literal is interpreted as a machine integer. *)
      (* We do not require this integer literal to lie within a certain
         range; we project it into the range of machine integers. *)
      ret (VInt (int.repr i))
  | EMaxInt =>
      ret (VInt (int.repr int.max_signed))
  | EMinInt =>
      ret (VInt (int.repr int.min_signed))
  | EIntNeg e =>
      i ← as_int (eval η e) ;
      ret (VInt (int.neg i))
  | EIntAdd e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.add i1 i2))
  | EIntSub e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.sub i1 i2))
  | EIntMul e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.mul i1 i2))
  | EIntDiv e1 e2 =>
      (* Signed division is used. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.divs i1 i2))
  | EIntMod e1 e2 =>
      (* Signed remainder is used. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.mods i1 i2))
  | EOpEq e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← eq_val v1 v2 ;
      ret (VBool b)
  | EOpNe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← ne_val v1 v2 ;
      ret (VBool b)
  | EOpLt e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← lt_val v1 v2 ;
      ret (VBool b)
  | EOpLe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← le_val v1 v2 ;
      ret (VBool b)
  | EOpGt e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← gt_val v1 v2 ;
      ret (VBool b)
  | EOpGe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← ge_val v1 v2 ;
      ret (VBool b)
  | EBoolDisj e1 e2 =>
      b1 ← as_bool (eval η e1) ;
      if (b1 : bool) then ret VTrue else eval η e2
  | EBoolNeg e =>
      b ← as_bool (eval η e) ;
      ret (VBool (negb b))
  | ELet bs e =>
      (* This is evaluated like a [match] construct with one branch. *)
      try
        (eval_bindings η bs)
      (concatenating eval η e)
      match_failure
  | ELetRec rbs e =>
      (* Extend the environment with a mapping of each function name in [rbs]
         to a suitable recursive closure; then, evaluate [e]. *)
      let δ := eval_rec_bindings η rbs in
      concatenating eval η e δ
  | ESeq e1 e2 =>
      _ ← eval η e1 ;
      eval η e2
  | EIfThen e e1 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else ok
  | EIfThenElse e e1 e2 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else eval η e2
  | EMatch e bs =>
      v ← eval η e ;
      eval_match η v bs
  | EWhile e body =>
      b ← as_bool (eval η e) ;
      if (b : bool) then
        _ ← eval η body ;
        stop Eval (η, EWhile e body)
      else
        ok
  | EFor x e1 e2 e =>
      (* The bounds are evaluated first. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      (* Then, the loop is executed. *)
      stop Loop (η, x, i1, i2, e)
  | EAssertFalse =>
      assertion_failure
  | EAssert e =>
      (* OCaml runtime assertions are erased when a module is compiled with
         the compiler flag [-noassert]; they are retained otherwise. We do not
         wish to depend on this flag, so we make a non-deterministic choice:
         either the runtime test is executed, or it is skipped. This forces
         the user to prove that the program is safe in both scenarios. *)
      let test : free val :=
        success ← as_bool (eval η e) ;
        if (success : bool) then ok else assertion_failure
      in
      choose ok test
  end

(* ------------------------------------------------------------------------ *)

(* [evals η es] evaluates the expressions [es] in the environment [η],
   producing values [vs]. The expressions are evaluated in parallel. *)

(* [evals] is used to evaluate tuples. *)

with evals η es : free vals :=
  match es with
  | ENil =>
      ret VNil
  | ECons e es =>
      '(v, vs) ← par (eval η e) (evals η es) ;
      ret (VCons v vs)
  end

(* ------------------------------------------------------------------------ *)

(* [evalfs η fes] evaluates the expressions [fes] in the environment [η],
   producing values [fvs]. The expressions are evaluated in parallel.

   Each expression in the list [fes] and each value in the list [fvs]
   is indexed with a record field. *)

(* [evalfs] is used to evaluate record construction expressions. *)

with evalfs η fes : free env :=
  match fes with
  | FENil =>
      ret EnvNil
  | FECons f e fes =>
      '(v, fvs) ← par (eval η e) (evalfs η fes) ;
      ret (EnvCons f v fvs)
  end

(* ------------------------------------------------------------------------ *)

(* [eval_bindings η bs] evaluates the bindings [bs] in the environment [η],
   producing an environment fragment. *)

(* [eval_bindings] is used to evaluate the [let/and] construct. *)

(* A binding is a pair [p = e]. The expressions in the right-hand sides of the
   bindings [bs] are evaluated in parallel. The values thus obtained are then
   matched against the patterns in the left-hand sides. The pattern matching
   process is sequential. *)

(* If we chose to encode the multiple-let-and construct [let p_i = e_i in e]
   as [let (p_i) = (e_i) in e], using a tuple and a single-let-and construct,
   then [eval_bindings] would disappear. We prefer to avoid encodings. *)

with eval_bindings η (bs : bindings) : free env :=
  match bs with
  | BiNil =>
      ret EnvNil
  | BiCons (Binding p e) bs =>
      (* Evaluate the expression [e], yielding a value [v]. In parallel,
         evaluate the bindings [bs], yielding an environment fragment [δ]. *)
      '(v, δ) ← par (eval η e) (eval_bindings η bs) ;
      (* Match the value [v] against the pattern [p], extending [δ]. *)
      extend δ p v
  end

(* ------------------------------------------------------------------------ *)

(* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)

with eval_match η v bs :=
  match bs with
  | BrNil =>
      (* A nonexhaustive [match] construct causes a hard failure. *)
      (* Because the proof system forbids hard failures, the user of
         the system will have to prove that this cannot happen, i.e.,
         every case analysis is exhaustive. *)
      match_failure()
  | BrCons (Branch p e) bs =>
      (* Match the value [v] against the pattern [p]. *)
      try
        (extend EnvNil p v)
      (* Success: commit to this branch. Evaluate its body. *)
      (concatenating eval η e)
      (* Soft failure: abandon this branch. Try the following branches. *)
      (λ tt, eval_match η v bs)
  end.

(* ------------------------------------------------------------------------ *)

(* [loop η x i1 i2 e] executes the loop [for x = i1 to i2 do e done]
   in the environment [η]. *)

Definition loop η x i1 i2 e : free val :=
  if int.lt i2 i1 then
    (* If [i2 < i1] holds, then there is nothing to do. *)
    ok
  else
    (* Otherwise, the loop body [e] must be executed with a binding of [x]
       to [i1]. The value of [e] is ignored. Then, the loop continues. *)
    let η' := EnvCons x (VInt i1) η in
    _v ← eval η' e ;
    (* Every [for] loop terminates, so we could in principle arrange to
       use a recursive call to [loop], but using a [stop] effect is much
       easier. *)
    stop Loop (η, x, int.add i1 int.one, i2, e)
.
