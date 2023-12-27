From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code.
From Equations Require Import Equations.
Local Infix "=?" := String.eqb.

(* Conventional metavariables. *)

Implicit Type g x : var.
Implicit Type c : data. (* or coercion; TODO *)
Implicit Type f : field.
Implicit Type p : pat.
Implicit Type ps : list pat.
Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type fes : list fexpr.
Implicit Type a : anonfun.
Implicit Type v : val.
Implicit Type vs : list val.
Implicit Type fvs xvs : env.
Implicit Type η δ : env.
Implicit Type rbs : list rec_binding.
Implicit Type i : int.
Implicit Type M : module.
Implicit Type π : path.
Implicit Type me : mexpr.
Implicit Type item : sitem.
Implicit Type items : list sitem.

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* Crashes. *)

(* Most kinds of crashes cannot occur in well-typed code, but some can,
   namely, pattern matching failures (caused by nonexhaustive case analyses)
   and assertion failures. *)

Definition unsupported_construct {A} : micro A :=
  crash.

Definition assertion_failure {A} : micro A :=
  crash.

Definition division_by_zero {A} : micro A :=
  crash.

Definition length_mismatch {A} (msg : string) : micro A :=
  crash.

Definition match_failure {A} (tt : unit) : micro A :=
  crash.

Definition missing_field {A} (x : var) : micro A :=
  crash.

Definition missing_variable {A} (x : var) : micro A :=
  crash.

Definition missing_variable_or_field {A} (x : var) : micro A :=
  crash.

Definition physical_equality_error {A} (msg : string) : micro A :=
  crash.

Definition structural_equality_error {A} (msg : string) : micro A :=
  crash.

Definition structural_ordering_error {A} (msg : string) : micro A :=
  crash.

Definition type_mismatch {A} (msg : string) : micro A :=
  crash.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

(* [ok] is an inert computation. It produces the value [VUnit]. *)

Notation ok :=
  (ret (VData "()" $ VTuple [])).

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [val_as_bool v] checks that the value [v] is a language-level Boolean
   value and returns its meta-level Boolean value. *)

Definition val_as_bool (v : val) : micro bool :=
  match v with
  | VFalse =>
      ret false
  | VTrue =>
      ret true
  | _ =>
      type_mismatch "Boolean value expected"
  end.

Definition as_bool (m : micro val) : micro bool :=
  bind m val_as_bool.

(* ------------------------------------------------------------------------ *)

(* [val_as_loc v] checks that the value [v] is a language-level location
   value and returns its meta-level value. *)

Definition val_as_loc (v: val) : micro loc :=
  match v with
  | VLoc l =>
      ret l
  | _ =>
      type_mismatch "location value expected"
  end.

Definition as_loc (m : micro val) : micro loc :=
  bind m val_as_loc.

(* ------------------------------------------------------------------------ *)

(* [val_as_int v] checks that the value [v] is a language-level integer
   value and returns its meta-level value. *)

Definition val_as_int (v : val) : micro int :=
  match v with
  | VInt i =>
      ret i
  | _ =>
      type_mismatch "integer value expected"
  end.

Definition as_int (m : micro val) : micro int :=
  bind m val_as_int.

(* [check_div_by_zero i] checks that the divisor [i] is nonzero. *)

Definition check_div_by_zero i : micro unit :=
  if int.eq i int.zero then
    division_by_zero (* TODO raise an exception *)
  else
    ret ().

(* ------------------------------------------------------------------------ *)

(* [val_as_record v] checks that the value [v] is a language-level record
   value and returns its content, a list of field-value pairs, which can
   also be viewed as an environment fragment. *)

Definition val_as_record (v : val) : micro env :=
  match v with
  | VRecord fvs =>
      ret fvs
  | _ =>
      type_mismatch "record value expected"
  end.

Definition as_record (m : micro val) : micro env :=
  bind m val_as_record.

(* ------------------------------------------------------------------------ *)

(* [val_as_struct v] checks that the value [v] is a value of the form [VStruct
   xvs] and returns its content [xvs]. *)

Definition val_as_struct (v : val) : micro env :=
  match v with
  | VStruct xvs =>
      ret xvs
  | _ =>
      type_mismatch "structure expected"
  end.

Definition as_struct (m : micro val) : micro env :=
  bind m val_as_struct.

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [lookup_name η x] looks up the name [x] in the environment [env],
   producing a value. A hard failure occurs if [x] is unbound. *)

(* This function is used also to look up fields in records and module
   components in modules. *)

Fixpoint lookup_name η x : micro val :=
  match η with
  | (x', v) :: η =>
      if x =? x' then ret v else lookup_name η x
  | [] =>
      missing_variable_or_field x
  end.

(* ------------------------------------------------------------------------ *)

(* [lookup_path η π] looks up the path [π] in the environment [η]. *)

Fixpoint lookup_path η π : micro val :=
  match π with
  | PathBase x =>
      lookup_name η x
  | PathDot π x =>
      (* The content of a structure is an environment, *)
      xvs ← as_struct (lookup_path η π) ;
      (* so we can look up [x] in the environment [xvs]. *)
      lookup_name xvs x
  end.

(* ------------------------------------------------------------------------ *)

(* [remove f fvs] removes field [f] from the field-value list [fvs]. *)

Fixpoint remove f fvs : micro env :=
  match fvs with
  | (f', v) :: fvs =>
      if f =? f' then
        ret fvs
      else
        fvs ← remove f fvs ;
        ret ((f', v) :: fvs)
  | [] =>
      missing_field f
  end.

(* ------------------------------------------------------------------------ *)

(* [update fvs fvs'] updates the existing record fields [fvs] with the new
   record fields [fvs']. *)

Fixpoint update fvs fvs' : micro env :=
  match fvs' with
  | [] =>
      ret fvs
  | (f, v') :: fvs' =>
      fvs ← remove f fvs ;
      let fvs := (f, v') :: fvs in
      update fvs fvs'
  end.

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

Module StringSort := Sort StringOrder.

Definition domain (η : env) : list string := fst (split η).

Fixpoint build (η : env) (xs : list string) : micro env :=
  match xs with
  | [] =>
      ret []
  | x :: xs =>
      v ← lookup_name η x ;
      xs ← build η xs ;
      ret ((x, v) :: xs)
  end.

Definition sort (η : env) : micro env :=
  build η (StringSort.sort (domain η)).

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [eval_rec_bindings_aux η rbs rbs'] transforms the bindings [rbs'] into an
   environment fragment. Each name [g] is mapped to a recursive closure that
   captures the environment [η] and the bindings [rbs]. *)

(* The parameters [η] and [rbs] are invariant. At the beginning, [rbs']
   is [rbs], so, in general, [rbs'] is a suffix of [rbs]. *)

Fixpoint eval_rec_bindings_aux η rbs rbs' : env :=
  match rbs' with
  | [] =>
      []
  | (RecBinding g _a) :: rbs' =>
      (g, (VCloRec η rbs g)) :: (eval_rec_bindings_aux η rbs rbs')
  end.

(* [eval_rec_bindings η rbs] transforms the bindings [rbs] into an environment
   fragment. Each name [g] is mapped to a recursive closure that captures the
   environment [η] and the bindings [rbs]. *)

Definition eval_rec_bindings η rbs : env :=
  eval_rec_bindings_aux η rbs rbs.

(* ------------------------------------------------------------------------ *)

(* [lookup_rec_bindings rbs g] looks up the function [g] in the recursive
   bindings [rbs]. The right-hand side is an anonymous function [a]. *)

Fixpoint lookup_rec_bindings rbs g : micro anonfun :=
  match rbs with
  | (RecBinding g' a) :: rbs =>
      if g =? g' then ret a else lookup_rec_bindings rbs g
  | [] =>
      missing_variable g
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

Fixpoint extend δ p v : micro env :=
  match p, v with
  | PUnsupported, _ =>
      unsupported_construct
  | PAny, _ =>
      (* A wildcard pattern always succeeds. *)
      ret δ
  | PVar x, _ =>
      (* A variable pattern always succeeds, and causes the environment
         to be extended. *)
      ret ((x, v) :: δ)
  | PAlias p x, _ =>
      (* An alias pattern [p as x] is an intersection pattern: the value
         [v] must match both the pattern [p] and the pattern [x]. *)
      δ ← extend δ p v ;
      ret ((x, v) :: δ)
  | POr p1 p2, _ =>
      (* A disjunction pattern [p1 | p2] requires that the value [v]
         match either [p1] or [p2]. *)
      orelse (extend δ p1 v) (extend δ p2 v)
  | PTuple ps, VTuple vs =>
      (* A tuple pattern matches a tuple value. *)

      (* [extends δ ps vs] matches the values [vs] against the patterns [ps].
         In case of success, the result is an extension of the environment
         fragment [δ] with bindings for the bound variables of the patterns [ps].

         A hard failure occurs when [length ps ≠ length vs]. *)

      (* Pattern matching is sequential and obeys a left-to-right strategy. This
         is important in the presence of GADTs, as the success of a test in the
         left-hand side of a pair can guarantee the safety of a test in the
         right-hand side of this pair. *)
      ((fix extends (δ : env) ps vs : micro env :=
        match ps, vs with
        | [], [] =>
            ret δ
        | p::ps, v::vs =>
            δ ← extend δ p v ;
            δ ← extends δ ps vs ;
            ret δ
        | _::_, [] =>
            length_mismatch "longer tuple expected"
        | [], _::_ =>
            length_mismatch "shorter tuple expected"
        end) δ ps vs)
  | PData c p, VData c' v =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a soft failure takes
         place. *)
      if c =? c' then extend δ p v else next
  | PRecord fps, VRecord fvs =>
      (* A record pattern matches a record value. *)
      (* The pattern may have fewer fields than the value. *)

      (* [extendfs δ fps fvs] matches the field-indexed values [fvs] against the
         field-indexed patterns [fps].

         In case of success, the result is an extension of the environment
         fragment [δ] with bindings for the bound variables of
         the patterns [fps].

         A hard failure occurs if a field is present in [fps]
         but absent in [fvs]. *)
      ((fix extendfs (δ : env) fps fvs : micro env :=
          match fps with
          | [] =>
              ret δ
          | (f, p)::fps =>
              v ← lookup_name fvs f ;
              δ ← extend δ p v ;
              δ ← extendfs δ fps fvs ;
              ret δ
        end) δ fps fvs)
  | PInt z, VInt i' =>
      let i := int.repr z in
      if int.eq i i' then ret δ else next
  | PChar c', VChar c =>
      if Ascii.eqb c c' then ret δ else next
  | PString s', VString s =>
      if s =? s' then ret δ else next
  | PTuple _, _ =>
      type_mismatch "tuple expected"
  | PData _ _, _ =>
      type_mismatch "algebraic data expected"
  | PRecord _, _ =>
      type_mismatch "record expected"
  | PInt _, _ =>
      type_mismatch "integer expected"
  | PChar _, _ =>
      type_mismatch "char expected"
  | PString _, _ =>
      type_mismatch "string expected"
end.

(* ------------------------------------------------------------------------ *)

(* [acall η a v] evaluates the application of the anonymous function [a]
   to the value [v] in the environment [η]. *)

Definition acall η a v : micro val :=
  (* An anonymous function [a] is of the form [fun x -> e]. *)
  let '(AnonFun x e) := a in
  (* Extend the environment [η] with a binding of the variable [x]
     to the value [v]. *)
  let η := (x, v) :: η in
  (* Then, evaluate the function body [e]. A recursive call to [eval] cannot
     be used, so evaluation of [e] is requested via a [stop] effect. *)
  stop CEval (η, e).

(* [call v1 v2] evaluates the function call [v1 v2]. *)

(* The value [v1] is expected to be either a non-recursive closure [VClo η a]
   or a recursive closure [VCloRec η rbs g]. *)

Definition call v1 v2 : micro val :=
  (* The value [v1] must be a closure. *)
  match v1 with
  | VClo η a =>
      acall η a v2
  | VCloRec η rbs g =>
      (* Extend the environment [η] found in the closure with bindings
         for the recursive functions in [rbs]. *)
      let δ := eval_rec_bindings η rbs in
      let η := δ ++ η in
      (* Look up the entry point [g] in [rbs], yielding an anonymous
         function [a]. *)
      a ← lookup_rec_bindings rbs g ;
      (* Then, proceed as in the case of a non-recursive closure. *)
      acall η a v2
   | _ =>
      type_mismatch "closure expected"
   end.

(* ------------------------------------------------------------------------ *)

(* [phys_eq_val v1 v2] implements OCaml's physical equality operator [==]. *)

(* This operator can be applied to memory locations. *)

Definition phys_eq_val v1 v2 : micro bool :=
  match v1, v2 with
  | VLoc l1, VLoc l2 =>
      ret (locations.eqb l1 l2)
  | _, _ =>
      physical_equality_error "invalid or unsupported arguments"
  end.

(* ------------------------------------------------------------------------ *)

(* [eq_val v1 v2] implements OCaml's structural equality operator [=]. *)

(* This operator cannot be applied to closures or to mutable data, but can be
   applied to values of base type (e.g., integers) and to composite immutable
   data structures (tuples, algebraic data, etc.). *)

Fixpoint eq_val v1 v2 : micro bool :=
  match v1, v2 with
  | VInt i1, VInt i2 =>
      ret (int.eq i1 i2)
  | VChar c1, VChar c2 =>
      ret (Ascii.eqb c1 c2)
  | VString s1, VString s2 =>
      ret (s1 =? s2)
  | VTuple vs1, VTuple vs2 =>
      ((fix eq_vals vs1 vs2 :=
        match vs1, vs2 with
        | [], [] =>
            ret true
        | v1 :: vs1, v2 :: vs2 =>
            b ← eq_val v1 v2 ;
            b' ← eq_vals vs1 vs2 ;
            ret (b && b')
        |  _ :: _, []
        | [], _ :: _ =>
            structural_equality_error "tuple length mismatch"
        end) vs1 vs2)
  | VData c1 v1, VData c2 v2 =>
      let b := c1 =? c2 in
      b' ← eq_val v1 v2 ;
      ret (b && b')
  | _, _ =>
      structural_equality_error "invalid or unsupported arguments"
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

Definition lt_val v1 v2 : micro bool :=
  match v1, v2 with
  | VInt i1, VInt i2 =>
      (* A signed integer comparison. *)
      ret (int.lt i1 i2)
  | _, _ =>
      structural_ordering_error "invalid or unsupported arguments"
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

(* [ret_concat δ η] is [ret (concat δ η)]. *)

(* The auxiliary function [ret_concat] is used when the environment is
   extended with potentially "interesting" bindings, including [let],
   [let rec], and [match] constructs. It is later made opaque. This
   allows the user to get a chance to inspect the new bindings, possibly
   prove something about them, such as a function specification, and
   possibly abstract them away. *)

(* [ret_concat] is not used when the environment is extended with
   uninteresting bindings, e.g., when a function is invoked (see
   [acall]) and when the body of a loop is executed (see [loop]). *)

Definition ret_concat δ η : micro env :=
  ret (δ ++ η).

(* ------------------------------------------------------------------------ *)

(* The evaluation of a list of structure items involves two environments [η]
   and [δ]. The environment [η] contains the bindings that are currently in
   scope: it is used when a name must be looked up. The environment [δ]
   accumulates the bindings that form the current (incomplete) structure
   that is being built. *)

Definition envs : Type :=
  (* η: *) env *
  (* δ: *) env.

Implicit Type ηδ : envs.

(* [dconcat δ' ηδ] prepends the environment fragment [δ'] in front of both
   components of the double environment [ηδ]. This reflects the common case
   where a new binding is both in scope in the following bindings and added
   to the current structure. *)

Definition dconcat δ' ηδ : envs :=
  let '(η, δ) := ηδ in
  (δ' ++ η, δ' ++ δ).

(* TODO comment *)

Definition ret_dconcat δ' ηδ :=
  ret (dconcat δ' ηδ).

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [coerce c v] applies the module coercion [c] to the module value [v]. *)

Fixpoint coerce (c : coercion) (v : val) : micro val :=
  match c with
  | CIdentity =>
      ret v
  | CStruct xcs =>
      (* [v] must be a structure, whose components form a list [xvs]. *)
      xvs ← val_as_struct v ;
      (* From [xvs], fetch the components named in the list [xcs], and
         apply the corresponding coercions to them. *)
      bind ((fix coerces (xcs : list fcoercion ) xvs : micro env :=
             match xcs with
             | [] =>
                 ret []
             | (x, c) :: xcs =>
                 (* Fetch the component [x] from [xvs]. *)
                 v ← lookup_name xvs x ;
                 (* Apply the coercion [c] to it. *)
                 v ← coerce c v ;
                 (* Fetch the rest. *)
                 xvs ← coerces xcs xvs ;
                 (* Combine the results. Whether we place [x] in front of [xvs] or
                    behind [xvs] should not make any difference, because the field
                    names that appear in the coercion should be pairwise distinct,
                    so the order in which these fields appear in the new structure
                    should be irrelevant. *)
                 ret ((x, v) :: xvs)
             end) xcs xvs)
      (λ xvs : env, ret (VStruct xvs))
  end.

(* ------------------------------------------------------------------------ *)
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

Open Scope nat.
Fixpoint length_expr (e : expr) : nat :=
  match e with
  | EUnsupported => 1
  | EPath _ => 1
  | EAnonFun afun =>
      match afun with
      | AnonFun _ e => 1 + length_expr e end
  | EApp e1 e2 => 1 + length_expr e1 + length_expr e2
  | ETuple es => fold_left (fun acc e => (length_expr e) + acc) es 1
  | EData _ e => 1 + length_expr e
  | ERecord fexprs =>
      fold_left (fun acc fe =>
                   match fe with
                   | Fexpr _ e =>
                       (length_expr e) + acc
                   end) fexprs 1
  | ERecordUpdate e fexprs =>
      fold_left (fun acc fe =>
                   match fe with
                   | Fexpr _ e =>
                       (length_expr e) + acc
                   end) fexprs (1 + length_expr e)
  | ERecordAccess e _ => 1 + length_expr e
  | EBoolConj e1 e2 => 1 + length_expr e1 + length_expr e2
  | EBoolDisj e1 e2 => 1 + length_expr e1 + length_expr e2
  | EBoolNeg e => 1 + length_expr e
  | EInt _ => 1
  | EMaxInt => 1
  | EMinInt => 1
  | EIntNeg e => 1 + length_expr e
  | EIntAdd e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIntSub e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIntMul e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIntDiv e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIntMod e1 e2 => 1 + length_expr e1 + length_expr e2
  | EChar _ => 1
  | EString _ => 1
  | EOpPhysEq e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpEq e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpNe e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpLt e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpLe e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpGt e1 e2 => 1 + length_expr e1 + length_expr e2
  | EOpGe e1 e2 => 1 + length_expr e1 + length_expr e2
  | ELet bs e =>
      fold_left (fun acc b =>
                   match b with
                   | Binding _ e =>
                       acc + length_expr e
                   end) bs (1 + length_expr e)
  | ELetRec rbs e =>
      fold_left (fun acc rb =>
                   match rb with
                   | RecBinding _ afun =>
                       match afun with
                       | AnonFun _ e =>
                           acc + length_expr e
                       end
                   end) rbs (1 + length_expr e)
  | ELetModule _ _ e => 1 + length_expr e
  | ELetOpen _ e => 1 + length_expr e
  | ESeq e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIfThen e1 e2 => 1 + length_expr e1 + length_expr e2
  | EIfThenElse e1 e2 e3 => 1 + length_expr e1 + length_expr e2 + length_expr e3
  | EMatch e bs =>
      fold_left (fun acc b =>
                   match b with
                   | Branch _ e =>
                       acc + length_expr e
                   end) bs (1 + length_expr e)
  | EWhile e1 e2 => 1 + length_expr e1 + length_expr e2
  | EFor _ e1 e2 e3 => 1 + length_expr e1 + length_expr e2 + length_expr e3
  | EAssertFalse => 1
  | EAssert e => 1 + length_expr e
  | ERef e => 1 + length_expr e
  | ELoad e => 1 + length_expr e
  | EStore e1 e2 => 1 + length_expr e1 + length_expr e2
  end.

Definition lt_expr e1 e2 :=
  length_expr e1 < length_expr e2.

Lemma wf_length_expr :
  well_founded lt_expr.
Proof.
  unfold lt_expr.
  apply Inverse_Image.wf_inverse_image.
  exact Nat.lt_wf_0.
Qed.

Definition eval_bindings eval η bs :=
  let f :=
    fun b acc =>
      match b with
      | Binding p e =>
          '(v, δ) ← par (eval η e) acc ;
          extend δ p v
      end
  in
  fold_right f (ret []) bs.


Fixpoint length_mexpr me : nat :=
  match me with
  | MUnsupported => 1
  | MPath _ => 1
  | MCoercion me _ => 1 + length_mexpr me
  | MStruct items =>
      let f :=
        fun acc item =>
          acc +
          match item with
          | ILet bs => 0
          | ILetRec rbs => 0
          | IModule _ me => length_mexpr me
          | IOpen me => length_mexpr me
          | IInclude me => length_mexpr me
          end
      in
      fold_left f items 1
  end.

Definition lt_mexpr me1 me2 :=
  length_mexpr me1 < length_mexpr me2.

Lemma wf_length_mexpr :
  well_founded lt_mexpr.
Proof.
  unfold lt_mexpr.
  apply Inverse_Image.wf_inverse_image.
  apply Nat.lt_wf_0.
Qed.

Program Fixpoint eval_mexpr eval η me : micro val :=
  (* [eval_mexpr η me] evaluates the module expression [me] in environment [η],
     yielding a value. *)
  (match me as r return me = r -> micro val with
  | MUnsupported => fun _ => unsupported_construct
  | MPath π => fun _ =>
      (* A path is looked up in the environment [η]. *)
      lookup_path η π
  | MCoercion me c => fun _ =>
      'v ← eval_mexpr eval η me ;
       coerce c v
  | MStruct items => fun Heq =>
      (* evaluate the structure items, yielding an environment [δ], *)
      bind
        (let eval_sitem :=
           fun (acc : micro envs) item =>
             match acc with
             | ret ηδ =>
                 let '(η, δ) := ηδ in
                 match item as r' return item = r' -> micro envs with
                 | ILet bs => fun Heq =>
                     δ' ← eval_bindings eval η bs;
                     ret_dconcat δ' (η, δ)
                 | ILetRec rbs => fun Heq =>
                     let δ' := eval_rec_bindings η rbs in
                     ret_dconcat δ' (η, δ)
                 | IModule m me' => fun Heq =>
                     v ← eval_mexpr eval η me' ;
                     ret_dconcat [(m, v)] (η, δ)
                 | IOpen me' => fun Heq =>
                     δ' ← as_struct (eval_mexpr eval η me') ;
                     ret (δ' ++ η, δ)
                 | IInclude me' => fun Heq =>
                     δ' ← as_struct (eval_mexpr eval η me') ;
                     ret (dconcat δ' (η, δ))
                 end eq_refl
             | _ => acc
             end
         in
         fold_left eval_sitem items (ret (η, [])))
        (fun '(_, δ) => ret (VStruct δ))
   end) eq_refl.

Next Obligation.
  admit.
Admitted.

Next Obligation.
  admit.
Admitted.

Next Obligation.
admit.
Admitted.



with eval_sitems eval ηδ items : micro envs :=
  match items with
  | [] => ret ηδ
  | item :: items =>
      let '(η, δ) := ηδ in
      bind
        ((fix eval_sitem η δ item :=
            match item with
            | ILet bs =>
                δ' ← eval_bindings eval η bs;
                ret_dconcat δ' (η, δ)
            | ILetRec rbs =>
                let δ' := eval_rec_bindings η rbs in
                ret_dconcat δ' (η, δ)
            | IModule m me =>
                'v ← eval_mexpr eval η me ;
                ret_dconcat [(m, v)] (η, δ)
            | IOpen me =>
                δ' ← as_struct (eval_mexpr eval η me) ;
                ret (δ' ++ η, δ)
            | IInclude me =>
                δ' ← as_struct (eval_mexpr eval η me) ;
                ret (dconcat δ' (η, δ))
            end) η δ item)
        (fun ηδ => eval_sitems eval ηδ items)
  end
.

with eval_sitem eval (η δ : env) item : micro envs :=
  match item with
  | ILet bs =>
      δ' ← eval_bindings eval η bs;
      ret_dconcat δ' (η, δ)
  | ILetRec rbs =>
      let δ' := eval_rec_bindings η rbs in
      ret_dconcat δ' (η, δ)
  | IModule m me =>
      'v ← eval_mexpr eval η me ;
       ret_dconcat [(m, v)] (η, δ)
  | IOpen me =>
      (* The bindings contained in the structure denoted by the module
         expression [me] are used to extend [η] but not [δ]. This reflects
         the fact that these bindings become visible, but do not extend the
         current structure. *)
      'δ' ← as_struct (eval_mexpr eval η me) ;
       ret (δ' ++ η, δ)
  | IInclude me =>
      δ' ← as_struct (eval_mexpr eval η me) ;
      (* The bindings contained in the structure denoted by the module
         expression [me] are used to extend both [η] and [δ]. *)
      ret (dconcat δ' (η, δ))
  end
.

Program Fixpoint eval η e {measure (length_expr e)} : micro val :=
  match e with
  | EUnsupported => unsupported_construct
  | EChar c => ret (VChar c)
  | EPath π =>
      (* A path [π] is looked up in the environment [η]. *)
      lookup_path η π
  | EApp e1 e2 =>
      (* The expressions [e1] and [e2] are evaluated in parallel. *)
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
       call v1 v2
  | ETuple es =>
      (* The tuple components are evaluated in parallel. *)

      (* [evals η es] evaluates the expressions [es] in the environment [η],
         producing values [vs]. The expressions are evaluated in parallel. *)
      'vs ← evals η es ;
       ret (VTuple vs)
  | ERecord fes =>
      (* The record components are evaluated in parallel. *)

      (* [evalfs η fes] evaluates the expressions [fes] in the environment [η],
         producing values [fvs]. The expressions are evaluated in parallel. *)

      (* Each expression in the list [fes] and each value in the list [fvs]
         is indexed with a record field. *)
      'fvs ← evalfs η fes ;
      'fvs ← sort fvs ;
       ret (VRecord fvs)
  | ELet bs e =>
      (* This is evaluated like a [match] construct with one branch. *)
      try
        (eval_bindings η bs)
        (λ δ, η ← ret_concat δ η; eval η e)
        match_failure
  | EMatch e bs =>
      'v ← eval η e ;
       eval_match η v bs
  | ELetModule M me e =>
      'v ← eval_mexpr η me ;
      'η ← ret_concat [(M, v)] η;
       eval η e
  | _ => unsupported_construct
end

with evals η es :=
       let f :=
         fun e acc =>
           '(v, vs) ← par (eval η e) acc ;
            ret (v :: vs)
       in
       fold_right f (ret []) es
       (* match es with *)
       (* | [] => *)
       (*     ret [] *)
       (* | e :: es => *)
       (*     '(v, vs) ← par (eval η e) (evals η es) ; *)
       (*      ret (v :: vs) *)
       (* end *)

with evalfs η fes :=
       let f :=
         fun fe acc =>
           match fe with
           | Fexpr f e =>
               '(v, fvs) ← par (eval η e) (evalfs η fes) ;
               ret ((f, v) :: fvs)
           end
       in
       fold_right f (ret []) fes
       (* match fes with *)
       (* | [] => *)
       (*     ret [] *)
       (* | (Fexpr f e) :: fes => *)
       (*     '(v, fvs) ← par (eval η e) (evalfs η fes) ; *)
       (*      ret ((f, v) :: fvs) *)
       (* end *)

with eval_bindings eval η bs :=
  let f :=
    fun b acc =>
      match b with
      | Binding p e =>
          '(v, δ) ← par (eval η e) acc ;
          extend δ p v
      end
  in
  fold_right f (ret []) bs
  (*   match bs with *)
  (*   | [] => *)
  (*       ret [] *)
  (*   | (Binding p e) :: bs => *)
  (*       (* Evaluate the expression [e], yielding a value [v]. In parallel, *)
  (*          evaluate the bindings [bs], yielding an environment fragment [δ]. *) *)
  (*       '(v, δ) ← par (eval η e) (eval_bindings η bs) ; *)
  (*        (* Match the value [v] against the pattern [p], extending [δ]. *) *)
  (*        extend δ p v *)
  (* end *)

with eval_match η v (bs : list branch) {struct bs} : micro val :=
  (* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)
  match bs with
  | [] =>
      (* A nonexhaustive [match] construct causes a hard failure. *)
      (* Because the proof system forbids hard failures, the user of
         the system will have to prove that this cannot happen, i.e.,
         every case analysis is exhaustive. *)
      match_failure()
  | (Branch p e) :: bs =>
      (* Match the value [v] against the pattern [p]. *)
      try
        (extend [] p v)
        (* Success: commit to this branch. Evaluate its body. *)
        (λ δ, η ← ret_concat δ η; eval η e)
        (* Soft failure: abandon this branch. Try the following branches. *)
        (λ tt, eval_match η v bs)
  end

with eval_mexpr η me {struct me} : micro val :=
  (* [eval_mexpr η me] evaluates the module expression [me] in environment [η],
     yielding a value. *)
  match me with
  | MUnsupported => unsupported_construct
  | MPath π =>
      (* A path is looked up in the environment [η]. *)
      lookup_path η π
  | MStruct items =>
      (* Beginning with an empty current structure, *)
      let δ := [] in
      (* evaluate the structure items, yielding an environment [δ], *)
      '(_, δ) ← eval_sitems (η, δ) items ;
       (* and wrap it in a [VStruct] value. *)
       ret (VStruct δ)
  | MCoercion me c =>
      'v ← eval_mexpr η me ;
       coerce c v
  end

with eval_sitems ηδ items : micro envs :=
  match items with
  | [] => ret ηδ
  | item :: items =>
      let '(η, δ) := ηδ in
      ηδ ← eval_sitem η δ item ;
      (* Evaluate the remaining items. *)
      eval_sitems ηδ items
  end

with eval_sitem (η δ : env) item : micro envs :=
  match item with
  | ILet bs =>
      δ' ← eval_bindings η bs;
      ret_dconcat δ' (η, δ)
  | ILetRec rbs =>
      let δ' := eval_rec_bindings η rbs in
      ret_dconcat δ' (η, δ)
  | IModule m me =>
      'v ← eval_mexpr η me ;
       ret_dconcat [(m, v)] (η, δ)
  | IOpen me =>
      (* The bindings contained in the structure denoted by the module
         expression [me] are used to extend [η] but not [δ]. This reflects
         the fact that these bindings become visible, but do not extend the
         current structure. *)
      'δ' ← as_struct (eval_mexpr η me) ;
       ret (δ' ++ η, δ)
  | IInclude me =>
      δ' ← as_struct (eval_mexpr η me) ;
      (* The bindings contained in the structure denoted by the module
         expression [me] are used to extend both [η] and [δ]. *)
      ret (dconcat δ' (η, δ))
  end
.

Equations eval η e : micro val by wf e lt_expr :=
  eval η EUnsupported := unsupported_construct ;
  eval η (EChar c) := ret (VChar c) ;
  eval η (EPath π) :=
    (* A path [π] is looked up in the environment [η]. *)
    lookup_path η π ;
  eval η (EAnonFun a) :=
    (* The creation of a closure captures the environment [η]. *)
    (* This environment is *not* trimmed so as to keep only the variables
       that occur free in [a]. Indeed, in OCaml, due to [open], [include]
       and other constructs, it is not easy to statically compute the set
       of free variables of an expression. *)
    ret (VClo η a) ;
  eval η (EApp e1 e2) :=
    (* The expressions [e1] and [e2] are evaluated in parallel. *)
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    call v1 v2 ;
  eval η (ETuple es) :=
    (* The tuple components are evaluated in parallel. *)

    (* [evals η es] evaluates the expressions [es] in the environment [η],
       producing values [vs]. The expressions are evaluated in parallel. *)
    bind ((fix evals (η : env) es :=
             match es with
             | [] =>
                 ret []
             | e :: es =>
                 '(v, vs) ← par (eval η e) (evals η es) ;
               ret (v :: vs)
             end) η es)
      (λ vs : list val, ret (VTuple vs)) ;
  eval η (EData c e) :=
    v ← eval η e ;
    ret (VData c v) ;
  eval η (ERecord fes) :=
    (* The record components are evaluated in parallel. *)

    (* [evalfs η fes] evaluates the expressions [fes] in the environment [η],
       producing values [fvs]. The expressions are evaluated in parallel. *)

    (* Each expression in the list [fes] and each value in the list [fvs]
       is indexed with a record field. *)
    bind ((fix evalfs (η : env) fes : micro env :=
             match fes with
             | [] =>
                 ret []
             | (Fexpr f e) :: fes =>
                 '(v, fvs) ← par (eval η e) (evalfs η fes) ;
               ret ((f, v) :: fvs)
             end) η fes)
      (λ fvs : env, fvs ← sort fvs ;
       ret (VRecord fvs)) ;
  eval η (ERecordUpdate e fes) :=
    (* The existing record and the new record components are evaluated in
       parallel. *)
    '(fvs, fvs') ← par
      (as_record (eval η e))
      ((fix evalfs (η : env) fes : micro env :=
          match fes with
          | [] =>
              ret []
          | (Fexpr f e) :: fes =>
              '(v, fvs) ← par (eval η e) (evalfs η fes) ;
            ret ((f, v) :: fvs)
          end) η fes) ;
      (* The new components override existing components by the same name. *)
      fvs ← update fvs fvs' ;
      fvs ← sort fvs ;
      ret (VRecord fvs) ;
  eval η (ERecordAccess e f) :=
    fvs ← as_record (eval η e) ;
    lookup_name fvs f ;
  eval η (EBoolConj e1 e2) :=
    b1 ← as_bool (eval η e1) ;
    if (b1 : bool) then eval η e2 else ret VFalse ;
  eval η (EString s) :=
    ret (VString s) ;
  eval η (EInt i) :=
    (* An integer literal is interpreted as a machine integer. *)
    (* We do not require this integer literal to lie within a certain
       range; we project it into the range of machine integers. *)
    ret (VInt (int.repr i)) ;
  eval η EMaxInt :=
    ret (VInt (int.repr int.max_signed)) ;
  eval η EMinInt :=
    ret (VInt (int.repr int.min_signed)) ;
  eval η (EIntNeg e) :=
    i ← as_int (eval η e) ;
    ret (VInt (int.neg i)) ;
  eval η (EIntAdd e1 e2) :=
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    ret (VInt (int.add i1 i2)) ;
  eval η (EIntSub e1 e2) :=
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    ret (VInt (int.sub i1 i2)) ;
  eval η (EIntMul e1 e2) :=
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    ret (VInt (int.mul i1 i2)) ;
  eval η (EIntDiv e1 e2) :=
    (* Signed division is used. *)
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    '() ← check_div_by_zero i2 ;
    ret (VInt (int.divs i1 i2)) ;
  eval η (EIntMod e1 e2) :=
    (* Signed remainder is used. *)
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    '() ← check_div_by_zero i2 ;
    ret (VInt (int.mods i1 i2)) ;
  eval η (EOpPhysEq e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← phys_eq_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpEq e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← eq_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpNe e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← ne_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpLt e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← lt_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpLe e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← le_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpGt e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← gt_val v1 v2 ;
    ret (VBool b) ;
  eval η (EOpGe e1 e2) :=
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    b ← ge_val v1 v2 ;
    ret (VBool b) ;
  eval η (EBoolDisj e1 e2) :=
    b1 ← as_bool (eval η e1) ;
    if (b1 : bool) then ret VTrue else eval η e2 ;
  eval η (EBoolNeg e) :=
    b ← as_bool (eval η e) ;
    ret (VBool (negb b)) ;
  eval η (ELet bs e) :=
      (* This is evaluated like a [match] construct with one branch. *)
    try
      (eval_bindings η bs)
      (λ δ, η ← ret_concat δ η; eval η e)
      match_failure ;
  eval η (ELetRec rbs e) :=
    (* Extend the environment with a mapping of each function name in [rbs]
       to a suitable recursive closure; then, evaluate [e]. *)
    let δ := eval_rec_bindings η rbs in
    η ← ret_concat δ η;
    eval η e ;
  eval η (ELetModule M me e) :=
    v ← eval_mexpr η me ;
    η ← ret_concat [(M, v)] η;
    eval η e ;
  eval η (ELetOpen me e) :=
    δ ← as_struct (eval_mexpr η me) ;
    η ← ret_concat δ η;
    eval η e ;
  eval η (ESeq e1 e2) :=
    _ ← eval η e1 ;
    eval η e2 ;
  eval η (EIfThen e e1) :=
    b ← as_bool (eval η e) ;
    if (b : bool) then eval η e1 else ok ;
  eval η (EIfThenElse e e1 e2) :=
    b ← as_bool (eval η e) ;
    if (b : bool) then eval η e1 else eval η e2 ;
  eval η (EMatch e bs) :=
    v ← eval η e ;
    eval_match η v bs ;
  eval η (EWhile e body) :=
    b ← as_bool (eval η e) ;
    if (b : bool) then
      _ ← eval η body ;
      stop CEval (η, EWhile e body)
    else
      ok ;
  eval η (EFor x e1 e2 e) :=
    (* The bounds are evaluated first. *)
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    (* Then, the loop is executed. *)
    stop CLoop (η, x, i1, i2, e) ;
  eval η EAssertFalse := assertion_failure ;
  eval η (EAssert e) =>
    (* OCaml runtime assertions are erased when a module is compiled with
       the compiler flag [-noassert]; they are retained otherwise. We do not
       wish to depend on this flag, so we make a non-deterministic choice:
       either the runtime test is executed, or it is skipped. This forces
       the user to prove that the program is safe in both scenarios. *)
    let test : micro val :=
      success ← as_bool (eval η e) ;
      if (success : bool) then ok else assertion_failure
    in
    choose ok test ;
  eval η (ERef e) :=
    v ← eval η e ;
    l ← stop CAlloc v ;
    ret (VLoc l) ;
  eval η (ELoad e) :=
    l ← as_loc (eval η e) ;
    stop CLoad l ;
  eval η (EStore e1 e2) :=
    '(l, v) ← par (as_loc (eval η e1)) (eval η e2) ;
    _ ← stop CStore (l, v) ;
    ok;
    
where eval_bindings η (bs : list binding) : micro env :=
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
  eval_bindings η [] := ret [] ;
  eval_bindings η ((Binding p e) :: bs) :=
    (* Evaluate the expression [e], yielding a value [v]. In parallel,
       evaluate the bindings [bs], yielding an environment fragment [δ]. *)
    '(v, δ) ← par (eval η e) (eval_bindings η bs) ;
    (* Match the value [v] against the pattern [p], extending [δ]. *)
    extend δ p v ;

where eval_match η v (bs : list branch) : micro val :=
  (* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)
  
  eval_match η v [] :=
    (* A nonexhaustive [match] construct causes a hard failure. *)
    (* Because the proof system forbids hard failures, the user of
       the system will have to prove that this cannot happen, i.e.,
       every case analysis is exhaustive. *)
    match_failure() ;
  eval_match η v ((Branch p e) :: bs) :=
    (* Match the value [v] against the pattern [p]. *)
    try
      (extend [] p v)
      (* Success: commit to this branch. Evaluate its body. *)
      (λ δ, η ← ret_concat δ η; eval η e)
      (* Soft failure: abandon this branch. Try the following branches. *)
      (λ tt, eval_match η v bs) ;

where eval_mexpr η me : micro val :=
  (* [eval_mexpr η me] evaluates the module expression [me] in environment [η],
     yielding a value. *)

  eval_mexpr η MUnsupported := unsupported_construct ;
  eval_mexpr η (MPath π) :=
    (* A path is looked up in the environment [η]. *)
    lookup_path η π ;
  eval_mexpr η (MStruct items) :=
    (* Beginning with an empty current structure, *)
    let δ := [] in
    (* evaluate the structure items, yielding an environment [δ], *)
    '(_, δ) ← eval_sitems (η, δ) items ;
    (* and wrap it in a [VStruct] value. *)
    ret (VStruct δ) ;
  eval_mexpr η (MCoercion me c) :=
    v ← eval_mexpr η me ;
    coerce c v ;

(* [eval_sitems ηδ items] evaluates the structure items [items] in the
   double environment [ηδ], yielding an updated double environment. *)

with eval_sitems ηδ items : micro envs :=
  eval_sitems ηδ [] := ret ηδ ;
  eval_sitems ηδ (item :: items) :=
    (* Evaluate this item. *)
    let '(η, δ) := ηδ in
    ηδ ← eval_sitem η δ item ;
    (* Evaluate the remaining items. *)
    eval_sitems ηδ items ;

(* [eval_sitem ηδ item] evaluates the structure item [item] in the
   double environment [ηδ], yielding an updated double environment. *)

where eval_sitem (η δ : env) item : micro envs :=
  eval_sitem η δ (ILet bs) :=
    δ' ← eval_bindings η bs;
    ret_dconcat δ' (η, δ) ;
  eval_sitem η δ (ILetRec rbs) :=  
    let δ' := eval_rec_bindings η rbs in
    ret_dconcat δ' (η, δ) ;
  eval_sitem η δ (IModule m me) :=
    v ← eval_mexpr η me ;
    ret_dconcat [(m, v)] (η, δ) ;
  eval_sitem η δ (IOpen me) :=
    (* The bindings contained in the structure denoted by the module
       expression [me] are used to extend [η] but not [δ]. This reflects
       the fact that these bindings become visible, but do not extend the
       current structure. *)
    δ' ← as_struct (eval_mexpr η me) ;
    ret (δ' ++ η, δ) ;
  eval_sitem η δ (IInclude me) :=
    δ' ← as_struct (eval_mexpr η me) ;
    (* The bindings contained in the structure denoted by the module
       expression [me] are used to extend both [η] and [δ]. *)
    ret (dconcat δ' (η, δ))

.

(* ------------------------------------------------------------------------ *)

(* [loop η x i1 i2 e] executes the loop [for x = i1 to i2 do e done]
   in the environment [η]. *)

Definition loop η x i1 i2 e : micro val :=
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
    stop CLoop (η, x, int.add i1 int.one, i2, e)
.
