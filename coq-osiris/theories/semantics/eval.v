From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code.
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

(* Some errors that are exceptions in OCaml are treated as crashes here:
   assertion failure, match failure, division by zero, applications of
   structural equality to values of an unsupported type, etc. *)

Definition unsupported_construct {A E} : micro A E :=
  crash.

Definition assertion_failure {A E} : micro A E :=
  crash.

Definition division_by_zero {A E} : micro A E :=
  crash.

Definition length_mismatch {A E} (msg : string) : micro A E :=
  crash.

Definition match_failure {A E} (tt : unit) : micro A E :=
  crash.

Definition missing_field {A E} (x : var) : micro A E :=
  crash.

Definition missing_variable {A E} (x : var) : micro A E :=
  crash.

Definition missing_variable_or_field {A E} (x : var) : micro A E :=
  crash.

Definition physical_equality_error {A E} (msg : string) : micro A E :=
  crash.

Definition structural_equality_error {A E} (msg : string) : micro A E :=
  crash.

Definition structural_ordering_error {A E} (msg : string) : micro A E :=
  crash.

Definition type_mismatch {A E} (msg : string) : micro A E :=
  crash.

(* The logical operations [lsl], [lsr], and [asr] require their second
   operand [i2] to satisfy [0 <= i2 <= zintsize]. This is perhaps more
   restrictive than necessary, but this requirement appears in the OCaml
   reference manual. If this condition is not met then, according to the
   manual, the result is an unspecified integer value. In this semantics,
   we adopt a more pessimistic (more permissive) specification and allow
   the result in that case to be a crash. This removes the need for an
   effectful operation that produces an arbitrary integer result. We may
   revisit this in the future. TODO *)

Definition in_shift_range_b (i : int) : bool :=
  (0 <=? signed i) && (signed i <=? int.zintsize).

Definition out_of_shift_range {A E} : micro A E :=
  crash.

Definition if_in_shift_range {A E} (i : int) (m : micro A E) :=
  if in_shift_range_b i then m else out_of_shift_range.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

(* [ok] is an inert computation. It produces the value [VUnit]. *)

Notation ok :=
  (ret (VData "()" $ VTuple [])).

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [val_as_bool v] checks that the value [v] is a language-level Boolean
   value and returns its meta-level Boolean value. *)

Definition val_as_bool (v : val) : micro bool exn :=
  match v with
  | VFalse =>
      ret false
  | VTrue =>
      ret true
  | _ =>
      type_mismatch "Boolean value expected"
  end.

Definition as_bool (m : microvx) : micro bool exn :=
  v ← m ;
  val_as_bool v.

(* ------------------------------------------------------------------------ *)

(* [val_as_loc v] checks that the value [v] is a language-level location
   value and returns its meta-level value. *)

Definition val_as_loc {E} (v : val) : micro loc E :=
  match v with
  | VLoc l =>
      ret l
  | _ =>
      type_mismatch "location value expected"
  end.

Definition as_loc {E} (m : micro val E) : micro loc E :=
  v ← m ;
  val_as_loc v.

(* ------------------------------------------------------------------------ *)

(* [val_as_cont v] checks that the value [v] is a language-level continuation
   value and returns its meta-level value. *)

Definition val_as_cont {E} (v : val) : micro loc E :=
  match v with
  | VCont l =>
      ret l
  | _ =>
      type_mismatch "continuation value expected"
  end.

Definition as_cont {E} (m : micro val E) : micro loc E :=
  v ← m ;
  val_as_cont v.

(* ------------------------------------------------------------------------ *)

(* [val_as_int v] checks that the value [v] is a language-level integer
   value and returns its meta-level value. *)

Definition val_as_int (v : val) : micro int exn :=
  match v with
  | VInt i =>
      ret i
  | _ =>
      type_mismatch "integer value expected"
  end.

Definition as_int (m : microvx) : micro int exn :=
  v ← m ;
  val_as_int v.

(* [check_div_by_zero i] checks that the divisor [i] is nonzero. *)

Definition check_div_by_zero i : micro unit exn :=
  if int.eq i int.zero then
    division_by_zero
  else
    ret ().

(* ------------------------------------------------------------------------ *)

(* [val_as_record v] checks that the value [v] is a language-level record
   value and returns its content, a list of field-value pairs, which can
   also be viewed as an environment fragment. *)

Definition val_as_record (v : val) : micro env exn :=
  match v with
  | VRecord fvs =>
      ret fvs
  | _ =>
      type_mismatch "record value expected"
  end.

Definition as_record (m : microvx) : micro env exn :=
  v ← m ;
  val_as_record v.

(* ------------------------------------------------------------------------ *)

(* [val_as_struct v] checks that the value [v] is a value of the form [VStruct
   xvs] and returns its content [xvs]. *)

Definition val_as_struct (v : val) : micro env void :=
  match v with
  | VStruct xvs =>
      ret xvs
  | _ =>
      type_mismatch "structure expected"
  end.

Definition as_struct {E} (m : micro val E) : micro env E :=
  v ← m ;
  widen (val_as_struct v).

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* [lookup_name η x] looks up the name [x] in the environment [env],
   producing a value. A hard failure occurs if [x] is unbound. *)

(* This function is used also to look up fields in records and module
   components in modules. *)

Fixpoint lookup_name η x : micro val void :=
  match η with
  | (x', v) :: η =>
      if x =? x' then ret v else lookup_name η x
  | [] =>
      missing_variable_or_field x
  end.

(* ------------------------------------------------------------------------ *)

(* [lookup_path η π] looks up the path [π] in the environment [η]. *)

Fixpoint lookup_path η π : micro val void :=
  match π with
  | [] =>
      missing_variable "no path base"
  | [x] =>
      lookup_name η x
  | x1 :: π =>
      (* We retrieve the value bound to the name [x1] in [η]. *)
      v ← lookup_name η x1 ;
      (* We expect this value to be a structure. *)
      xvs ← val_as_struct v ;
      (* The content of a structure is an environment,
         so we can look up [π] in the environment [xvs]. *)
      lookup_path xvs π
  end.

(* ------------------------------------------------------------------------ *)

(* [remove f fvs] removes field [f] from the field-value list [fvs]. *)

Fixpoint remove f fvs : micro env exn :=
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

Fixpoint update fvs fvs' : micro env exn :=
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

Require Import Orders Sorting.

Module PairOrder <: TotalLeBool.
  Definition t := prod string val.
  Definition leb (t1 t2 : string * val) :=
    String.leb (fst t1) (fst t2).
  Definition leb_total (t1 t2 : string * val) :=
    String.leb_total (fst t1) (fst t2).
End PairOrder.

Module PairSort := Sort PairOrder.

Definition sort (η : env) : env := PairSort.sort η.

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
  | RecBinding g _a :: rbs' =>
      (g, VCloRec η rbs g) :: eval_rec_bindings_aux η rbs rbs'
  end.

(* [eval_rec_bindings η rbs] transforms the bindings [rbs] into an environment
   fragment. Each name [g] is mapped to a recursive closure that captures the
   environment [η] and the bindings [rbs]. *)

Definition eval_rec_bindings η rbs : env :=
  eval_rec_bindings_aux η rbs rbs.

(* ------------------------------------------------------------------------ *)

(* [lookup_rec_bindings rbs g] looks up the function [g] in the recursive
   bindings [rbs]. The right-hand side is an anonymous function [a]. *)

Fixpoint lookup_rec_bindings rbs g : micro anonfun exn :=
  match rbs with
  | RecBinding g' a :: rbs =>
      if g =? g' then ret a else lookup_rec_bindings rbs g
  | [] =>
      missing_variable g
  end.

(* ------------------------------------------------------------------------ *)

(* This section defines the auxiliary functions that are mutually recursive
   with [extend]. *)

Section Extend.

Variable extend : env → pat → val → micro env unit.

(* ------------------------------------------------------------------------ *)

(* [extends δ ps vs] matches the values [vs] against the patterns [ps].

   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of the patterns [ps].

   In case of failure, a (meta-level) exception is raised. This is why the
   exceptional result type of [extends] is [unit].

   A hard failure occurs when [length ps ≠ length vs]. *)

(* Pattern matching is sequential and obeys a left-to-right strategy. This
   is important in the presence of GADTs, as the success of a test in the
   left-hand side of a pair can guarantee the safety of a test in the
   right-hand side of this pair. *)

Fixpoint pre_extends (δ : env) ps vs : micro env unit :=
  let extends := pre_extends in
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
 end.

(* [extendfs δ fps fvs] matches the field-indexed values [fvs] against the
   field-indexed patterns [fps].

   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of
   the patterns [fps].

   A hard failure occurs if a field is present in [fps]
   but absent in [fvs]. *)

Fixpoint pre_extendfs (δ : env) fps fvs : micro env unit :=
  let extendfs := pre_extendfs in
  match fps with
  | [] => ret δ
  | (f, p) :: fps =>
      v ← widen (lookup_name fvs f) ;
      δ ← extend δ p v ;
      δ ← extendfs δ fps fvs ;
      ret δ
  end.

End Extend.

(* [extend_value δ p v] matches the value [v] against the pattern [p].

   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of the pattern [p].

   A (meta-level) exception is raised if [p] does not match [v], e.g., if [p]
   selects a data constructor [c] but [v] carries a distinct data constructor
   [c']. This is why the exceptional result type of [extends] is [unit].

   A hard failure takes place if [p] and [v] have incompatible types,
   e.g., if [p] is a tuple pattern and [v] is not a tuple value or
   is a tuple value of an incorrect arity. *)

(* We assume that the pattern [p] is linear: that is, no variable is
   bound twice. This property is enforced by the OCaml type-checker. *)

Fixpoint extend δ p v : micro env unit :=
  let extends := pre_extends extend in
  let extendfs := pre_extendfs extend in
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
      extends δ ps vs
  | PData c p, VData c' v =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a meta-level exception
         is raised. *)
      if c =? c' then extend δ p v else throw ()
  | PXData c p, VXData l v =>
      (* A data pattern for an extensible data type matches a data value, provided
         the data constructors correspond to the same location in the environment.
         If the data constructors do not match, a meta-level exception is raised. *)
      l' ← as_loc (widen (lookup_name δ c)) ;
      if (locations.eqb l l') then extend δ p v else throw()
  | PRecord fps, VRecord fvs =>
      (* A record pattern matches a record value. *)
      (* The pattern may have fewer fields than the value. *)
      extendfs δ fps fvs
  | PInt z, VInt i' =>
      let i := int.repr z in
      if int.eq i i' then ret δ else throw ()
  | PChar c', VChar c =>
      if Ascii.eqb c c' then ret δ else throw ()
  | PString s', VString s =>
      if s =? s' then ret δ else throw ()
  | PTuple _, _ =>
      type_mismatch "tuple expected"
  | PData _ _, _ =>
      type_mismatch "algebraic data expected"
  | PXData _ _, _ =>
      type_mismatch "extensible algebraic data expected"
  | PRecord _, _ =>
      type_mismatch "record expected"
  | PInt _, _ =>
      type_mismatch "integer expected"
  | PChar _, _ =>
      type_mismatch "char expected"
  | PString _, _ =>
      type_mismatch "string expected"
  end.

Definition extends δ ps vs :=
  pre_extends extend δ ps vs.

Definition extendfs δ fps fvs :=
  pre_extendfs extend δ fps fvs.

(* [cextend η cp o] matches the outcome [o] against
   the computation pattern [cp]. *)

Fixpoint cextend δ cp o : micro env unit :=
  match cp, o with
  | CVal p, O3Ret v =>
      (* A value pattern matches a return. *)
      extend δ p v
  | CExc p, O3Throw v =>
      (* An exception pattern matches a throw. *)
      extend δ p v
  | CEff pe pk, O3Perform e k =>
      δ ← extend δ pe e ;
      (* [pk] is a pattern for the continuation [k].
         It can only be a [PVar] or a [PAny]. *)
      extend δ pk (VCont k)
  | COr cp1 cp2, _  =>
      (* A [COr] either matches its first or second branch. *)
      orelse (cextend δ cp1 o) (cextend δ cp2 o)
  | _, _ =>
      (* If [o] and [cp] don't match, we throw a meta-level exception
         and continue to the next branch.*)
      throw()
  end.

(* TODO: Comment. *)

Fixpoint try_cextend_eff η v k bs :=
  match bs with
  | [] =>
      None
  | (Branch cp e) :: bs =>
      match cextend η cp (O3Perform v k) with
      | ret δ =>
          Some (δ, e)
      | _ =>
          try_cextend_eff η v k bs
      end
  end.

(* This variant of [extend] crashes if [p] does not match [v]. *)

Definition irrefutably_extend δ p v : micro env void :=
  try (extend δ p v) ret match_failure.

(* ------------------------------------------------------------------------ *)

(* [acall η a v] evaluates the application of the anonymous function [a]
   to the value [v] in the environment [η]. *)

Definition acall η a v : microvx :=
  (* An anonymous function [a] is of the form [fun x → e]. *)
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

Definition call v1 v2 : microvx :=
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

Definition phys_eq_val v1 v2 : micro bool exn :=
  match v1, v2 with
  | VLoc l1, VLoc l2 =>
      ret (locations.eqb l1 l2)
  | VCont k1, VCont k2 =>
      ret (locations.eqb k1 k2)
  | _, _ =>
      physical_equality_error "invalid or unsupported arguments"
  end.

(* ------------------------------------------------------------------------ *)

(* [eq_val v1 v2] implements OCaml's structural equality operator [=]. *)

(* This operator cannot be applied to closures or to mutable data, but can be
   applied to values of base type (e.g., integers) and to composite immutable
   data structures (tuples, algebraic data, etc.). *)

Fixpoint eq_val v1 v2 : micro bool exn :=

  let eq_vals :=
    fix eq_vals vs1 vs2 :=
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
      end
  in

  match v1, v2 with
  | VInt i1, VInt i2 =>
      ret (int.eq i1 i2)
  | VChar c1, VChar c2 =>
      ret (Ascii.eqb c1 c2)
  | VString s1, VString s2 =>
      ret (s1 =? s2)
  | VTuple vs1, VTuple vs2 =>
      eq_vals vs1 vs2
  | VData c1 v1, VData c2 v2 =>
      let b := c1 =? c2 in
      b' ← eq_val v1 v2 ;
      ret (b && b')
  | _, _ =>
      structural_equality_error "invalid or unsupported arguments"
end.

Definition ne_val v1 v2 : micro bool exn :=
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

Definition lt_val v1 v2 : micro bool exn :=
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

Definition gt_val v1 v2 : micro bool exn :=
  lt_val v2 v1.

Definition le_val v1 v2 : micro bool exn :=
  b ← gt_val v1 v2 ;
  ret (negb b).

Definition ge_val v1 v2 : micro bool exn :=
  b ← lt_val v1 v2 ;
  ret (negb b).

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

(* ------------------------------------------------------------------------ *)

Definition pre_coerces coerce :=
  fix coerces (xcs : list fcoercion ) (xvs : env) : micro env void :=
    match xcs with
    | [] => ret []
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
    end.

(* [coerce c v] applies the module coercion [c] to the module value [v]. *)

Fixpoint coerce (c : coercion) (v : val) : micro val void :=
  let coerces := pre_coerces coerce in
  match c with
  | CIdentity =>
      ret v
  | CStruct xcs =>
      (* [v] must be a structure, whose components form a list [xvs]. *)
      xvs ← val_as_struct v ;
      (* From [xvs], fetch the components named in the list [xcs], and
         apply the corresponding coercions to them. *)
      xvs ← coerces xcs xvs ;
      ret (VStruct xvs)
  end.

(* ------------------------------------------------------------------------ *)

(* A large group of mutually recursive functions follows. We use several
   sections to make open recursion (parameterization) more lightweight. The
   functions that need forward edges are [eval_bindings], [eval_mexpr], and
   [eval]. *)

Section EvalBindings.

Variable eval_bindings : env → list binding → micro env exn.

Section EvalMExpr.

Variable eval_mexpr : env → mexpr → microvx.

(* ------------------------------------------------------------------------ *)

(* [eval_sitem ηδ item] evaluates the structure item [item] in the
   double environment [ηδ], yielding an updated double environment. *)

Definition pre_eval_sitem (ηδ : envs) (item : sitem) :=
  let '(η, δ) := ηδ in
  match item with
  | ILet bs =>
      δ' ← eval_bindings η bs;
      ret  (δ' ++ η, δ' ++ δ)
  | ILetRec rbs =>
      let δ' := eval_rec_bindings η rbs in
      ret (δ' ++ η, δ' ++ δ)
  | IModule m me' =>
      v ← eval_mexpr η me' ;
      ret ([(m, v)] ++ η, [(m, v)] ++ δ)
  | IOpen me' =>
      δ' ← as_struct (eval_mexpr η me') ;
      ret (δ' ++ η, δ)
  | IInclude me' =>
      δ' ← as_struct (eval_mexpr η me') ;
      ret (δ' ++ η, δ' ++ δ)
  end.

(* [eval_sitems ηδ items] evaluates the structure items [items] in the
   double environment [ηδ], yielding an updated double environment. *)

Fixpoint pre_eval_sitems (ηδ : envs) (items : list sitem) : micro envs exn :=
  let eval_sitem := pre_eval_sitem in
  let eval_sitems := pre_eval_sitems in
  match items with
  | [] =>
      ret ηδ
  | item :: items =>
      (* Evaluate this item *)
      ηδ ← eval_sitem ηδ item ;
      (* Evaluate the remaining items *)
      eval_sitems ηδ items
  end.

End EvalMExpr.

(* ------------------------------------------------------------------------ *)

(* [eval_mexpr η me] evaluates the module expression [me] in environment [η],
   yielding a value. *)

Fixpoint pre_eval_mexpr (η : env) (me : mexpr) : microvx :=
  let eval_mexpr := pre_eval_mexpr in
  let eval_sitems := pre_eval_sitems eval_mexpr in
  match me with
  | MUnsupported =>
      unsupported_construct
  | MPath π =>
      (* A path is looked up in the environment [η]. *)
      widen (lookup_path η π)
  | MCoercion me c =>
      v ← eval_mexpr η me ;
      widen (coerce c v)
  | MStruct items =>
      (* evaluate the structure items, yielding an environment [δ], *)
      '(_, δ) ← eval_sitems (η, []) items ;
      (* and wrap it in a [VStruct] value. *)
      ret (VStruct δ)
  end.

End EvalBindings.

Section Eval.

Variable eval : env → expr → microvx.

(* ------------------------------------------------------------------------ *)

(* [eval_bindings η bs] evaluates the bindings [bs] in the environment [η],
   producing an environment fragment. *)

(* [eval_bindings] is used to evaluate the [let/and] construct. *)

(* A binding is a pair [p = e]. The expressions in the right-hand sides of the
   bindings [bs] are evaluated in parallel. The values thus obtained are then
   matched against the patterns in the left-hand sides. The pattern matching
   process is sequential. *)

(* Every pattern is considered irrefutable, so if a pattern [p] does not
   match the corresponding value [v], a crash occurs. *)

(* If we chose to encode the multiple-let-and construct [let p_i = e_i in e]
   as [let (p_i) = (e_i) in e], using a tuple and a single-let-and construct,
   then [eval_bindings] would disappear. We prefer to avoid encodings. *)

Fixpoint pre_eval_bindings (η : env) (bs : list binding) : micro env exn :=
  let eval_bindings := pre_eval_bindings in
  match bs with
  | [] =>
      ret []
  | Binding p e :: bs =>
      (* Evaluate the expression [e], yielding a value [v]. In parallel,
         evaluate the bindings [bs], yielding an environment fragment [δ]. *)
      '(v, δ) ← par (eval η e) (eval_bindings η bs) ;
       (* Match the value [v] against the pattern [p], extending [δ]. *)
      widen (irrefutably_extend δ p v)
  end.

(* ------------------------------------------------------------------------ *)

(* [evals η es] evaluates the expressions [es] in the environment [η],
   producing values [vs]. The expressions are evaluated in parallel. *)

(* [evals] is used to evaluate tuples. *)

Fixpoint pre_evals (η : env) (es : list expr) : micro (list val) exn :=
  let evals := pre_evals in
  match es with
  | [] =>
      ret []
  | e :: es =>
      '(v, vs) ← par (eval η e) (evals η es) ;
      ret (v :: vs)
  end.

(* ------------------------------------------------------------------------ *)

(* [evalfs η fes] evaluates the expressions [fes] in the environment [η],
   producing values [fvs]. The expressions are evaluated in parallel.

   Each expression in the list [fes] and each value in the list [fvs]
   is indexed with a record field. *)

(* [evalfs] is used to evaluate record construction expressions. *)

Fixpoint pre_evalfs (η : env) (fes : list fexpr) : micro (list (field * val)) exn :=
  let evalfs := pre_evalfs in
  match fes with
  | [] =>
      ret []
  | (Fexpr f e) :: fes =>
      '(v, fvs) ← par (eval η e) (evalfs η fes) ;
      ret ((f, v) :: fvs)
  end.

(* ------------------------------------------------------------------------ *)

(* [eval_match deep η o bs] evaluates [match o with bs] in the environment [η],
   taking into account whether [o] is a return or a throw. *)

(* The boolean flag [deep] indicates whether the [match] is a deep handler.

   Shallow handlers must discharge itself only when it is consumed by an effect,
   thus [all_branches] keep track of all the branches in order to install the
   handler if it has not been consumed. *)

Fixpoint pre_eval_match_aux (deep : bool) (η : env) (o : outcome3 val exn)
  (bs : handler) (all_branches : handler)
   : microvx :=
  let eval_match := pre_eval_match_aux in
  match bs with
  | [] =>
      (* A nonexhaustive [match] construct. *)
      (match o with
      | O3Ret _ =>
          (* When matching on a value, a nonexhaustive [match] causes
              a hard failure. *)
          (* The user of the system will have to prove that this
              cannot happen, i.e., every case analysis is exhaustive. *)
          match_failure()
      | O3Throw e =>
          (* When matching on an exception, a nonexhaustive [match]
              causes the exception to be propagated. *)
          throw e
      | O3Perform e l =>
          if deep then
            (* For a deep handler, there is no need to install the handler
               again. *)
            try2 (stop CPerform e) (fun o => stop CResume (l, o))
          else
            (* For a shallow handler, since the handler has not been consumed
               by an effect, we must install the handler. *)
            l ← install deep l η all_branches ;
            try2 (stop CPerform e) (fun o => stop CResume (l, o))
      end)
  | Branch cp e :: bs =>
      try
        (* Match the outcome [o] against the computational pattern [cp]. *)
        (cextend η cp o)
        (* Success: commit to this branch. Evaluate its body. *)
        (λ δ, eval δ e)
        (* Soft failure: abandon this branch. Try the following branches. *)
        (fun tt => eval_match deep η o bs all_branches)
  end.

Definition pre_eval_match (deep : bool)
  (η : env) (o : outcome3 val exn) (bs : list branch) : microvx :=
  if deep then
    match o with
    | O3Perform e k =>
        (* Deep handler installation: we allocate a new location where the
         handler is installed around the continuation captured by [k]. *)
        k ← install deep k η bs ;
        pre_eval_match_aux deep η (O3Perform e k) bs bs
    | _ =>
        (* There are no effects to install the handler around, so we do not
           install a handler. *)
        pre_eval_match_aux deep η o bs bs
    end
  else
    (* Shallow handlers are "consumed-once" handlers; no installations necessary
       here. *)
    pre_eval_match_aux deep η o bs bs.

Fixpoint pre_eval_trywith (η : env) (ex : exn) (bs : list branch) : microvx :=
  let eval_trywith := pre_eval_trywith in
  match bs with
  | [] =>
      throw ex
  | Branch (CExc p) e :: bs =>
      try
        (extend η p ex)
        (λ δ, eval δ e)
        (λ tt, eval_trywith η ex bs)
  | _ =>
      type_mismatch "exception pattern expected"
  end.

(* TODO: Comment. *)

Fixpoint pre_try_cextend_pure η (o : outcome2 val exn) bs :=
  let try_cextend_pure := pre_try_cextend_pure in
  match bs with
  | [] =>
      match o with
      | O2Ret _ =>
          None
      | O2Throw e =>
          Some (throw e)
      end
  | (Branch cp e) :: bs =>
      match cextend η cp o with
      | ret δ =>
          Some (eval δ e)
      | _ =>
          try_cextend_pure η o bs
      end
  end.

End Eval.

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

Fixpoint eval η e {struct e} : microvx :=
  let evals := pre_evals eval in
  let evalfs := pre_evalfs eval in
  let eval_match := pre_eval_match eval in
  let eval_trywith := pre_eval_trywith eval in
  let eval_bindings := pre_eval_bindings eval in
  let eval_mexpr := pre_eval_mexpr eval_bindings in
  match e with
  | EUnsupported =>
      unsupported_construct
  | EChar c =>
      ret (VChar c)
  | EPath π =>
      (* A path [π] is looked up in the environment [η]. *)
      widen (lookup_path η π)
  | EAnonFun a =>
      (* The creation of a closure captures the environment [η]. *)
      (* This environment is *not* trimmed so as to keep only the variables
         that occur free in [a]. Indeed, in OCaml, due to [open], [include]
         and other constructs, it is not easy to statically compute the set
         of free variables of an expression. *)
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
  | EXData c e =>
      l ← as_loc (widen (lookup_name η c)) ;
      v ← eval η e ;
      ret (VXData l v)
  | ERecord fes =>
      (* The record components are evaluated in parallel. *)
      fvs ← evalfs η fes ;
      let fvs := sort fvs in
      ret (VRecord fvs)
  | ERecordUpdate e fes =>
      (* The existing record and the new record components are evaluated in
         parallel. *)
      '(fvs, fvs') ← par (as_record (eval η e)) (evalfs η fes) ;
      (* The new components override existing components by the same name. *)
      fvs ← update fvs fvs' ;
      let fvs := sort fvs in
      ret (VRecord fvs)
  | ERecordAccess e f =>
      fvs ← as_record (eval η e) ;
      widen (lookup_name fvs f)
  | EBoolConj e1 e2 =>
      b1 ← as_bool (eval η e1) ;
      if (b1 : bool) then eval η e2 else ret VFalse
  | EString s =>
      ret (VString s)
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
  | EIntLand e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.land i1 i2))
  | EIntLor e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lor i1 i2))
  | EIntLxor e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lxor i1 i2))
  | EIntLnot e =>
      i ← as_int (eval η e) ;
      ret (VInt (int.lnot i))
  | EIntLsl e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsl i1 i2)))
  | EIntLsr e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsr i1 i2)))
  | EIntAsr e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.asr i1 i2)))
  | EFloat f =>
      ret (VFloat f)
  | EOpPhysEq e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← phys_eq_val v1 v2 ;
      ret (VBool b)
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
      δ ← eval_bindings η bs ;
      η ← ret (δ ++ η);
      eval η e
  | ELetRec rbs e =>
      (* Extend the environment with a mapping of each function name in [rbs]
         to a suitable recursive closure; then, evaluate [e]. *)
      let δ := eval_rec_bindings η rbs in
      η ← ret (δ ++ η);
      eval η e
  | ELetModule M me e =>
      v ← eval_mexpr η me ;
      let δ := [(M, v)] in
      η ← ret (δ ++ η);
      eval η e
  | ELetOpen me e =>
      δ ← as_struct (eval_mexpr η me) ;
      η ← ret (δ ++ η);
      eval η e
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
      (* TODO: Comment. *)
      Handle (eval η e)
        (λ o3, eval_match true η o3 bs)
  | ETryWith e bs =>
      (* TODO: Comment. *)
      try
        (eval η e)
        Ret
        (λ ex, eval_trywith η ex bs)
  | ERaise e =>
      exn ← eval η e ;
      throw exn
  | EPerform e =>
      eff ← eval η e ;
      perform eff
  | EContinue e1 e2 =>
      l ← as_cont (eval η e1) ;
      v ← eval η e2 ;
      stop CResume (l, O2Ret v)
  | EDiscontinue e1 e2 =>
      l ← as_cont (eval η e1) ;
      exn ← eval η e2 ;
      stop CResume (l, O2Throw exn)
  | EWhile e body =>
      b ← as_bool (eval η e) ;
      if (b : bool) then
        _ ← eval η body ;
        stop CEval (η, EWhile e body)
      else
        ok
  | EFor x e1 e2 e =>
      (* The bounds are evaluated first. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      (* Then, the loop is executed. *)
      stop CLoop (η, x, i1, i2, e)
  | EAssertFalse =>
      assertion_failure
  | EAssert e =>
      (* OCaml runtime assertions are erased when a module is compiled with
         the compiler flag [-noassert]; they are retained otherwise. We do not
         wish to depend on this flag, so we make a non-deterministic choice:
         either the runtime test is executed, or it is skipped. This forces
         the user to prove that the program is safe in both scenarios. *)
      let test : microvx :=
        success ← as_bool (eval η e) ;
        if (success : bool) then ok else assertion_failure
      in
      choose ok test
  | ERef e =>
      v ← eval η e ;
      l ← stop CAlloc v ;
      ret (VLoc l)
  | ELoad e =>
      l ← as_loc (eval η e) ;
      stop CLoad l
  | EStore e1 e2 =>
      '(l, v) ← par (as_loc (eval η e1)) (eval η e2) ;
      _ ← stop CStore (l, v) ;
      ok
  end.

Definition evals := pre_evals eval.

Definition evalfs := pre_evalfs eval.

(* Handlers are deep by default. *)
Definition eval_match := pre_eval_match eval.

Definition deep_eval_match := eval_match true.

Definition shallow_eval_match := eval_match false.

Definition eval_trywith := pre_eval_trywith eval.

Definition try_cextend_pure := pre_try_cextend_pure eval.

Definition eval_bindings := pre_eval_bindings eval.

Definition eval_mexpr := pre_eval_mexpr eval_bindings.

Definition eval_sitem :=
  pre_eval_sitem eval_bindings eval_mexpr.

Definition eval_sitems :=
  pre_eval_sitems eval_bindings eval_mexpr.

(* ------------------------------------------------------------------------ *)

(* [loop η x i1 i2 e] executes the loop [for x = i1 to i2 do e done]
   in the environment [η]. *)

Definition loop η x i1 i2 e : microvx :=
  if int.lt i2 i1 then
    (* If [i2 < i1] holds, then there is nothing to do. *)
    ok
  else
    (* Otherwise, the loop body [e] must be executed with a binding of [x]
       to [i1]. The value of [e] is ignored. Then, the loop continues. *)
    let η' := (x, (VInt i1)) :: η in
    _v ← eval η' e ;
    (* Every [for] loop terminates, so we could in principle arrange to
       use a recursive call to [loop], but using a [stop] effect is much
       easier. *)
    stop CLoop (η, x, int.add i1 int.one, i2, e)
.
