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

Definition out_of_shift_range {A} : micro A :=
  crash.

Definition if_in_shift_range {A} (i : int) (m : micro A) :=
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

(* [eval_rec_bindings_aux η rbs rbs'] transforms the bindings [rbs'] into an
   environment fragment. Each name [g] is mapped to a recursive closure that
   captures the environment [η] and the bindings [rbs]. *)

(* The parameters [η] and [rbs] are invariant. At the beginning, [rbs']
   is [rbs], so, in general, [rbs'] is a suffix of [rbs]. *)

Fixpoint eval_rec_bindings_aux η rbs rbs' : env :=
  match rbs' with
  | [] => []
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

(* [extends δ ps vs] matches the values [vs] against the patterns [ps].
   In case of success, the result is an extension of the environment
   fragment [δ] with bindings for the bound variables of the patterns [ps].

   A hard failure occurs when [length ps ≠ length vs]. *)

(* Pattern matching is sequential and obeys a left-to-right strategy. This
   is important in the presence of GADTs, as the success of a test in the
   left-hand side of a pair can guarantee the safety of a test in the
   right-hand side of this pair. *)

Definition extends' extend : env -> list pat -> list val -> micro env :=
  fix extends (δ : env) ps vs : micro env :=
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

Definition extendfs' extend : env -> list (var * pat) -> env -> micro env :=
  fix extendfs (δ : env) fps fvs : micro env :=
    match fps with
    | [] => ret δ
    | (f, p) :: fps =>
        v ← lookup_name fvs f ;
        δ ← extend δ p v ;
        δ ← extendfs δ fps fvs ;
        ret δ
    end.

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
  let extends := extends' extend in
  let extendfs := extendfs' extend in
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
         match. If the data constructors do not match, a soft failure takes
         place. *)
      if c =? c' then extend δ p v else next
  | PRecord fps, VRecord fvs =>
      (* A record pattern matches a record value. *)
      (* The pattern may have fewer fields than the value. *)
      extendfs δ fps fvs
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

Definition extends := extends' extend.
Definition extendfs := extendfs' extend.

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

Definition coerces' coerce : list fcoercion -> env -> micro env :=
  fix coerces (xcs : list fcoercion ) xvs : micro env :=
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

Fixpoint coerce (c : coercion) (v : val) : micro val :=
  let coerces := coerces' coerce in
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


(* [eval_sitem ηδ item] evaluates the structure item [item] in the
   double environment [ηδ], yielding an updated double environment. *)

Definition eval_sitem' eval_mexpr eval_bindings (acc : micro envs) item :=
  bind acc (fun ηδ =>
              let '(η, δ) := ηδ in
              match item with
              | ILet bs =>
                  δ' ← eval_bindings η bs;
                  ret_dconcat δ' (η, δ)
              | ILetRec rbs =>
                  let δ' := eval_rec_bindings η rbs in
                  ret_dconcat δ' (η, δ)
              | IModule m me' =>
                  v ← eval_mexpr η me' ;
                  ret_dconcat [(m, v)] (η, δ)
              | IOpen me' =>
                  δ' ← as_struct (eval_mexpr η me') ;
                  ret (δ' ++ η, δ)
              | IInclude me' =>
                  δ' ← as_struct (eval_mexpr η me') ;
                  ret (dconcat δ' (η, δ))
              end).

(* [eval_sitems ηδ items] evaluates the structure items [items] in the
   double environment [ηδ], yielding an updated double environment. *)

Definition eval_sitems' eval_mexpr eval_bindings : list sitem -> envs -> micro envs :=
  λ (items : list sitem) (ηδ : envs),
    let eval_sitem := eval_sitem' eval_mexpr eval_bindings in
    fold_left eval_sitem items (ret ηδ).

(* ------------------------------------------------------------------------ *)

(* [eval_mexpr η me] evaluates the module expression [me] in environment [η],
   yielding a value. *)

Definition eval_mexpr' eval_bindings : env -> mexpr -> micro val :=
  fix eval_mexpr (η : env) (me : mexpr) :=
    let eval_sitems := eval_sitems' eval_mexpr eval_bindings in
    match me with
    | MUnsupported => unsupported_construct
    | MPath π =>
        (* A path is looked up in the environment [η]. *)
        lookup_path η π
    | MCoercion me c =>
        v ← eval_mexpr η me ;
        coerce c v
    | MStruct items =>
        (* evaluate the structure items, yielding an environment [δ], *)
        '(_, δ) ← eval_sitems items (η, []) ;
        (* and wrap it in a [VStruct] value. *)
        ret (VStruct δ)
    end.

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

Definition eval_bindings' eval : env -> list binding -> micro env :=
  λ (η : env) (bs : list binding),
    let f :=
      fun b acc =>
        match b with
        | Binding p e0 =>
            '(v, δ) ← par (eval η e0) acc ;
            extend δ p v
        end
    in
    fold_right f (ret []) bs.

(* ------------------------------------------------------------------------ *)

(* [evals η es] evaluates the expressions [es] in the environment [η],
   producing values [vs]. The expressions are evaluated in parallel. *)

(* [evals] is used to evaluate tuples. *)

Definition evals' eval : env -> list expr -> micro (list val) :=
  λ (η : env) (es : list expr),
    let f :=
      fun e acc =>
        '(v, vs) ← par (eval η e) acc ;
        ret (v :: vs)
    in
    fold_right f (ret []) es.

(* ------------------------------------------------------------------------ *)

(* [evalfs η fes] evaluates the expressions [fes] in the environment [η],
   producing values [fvs]. The expressions are evaluated in parallel.

   Each expression in the list [fes] and each value in the list [fvs]
   is indexed with a record field. *)

(* [evalfs] is used to evaluate record construction expressions. *)

Definition evalfs' eval : env -> list fexpr -> micro (list (field * val)) :=
  λ (η : env) (fes : list fexpr),
    let f :=
      fun fe acc =>
        match fe with
        | Fexpr f e =>
            '(v, fvs) ← par (eval η e) acc ;
            ret ((f, v) :: fvs)
        end
    in
    fold_right f (ret []) fes.

(* ------------------------------------------------------------------------ *)

(* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)

Definition eval_match' eval : env -> val -> list branch -> micro val :=
  λ (η : env) (v : val) (bs : list branch),
    let f :=
      fun b acc =>
        match b with
        | Branch p e =>
            (* Match the value [v] against the pattern [p]. *)
            try
              (extend [] p v)
              (* Success: commit to this branch. Evaluate its body. *)
              (λ δ, η ← ret_concat δ η; eval η e)
              (* Soft failure: abandon this branch. Try the following branches. *)
              (λ tt, acc)
        end
    in
    (* A nonexhaustive [match] construct causes a hard failure. *)
    (* Because the proof system forbids hard failures, the user of
       the system will have to prove that this cannot happen, i.e.,
       every case analysis is exhaustive. *)
    fold_right f (match_failure()) bs.

Fixpoint eval η e : micro val :=
  let evals := evals' eval in
  let evalfs := evalfs' eval in
  let eval_match := eval_match' eval in
  let eval_bindings := eval_bindings' eval in
  let eval_mexpr := eval_mexpr' eval_bindings in
  match e with
  | EUnsupported =>
      unsupported_construct
  | EChar c =>
      ret (VChar c)
  | EPath π =>
      (* A path [π] is looked up in the environment [η]. *)
      lookup_path η π
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
      lookup_name fvs f
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
      try
        (eval_bindings η bs)
      (λ δ, η ← ret_concat δ η; eval η e)
      match_failure
  | ELetRec rbs e =>
      (* Extend the environment with a mapping of each function name in [rbs]
         to a suitable recursive closure; then, evaluate [e]. *)
      let δ := eval_rec_bindings η rbs in
      η ← ret_concat δ η;
      eval η e
  | ELetModule M me e =>
      v ← eval_mexpr η me ;
      let δ := [(M, v)] in
      η ← ret_concat δ η;
      eval η e
  | ELetOpen me e =>
      δ ← as_struct (eval_mexpr η me) ;
      η ← ret_concat δ η;
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
      v ← eval η e ;
      eval_match η v bs
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
      let test : micro val :=
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

Definition evals := evals' eval.
Definition evalfs := evalfs' eval.
Definition eval_match := eval_match' eval.
Definition eval_bindings := eval_bindings' eval.
Definition eval_mexpr := eval_mexpr' eval_bindings.
Definition eval_sitems := eval_sitems' eval_mexpr eval_bindings.

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
    let η' := (x, (VInt i1)) :: η in
    _v ← eval η' e ;
    (* Every [for] loop terminates, so we could in principle arrange to
       use a recursive call to [loop], but using a [stop] effect is much
       easier. *)
    stop CLoop (η, x, int.add i1 int.one, i2, e)
.
