From Stdlib Require Import Orders Sorting.
From osiris Require Import base.
From osiris.logic Require Import list_z.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code strategy.

Module EvalF (Strat : Strategy).

Local Infix "=?" := String.eqb.

(* Conventional metavariables. *)

Implicit Type g x : var.
Implicit Type c : data.
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
  crash "unsupported_construct".

Definition assertion_failure {A E} : micro A E :=
  crash "assertion_failure".

Definition division_by_zero {A E} : micro A E :=
  crash "division_by_zero".

Definition length_mismatch {A E} (msg : string) : micro A E :=
  crash ("length_mismatch: " ++ msg).

Definition match_failure {A E} (tt : unit) : micro A E :=
  crash "match_failure".

Definition missing_field {A E} (x : var) : micro A E :=
  crash ("missing_field: " ++ x).

Definition missing_variable {A E} (x : var) : micro A E :=
  crash ("missing_variable: " ++ x).

Definition missing_variable_or_field {A E} (x : var) : micro A E :=
  crash ("missing_variable_or_field: " ++ x).

Definition physical_equality_error {A E} (msg : string) : micro A E :=
  crash ("physical_equality_error: " ++ msg).

Definition structural_equality_error {A E} (msg : string) : micro A E :=
  crash ("structural_equality_error: " ++ msg).

Definition structural_ordering_error {A E} (msg : string) : micro A E :=
  crash ("structural_ordering_error: " ++ msg).

Definition type_mismatch {A E} (msg : string) : micro A E :=
  crash ("type_mismatch: " ++ msg).

(* The logical operations [lsl], [lsr], and [asr] require their second
   operand [i2] to satisfy [0 <= i2 <= zintsize]. This is perhaps more
   restrictive than necessary, but this requirement appears in the OCaml
   reference manual. If this condition is not met then, according to the
   manual, the result is an unspecified integer value. In this semantics,
   we adopt a more pessimistic (more permissive) specification and allow
   the result in that case to be a crash. This removes the need for an
   effectful operation that produces an arbitrary integer result. We may
   revisit this in the future. *)

Definition in_shift_range_b (i : int) : bool :=
  (0 <=? signed i) && (signed i <=? int.zintsize).

Definition out_of_shift_range {A E} : micro A E :=
  crash "out_of_shift_range".

Definition if_in_shift_range {A E} (i : int) (m : micro A E) :=
  if in_shift_range_b i then m else out_of_shift_range.

(* ------------------------------------------------------------------------ *)

(* Local notations. *)

(* [ok] is an inert computation. It produces the value [VUnit]. *)

Notation ok :=
  (ret (VData "()" [])).

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

Definition val_as_loc_opt (v : val) : option loc :=
  match v with
  | VLoc l =>
      Some l
  | _ =>
      None
  end.

Definition as_loc {E} (m : micro val E) : micro loc E :=
  v ← m ;
  val_as_loc v.

(* ------------------------------------------------------------------------ *)

(* [val_as_block v] checks that the value [v] is a language-level pointer
   to a block and returns its meta-level value. *)

Definition val_as_block {E} (v : val) : micro block E :=
  match v with
  | VBlock l =>
      ret l
  | _ =>
      type_mismatch "location value expected"
  end.

Definition val_as_block_opt (v : val) : option block :=
  match v with
  | VBlock l =>
      Some l
  | _ =>
      None
  end.

Definition as_block {E} (m : micro val E) : micro block E :=
  v ← m ;
  val_as_block v.


(* ------------------------------------------------------------------------ *)

(* [val_as_thread v] checks that the value [v] is a language-level thread
   value and returns its meta-level value. *)

Definition val_as_thread {E} (v : val) : micro thread E :=
  match v with
  | VThread t =>
      ret t
  | _ =>
      type_mismatch "location value expected"
  end.

Definition as_thread {E} (m : micro val E) : micro thread E :=
  v ← m ;
  val_as_thread v.


(* ------------------------------------------------------------------------ *)

(* [val_as_cont v] checks that the value [v] is a language-level continuation
   value and returns its meta-level value. *)

Definition val_as_cont {E} (v : val) : micro cont E :=
  match v with
  | VCont l =>
      ret l
  | _ =>
      type_mismatch "continuation value expected"
  end.

Definition as_cont {E} (m : micro val E) : micro cont E :=
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

(* [val_as_array v] checks that the value [v] is a language-level array
   value and returns a tuple of the location of the first element,
   and the length. *)

Definition val_as_array (v : val) : micro (list loc) exn :=
  match v with
  | VBlock l =>
      '(_, ls) ← load_block l ;
      ret ls
  | _ =>
      type_mismatch "array expected"
  end.

Definition as_array (m : microvx) : micro (list loc) exn :=
  v ← m ;
  val_as_array v.

(* ------------------------------------------------------------------------ *)

(* [val_as_struct v] checks that the value [v] is a value of the form
   [VStruct xvs] and returns its content [xvs]. *)

(* It is useful to have [val_as_struct_opt] when performing lookups
   through modules, and to have [as_struct] when evaluating module
   expressions. *)

Definition val_as_struct_opt (v : val) : option env :=
  match v with
  | VStruct xvs =>
      Some xvs
  | _ =>
      None
  end.

Definition val_as_struct {E} (v : val) : micro env E :=
  match v with
  | VStruct xvs =>
      ret xvs
  | _ =>
      type_mismatch "structure expected"
  end.

Definition as_struct {E} (m : micro val E) : micro env E :=
  v ← m ;
  val_as_struct v.

(* ------------------------------------------------------------------------ *)

Section LookupEnv.

(* We locally open the stdpp notation scope to get do-notation for
   the option monad.

   Opening and then closing the scope results in losing notation access
   to other useful notations, hence the [Local Open]. *)
Local Open Scope stdpp.

(* [lookup_name η x] looks up the name [x] in the environment [env],
   producing a value. A hard failure occurs if [x] is unbound. *)

(* This function is used also to look up fields in records and module
   components in modules. *)

Fixpoint lookup_name η x : option val :=
  match η with
  | (x', v) :: η =>
      if x =? x' then Some v else lookup_name η x
  | [] => None
  end.

(* ------------------------------------------------------------------------ *)

(* [lookup_path η π] looks up the path [π] in the environment [η]. *)

Fixpoint lookup_path η π : option val :=
  match π with
  | [] => None
  | [x] =>
      lookup_name η x
  | x1 :: π =>
      (* We retrieve the value bound to the name [x1] in [η]. *)
      v ← lookup_name η x1 ;
      (* We expect this value to be a structure. *)
      xvs ← val_as_struct_opt v ;
      (* The content of a structure is an environment,
         so we can look up [π] in the environment [xvs]. *)
      lookup_path xvs π
  end.

End LookupEnv.

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

(* The parameters [η] and [rbs] are invariant. Initially, [rbs'] equals [rbs],
   so [rbs'] is always a suffix of [rbs]. *)

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

Fixpoint lookup_rec_bindings rbs g : option anonfun :=
  match rbs with
  | RecBinding g' a :: rbs =>
      if g =? g' then Some a else lookup_rec_bindings rbs g
  | [] =>
      None
  end.

(* ------------------------------------------------------------------------ *)

(* This section defines the auxiliary functions that are mutually recursive
   with [eval_pat]. *)

Section EvalPat.

Local Open Scope stdpp.

Variable eval_pat : env → env → pat → val → option env.

(* ------------------------------------------------------------------------ *)

(* [eval_pats η δ ps vs] matches the values [vs] against the patterns [ps].

   In case of success, the result is an extension of the environment (or
   environment fragment) [δ] with bindings for the bound variables of the
   patterns [ps].

   A failure occurs when [length ps ≠ length vs]. *)

(* Pattern matching is sequential and obeys a left-to-right strategy. This
   is important in the presence of GADTs, as the success of a test in the
   left-hand side of a pair can guarantee the safety of a test in the
   right-hand side of this pair. *)

Fixpoint pre_eval_pats (η δ : env) ps vs : option env :=
  let eval_pats := pre_eval_pats in
  match ps, vs with
  | [], [] =>
      Some δ
  | p::ps, v::vs =>
      δ ← eval_pat η δ p v ;
      δ ← eval_pats η δ ps vs ;
      Some δ
  | _::_, [] =>
      None
  | [], _::_ =>
      None
 end.

(* [eval_fpats η δ fps fvs] matches the field-indexed values [fvs] against the
   field-indexed patterns [fps].

   In case of success, the result is an extension of the environment
   (or environment fragment) [δ] with bindings for the bound variables of
   the patterns [fps].

   A failure occurs if a field is present in [fps] but absent in [fvs]. *)

Fixpoint pre_eval_fpats (η δ : env) fps fvs : option env :=
  let eval_fpats := pre_eval_fpats in
  match fps with
  | [] => Some δ
  | (f, p) :: fps =>
      v ← lookup_name fvs f ;
      δ ← eval_pat η δ p v ;
      δ ← eval_fpats η δ fps fvs ;
      Some δ
  end.

End EvalPat.

Section EvalPat.

Local Open Scope stdpp.

(* [eval_pat η δ p v] matches the value [v] against the pattern [p].

   In case of success, the result is an extension of the environment
   (or fragment) [δ] with bindings for the bound variables of the pattern [p].

   A failure occurs if [p] does not match [v], e.g., if [p] selects a data
   constructor [c] but [v] carries a distinct data constructor [c'].

   A failure takes place if [p] and [v] have incompatible types,
   e.g., if [p] is a tuple pattern and [v] is not a tuple value or
   is a tuple value of an incorrect arity.

   [η] is the current environment, it is only used to look up the location
   corresponding to a path [π] in the pattern [PXData π _] for extensible
   variant types *)

(* We assume that the pattern [p] is linear: that is, no variable is
   bound twice. This property is enforced by the OCaml type-checker. *)

Local Fixpoint pre_eval_pat η δ p v : option env :=
  let eval_pat := pre_eval_pat in
  let eval_pats := pre_eval_pats eval_pat in
  let eval_fpats := pre_eval_fpats eval_pat in
  match p, v with
  | PUnsupported, _ =>
      None
  | PAny, _ =>
      (* A wildcard pattern always succeeds. *)
      Some δ
  | PVar x, _ =>
      (* A variable pattern always succeeds, and causes the environment
         to be extended. *)
      Some ((x, v) :: δ)
  | PAlias p x, _ =>
      (* An alias pattern [p as x] is an intersection pattern: the value
         [v] must match both the pattern [p] and the pattern [x]. *)
      δ ← eval_pat η δ p v ;
      Some ((x, v) :: δ)
  | POr p1 p2, _ =>
      (* A disjunction pattern [p1 | p2] requires that the value [v]
         match either [p1] or [p2]. *)
      (eval_pat η δ p1 v) ∪ (eval_pat η δ p2 v)
  | PTuple ps, VTuple vs =>
      (* A tuple pattern matches a tuple value. *)
      eval_pats η δ ps vs
  | PData c ps, VData c' vs =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a meta-level exception
         is raised. *)
      if c =? c' then eval_pats η δ ps vs else None
  | PXData π ps, VXData l vs =>
      (* A data pattern for an extensible data type matches a data value, provided
         the data constructors correspond to the same location in the environment.
         If the data constructors do not match, a meta-level exception is raised. *)
      vl' ← (lookup_path η π) ;
      l' ← val_as_loc_opt vl' ;
      if (locations.eqb l l') then eval_pats η δ ps vs else None
  | PRecord fps, VRecord fvs =>
      (* A record pattern matches a record value. *)
      (* The pattern may have fewer fields than the value. *)
      eval_fpats η δ fps fvs
  | PInt z, VInt i' =>
      let i := int.repr z in
      if int.eq i i' then Some δ else None
  | PChar c', VChar c =>
      if Ascii.eqb c c' then Some δ else None
  | PString s', VString s =>
      if s =? s' then Some δ else None
  | PTuple _, _ =>
      None
  | PData _ _, _ =>
      None
  | PXData _ _, _ =>
      None
  | PRecord _, _ =>
      None
  | PInt _, _ =>
      None
  | PChar _, _ =>
      None
  | PString _, _ =>
      None
  end.

Local Definition eval_pat_aux : seal (pre_eval_pat).
Proof. by eexists. Qed.
Definition eval_pat := eval_pat_aux.(unseal).
Lemma fold_pre_eval_pat :
  pre_eval_pat = eval_pat.
Proof. unfold eval_pat; by rewrite seal_eq. Qed.

Local Definition eval_pats_aux : seal (pre_eval_pats eval_pat).
Proof. by eexists. Qed.
(* Top-level definition for [extends] *)
Definition eval_pats := eval_pats_aux.(unseal).
Lemma fold_pre_eval_pats :
  pre_eval_pats eval_pat = eval_pats.
Proof. unfold eval_pats; by rewrite seal_eq. Qed.

Local Definition eval_fpats_aux : seal (pre_eval_fpats eval_pat).
Proof. by eexists. Qed.
(* Top-level definition for [extendfs] *)
Definition eval_fpats := eval_fpats_aux.(unseal).

(* [eval_cpat η δ cp o] matches the outcome [o] against
   the computation pattern [cp]. *)

Fixpoint eval_cpat η δ cp o : option env :=
  match cp, o with
  | CVal p, O3Ret v =>
      (* A value pattern matches a return. *)
      eval_pat η δ p v
  | CExc p, O3Throw v =>
      (* An exception pattern matches a throw. *)
      eval_pat η δ p v
  | CEff pe pk, O3Perform e k =>
      δ ← eval_pat η δ pe e ;
      (* [pk] is a pattern for the continuation [k].
         It can only be a [PVar] or a [PAny]. *)
      eval_pat η δ pk (VCont k)
  | COr cp1 cp2, _  =>
      (* A [COr] either matches its first or second branch. *)
      (eval_cpat η δ cp1 o) ∪ (eval_cpat η δ cp2 o)
  | _, _ =>
      (* If [o] and [cp] don't match, we fail and continue to
         the next branch.*)
      None
  end.

End EvalPat.

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
  please_eval η e.

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
      a ← widen (lookup_rec_bindings rbs g) ;
      (* Then, proceed as in the case of a non-recursive closure. *)
      acall η a v2
   | _ =>
      type_mismatch "closure expected"
   end.

(* ------------------------------------------------------------------------ *)

(* [phys_eq_val v1 v2] implements OCaml's physical equality operator [==]. *)

(* This operator can be applied to:
   - memory locations (as long as at least one of them is mutable),
   - constructors with no arguments *)

Definition phys_eq_val v1 v2 : micro bool exn :=
  match v1, v2 with
  | VLoc l1, VLoc l2 =>
      ret (locations.eqb l1 l2)
  | VBlock l1, VBlock l2 =>
      '((t1, _), (t2, _)) ← par (load_block l1) (load_block l2) ;
      match t1, t2 with
      | Mut, _ | _, Mut => ret (locations.eqb l1 l2)
      | _, _ => physical_equality_error "invalid or unsupported arguments"
      end
  | VCont k1, VCont k2 =>
      ret (locations.eqb k1 k2)
  | VData c1 [], VData c2 [] =>
      ret (c1 =? c2)
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
      if c1 =? c2 then
        eq_vals v1 v2
      else
        ret false
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

Implicit Type ηδ : envs.

(* ------------------------------------------------------------------------ *)

Section Coercions.

Local Open Scope stdpp.

Definition pre_coerces coerce :=
  fix coerces (xcs : list fcoercion ) (xvs : env) : option env :=
    match xcs with
    | [] => Some []
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
        Some ((x, v) :: xvs)
    end.

(* [coerce c v] applies the module coercion [c] to the module value [v]. *)

Fixpoint coerce (c : coercion) (v : val) : option val :=
  let coerces := pre_coerces coerce in
  match c with
  | CIdentity =>
      Some v
  | CStruct xcs =>
      (* [v] must be a structure, whose components form a list [xvs]. *)
      xvs ← val_as_struct_opt v ;
      (* From [xvs], fetch the components named in the list [xcs], and
         apply the corresponding coercions to them. *)
      xvs ← coerces xcs xvs ;
      Some (VStruct xvs)
  end.

End Coercions.

(* ------------------------------------------------------------------------ *)

(* [eval_type_extensions xs] takes a list of (names of) constructors for an
   extensible type, and ties those names to a fresh location.

  For example, if we were evaluating the following type extension:
  ```
  type exn +=
    | New_exception
    | Not_found
  ```
  We would find ourselves with an environment of the form
  [("Not_found", l2) :: ("New_exception", l1) :: η]
  with [l1] and [l2] fresh locations, uniquely identifying the new
  constructors. *)

Fixpoint eval_type_extensions (cs : list name) :=
  match cs with
  | [] => ret []
  | c :: cs =>
      l ← alloc VUnit;
      η ← eval_type_extensions cs;
      ret ((c, VLoc l) :: η)
  end.

(* ------------------------------------------------------------------------ *)

(* A large group of mutually recursive functions follows. We use several
   sections to make open recursion (parameterization) more lightweight. The
   functions that need forward edges are [eval_bindings], [eval_mexpr], and
   [eval]. *)

Section EvalBindings.

Variable eval_bindings : env → list binding → micro env exn.

Section Eval.

Variable eval : env → expr → microvx.

Section EvalMExpr.

Variable eval_mexpr : env → mexpr → microvx.

(* [eval_sitem ηδ item] evaluates the structure items [item] in the
   double environment [ηδ], yielding an updated double environment.

   For an intuitive understand of the double environment, consider
   the difference between [IOpen me'] and [IInclude me'].
   Inclusion results in the names of [me'] being exported, while
   opening doesn't. *)

Definition pre_eval_sitem (ηδ : envs) (item : sitem) : micro envs exn :=
  let '(η, δ) := ηδ in
  match item with
  | ILet bs =>
      (* Evaluate the left-hand side of a [let], obtain an environment
         fragment from the new bindings, and add those bindings to
         both environments.
         There could be multiple bindings from [let/and]s,
         or from destructing patterns. *)
      δ' ← eval_bindings η bs;
      ret  (δ' ++ η, δ' ++ δ)
  | ILetRec rbs =>
      (* Evalute a [let rec], get the resulting environment fragment,
         and add those bindings to both environments. *)
      let δ' := eval_rec_bindings η rbs in
      ret (δ' ++ η, δ' ++ δ)
  | IModule m me' =>
      (* Evaluate the module [me'], bind the result to the name [m] in
         both environments. *)
      v ← eval_mexpr η me' ;
      ret ([(m, v)] ++ η, [(m, v)] ++ δ)
  | IOpen me' =>
      (* Evaluate the module expression [me'] into an environment
         fragment. Add that environment fragment only to the current
         local environment. *)
      δ' ← as_struct (eval_mexpr η me') ;
      ret (δ' ++ η, δ)
  | IInclude me' =>
      (* Evaluate the module expression [me'] into an environment
         fragment. Add that environment fragment only to both the
         current local environment, and the exported environment *)
      δ' ← as_struct (eval_mexpr η me') ;
      ret (δ' ++ η, δ' ++ δ)
  | IExternal x e =>
      (* We treat external declarations as the binding of the name of
         the external to the eta-expansion of the corresponding
         primitive.

         For example,
         `external array_get : int → array a' → a'`
         is treated as giving the name ["array_get"] to the
         eta-expansion of the [EArrayGet] primitive. *)
      v ← eval [] e;
      ret ((x, v) :: η, (x, v) :: δ)
  | IExtend cs =>
      (* Extend the environments with bindings from each new extensible
         constructor name in [cs] to a fresh location. *)
      δ' ← eval_type_extensions cs;
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
  | MFunctor x items =>
      ret (VFunctor η x items)
  end.

End Eval.

End EvalBindings.

Section Eval.

Variable eval : env → expr → microvx.

(* ------------------------------------------------------------------------ *)

(* Evaluate the expression [e], yielding a value [v],
   and produce an environment fragment [η]. *)

(* A binding is a pair [p = e]. The expressions in the right-hand sides of the
   bindings [bs] are evaluated in parallel. The values thus obtained are then
   matched against the patterns in the left-hand sides. The pattern matching
   process is sequential. *)

(* Every pattern is considered irrefutable, so if a pattern [p] does not
   match the corresponding value [v], a crash occurs via [widen]. *)

Definition eval_binding η '(Binding p e : binding) : micro env exn :=
  v ← eval η e;
  widen (eval_pat η [] p v).

(* [eval_bindings η bs] evaluates the bindings [bs] in the environment [η],
   producing an environment fragment. *)

(* [eval_bindings] is used to evaluate the [let/and] construct. *)

(* If we chose to encode the multiple-let-and construct [let p_i = e_i in e]
   as [let (p_i) = (e_i) in e], using a tuple and a single-let-and construct,
   then [eval_bindings] would disappear. We prefer to avoid encodings. *)

Fixpoint pre_eval_bindings (η : env) (bs : list binding) : micro env exn :=
  let eval_bindings := pre_eval_bindings in
  match bs with
  | [] =>
      ret []
  | b :: bs =>
      '(η, δ) ← pair_op Strat.let_and_order
        (eval_binding η b)
        (* In parallel, evaluate the bindings [bs],
           yielding an environment fragment [δ]. *)
        (eval_bindings η bs);
      (* Finally, concatenate the two environment fragments. *)
      ret (η ++ δ)
  end.

(* ------------------------------------------------------------------------ *)

(* [evals η es] evaluates the expressions [es] in the environment [η],
   producing values [vs]. The expressions are evaluated in parallel. *)

(* [evals] is used to evaluate tuples and arguments of constructors. *)

Fixpoint pre_evals (η : env) (es : list expr) : micro (list val) exn :=
  let evals := pre_evals in
  match es with
  | [] =>
      ret []
  | e :: es =>
      '(v, vs) ← pair_op Strat.tuple_order (eval η e) (evals η es) ;
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
      (* Sequentializing (be it left-to-right or right-to-left) is wrong here,
       because the order depends on the type declaration *)
      '(v, fvs) ← par (eval η e) (evalfs η fes) ;
      ret ((f, v) :: fvs)
  end.

(* ------------------------------------------------------------------------ *)

(* [eval_branches η o bs] matches the computational outcome [o] against
   the branches [bs]. *)

 (* This function assumes that the handler defined by the branches [bs]
    has already been reinstalled over the continuation of [o], if [o]
    is a performed effect.  *)

Fixpoint pre_eval_branches η (o : outcome3 val exn) (bs : list branch) : microvx :=
  match bs with
  | [] =>
      (* If we have exhausted the branches of the match. *)
      (match o with
       | O3Ret _ =>
           (* A non-exhaustive match on a value is a crash. *)
           match_failure()
       | O3Throw v =>
           (* An unhandled exception is propagated upwards. *)
           throw v
       | O3Perform v l =>
           (* An unhandled effect is propagated upwards. *)
           (* [l] is a stored continuation: that is, it is a heap address
              where a semantic continuation is stored.
              By writing [λ o, resume l o], we convert it back to
              a semantic continuation,
              which forms a suitable argument for [try2].
              In summary, we perform the same effect again,
              with the same continuation. *)
           try2 (perform v) (λ o, resume l o)
       end)
  | Branch cp e :: bs =>
      (* If we are facing a branch [| cp -> e ]. *)
      (* We attempt to match the outcome [o] against the pattern [cp]. *)
      match (eval_cpat η η cp o) with
      (* In case of success, we evaluate [e] in an environment
         that has been extended by [eval_cpat]. *)
      | Some η'  => eval η' e
      (* If case of failure, we move on to the remaining branches. *)
      | None => pre_eval_branches η o bs
      end
  end.


(* [wrap_outcome η bs o] matches on the computation outcome [o].
   If that outcome is a performed effect, we reinstall the handler
   described by the branches [bs] over the continuation of the
   outcome.  *)

Definition wrap_outcome {A E} η bs o : micro (outcome3 A E) exn :=
  match o with
  | O3Perform e k =>
      (* If we are matching on an effect, we reinstall the handler on
         top of that effect's continuation. *)
      k ← wrap k η bs ;
      ret (O3Perform e k)
  | _ =>
      ret o
  end.

(* A shallow handler must allow itself to vanish only if it is consumed by an
   effect. [all_branches] keeps track of all the branches in order to
   re-install the handler if it has not been consumed. *)

Fixpoint pre_shallow_eval_branches η bs all_bs o :=
  match bs with
  | [] =>
      (match o with
       | O3Ret _ =>
           match_failure()
       | O3Throw e =>
           throw e
       | O3Perform e l =>
           (* If we don't catch the effect, we reinstall the handler on
              top of the continuation (using a shallow wrap).
              We then reperform the effect with the same continuation
              it had initially. *)
           l ← shallow_wrap l η all_bs;
           try2 (perform e) (λ o, resume l o)
       end)
  | Branch cp e :: bs =>
      match (eval_cpat η η cp o) with
      | Some δ => eval δ e
      | None => pre_shallow_eval_branches η bs all_bs o
      end
  end.

End Eval.

(* ------------------------------------------------------------------------ *)

Section EvalBranches.

Variable eval_branches : env -> (outcome3 val exn) -> list branch -> microvx.

Definition pre_wrap_eval_branches η bs (o : outcome3 val exn) : microvx :=
  o ← wrap_outcome η bs o ;
  eval_branches η o bs.

End EvalBranches.

(* ------------------------------------------------------------------------ *)

(* [eval η e] evaluates the expression [e] in environment [η].

   In case of success, the result is a value.

   A hard failure reflects a dynamic type error (a crash).

   A soft failure reflects an exception, which can be caught.

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

Fixpoint pre_eval η e {struct e} : microvx :=
  let eval := pre_eval in
  let evals := pre_evals eval in
  let evalfs := pre_evalfs eval in
  let eval_branches := pre_eval_branches eval in
  let wrap_eval_branches := pre_wrap_eval_branches eval_branches in
  let shallow_eval_branches := pre_shallow_eval_branches eval in
  let eval_bindings := pre_eval_bindings eval in
  let eval_mexpr := pre_eval_mexpr eval_bindings eval in
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
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      call v1 v2
  | ETuple es =>
      (* The tuple components are evaluated using evals. *)
      vs ← evals η es ;
      ret (VTuple vs)
  | EData c es =>
      v ← evals η es ;
      ret (VData c v)
  | EXData π es =>
      l ← as_loc (widen (lookup_path η π)) ;
      v ← evals η es ;
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
  | EArrayLit es =>
      vs ← evals η es ;
      ls ← allocn vs ;
      l ← alloc_block ls ;
      ret (VBlock l)
  | EArrayLength e =>
      ls ← as_array (eval η e) ;
      ret (VInt (repr (length ls)))
  | EArrayGet e1 e2 =>
      '(ls, i) ← par (as_array (eval η e1)) (as_int (eval η e2)) ;
      match ls !! (signed i) with
      | Some l => load l
      | None => crash "index out of bounds"
      end
  | EArraySet e1 e2 e3 =>
      '(ls, (i, v)) ← par (as_array (eval η e1))
                       (par (as_int (eval η e2)) (eval η e3));
        match ls !! (signed i) with
        | Some l => store l v
        | None => crash "index out of bounds"
        end
  | EArrayMake e1 e2 =>
      '(n, v) ← par (as_int (eval η e1)) (eval η e2) ;
      let n : Z := signed n in
      if decide (0 ≤ n ≤ max_array) then
        ls ← allocn (replicate n v) ;
        l ← alloc_block ls ;
        ret (VBlock l)
      else crash "invalid_argument: Array.make"
  | EFreeze e =>
      l ← as_loc (eval η e) ;
      ret (VLoc l Immut)
  | EUnfreeze e =>
      l ← as_loc (eval η e) ;
      ret (VLoc l Mut)
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
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.add i1 i2))
  | EIntSub e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.sub i1 i2))
  | EIntMul e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.mul i1 i2))
  | EIntDiv e1 e2 =>
      (* Signed division is used. *)
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.divs i1 i2))
  | EIntMod e1 e2 =>
      (* Signed remainder is used. *)
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.mods i1 i2))
  | EIntLand e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.land i1 i2))
  | EIntLor e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lor i1 i2))
  | EIntLxor e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lxor i1 i2))
  | EIntLnot e =>
      i ← as_int (eval η e) ;
      ret (VInt (int.lnot i))
  | EIntLsl e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsl i1 i2)))
  | EIntLsr e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsr i1 i2)))
  | EIntAsr e1 e2 =>
      '(i1, i2) ← pair_op Strat.fun_app_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.asr i1 i2)))
  | EFloat f =>
      ret (VFloat f)
  | EOpPhysEq e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← phys_eq_val v1 v2 ;
      ret (VBool b)
  | EOpEq e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← eq_val v1 v2 ;
      ret (VBool b)
  | EOpNe e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← ne_val v1 v2 ;
      ret (VBool b)
  | EOpLt e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← lt_val v1 v2 ;
      ret (VBool b)
  | EOpLe e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← le_val v1 v2 ;
      ret (VBool b)
  | EOpGt e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      b ← gt_val v1 v2 ;
      ret (VBool b)
  | EOpGe e1 e2 =>
      '(v1, v2) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
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
      (* This [EMatch] construct may have effect-handling branches of the form
         [| effect ... -> ...]. We execute the expression [e] under a handler,
         which inspects the outcome of this computation using the branches
         [bs]. *)
      Handle (eval η e) (λ o, wrap_eval_branches η bs o)
  | EShallowMatch e bs =>
      handle (eval η e) (λ o, shallow_eval_branches η bs bs o)
  | ERaise e =>
      exn ← eval η e ;
      throw exn
  | EPerform e =>
      eff ← eval η e ;
      perform eff
  | EContinue e1 e2 =>
      '(l, v) ← par (as_cont (eval η e1)) (eval η e2) ;
      resume l (O2Ret v)
  | EDiscontinue e1 e2 =>
      '(l, v) ← par (as_cont (eval η e1)) (eval η e2) ;
      resume l (O2Throw v)
  | EWhile e body =>
      b ← as_bool (eval η e) ;
      if (b : bool) then
        _ ← eval η body ;
        please_eval η (EWhile e body)
      else
        ok
  | EFor x e1 e2 e =>
      (* The bounds are evaluated first. *)
      '(i1, i2) ← pair_op Strat.for_bounds_order (as_int (eval η e1)) (as_int (eval η e2)) ;
      (* Then, the loop is executed. *)
      loop η x i1 i2 e
  | EAssertFalse =>
      assertion_failure
  | EAssert e =>
      (* OCaml runtime assertions are erased when a module is compiled with
         the compiler flag [-noassert]; they are retained otherwise. We do not
         wish to depend on this flag, so we make a non-deterministic choice:
         either the runtime test is skipped, or it is executed. This forces
         the user to prove that the program is safe in both scenarios. *)
      let run_test := success ← as_bool (eval η e); if (success : bool) then ok else assertion_failure in
      match Strat.run_asserts with
      | No => ok
      | Yes => run_test
      | Unspecified => choose ok run_test
      end
  | ERef e =>
      v ← eval η e ;
      l ← alloc v ;
      ret (VLoc l)
  | ELoad e =>
      l ← as_loc (eval η e) ;
      load l
  | EStore e1 e2 =>
      '(l, v) ← pair_op Strat.fun_app_order (as_loc (eval η e1)) (eval η e2) ;
      store l v
  | EExchange e1 e2 =>
      '(l, v) ← pair_op Strat.fun_app_order (as_loc (eval η e1)) (eval η e2) ;
      exchange l v
  | ECAS e1 e2 e3 =>
      '(l, seen, v) ← par (par (as_loc (eval η e1)) (eval η e2)) (eval η e3);
      cas l seen v
  | EFAA e1 e2 =>
      '(l, i) ← par (as_loc (eval η e1)) (as_int (eval η e2)) ;
      faa l i
  | EIgnore e =>
      _ ← eval η e ;
      ok
  | EFork e1 e2 =>
      '(f, v) ← pair_op Strat.fun_app_order (eval η e1) (eval η e2) ;
      fork f v
  | EJoin e =>
      t ← as_thread (eval η e) ;
      join t
end.


(* -------------------------------------------------------------------------- *)

(* Sealing definitions. *)

Local Definition eval_aux : seal (pre_eval).
Proof. by eexists. Qed.
(* Top-level definition for [eval] *)
Definition eval := eval_aux.(unseal).
Lemma fold_pre_eval :
  pre_eval = eval.
Proof. unfold eval; by rewrite seal_eq. Qed.

Local Definition evals_aux : seal (pre_evals eval).
Proof. by eexists. Qed.
(* Top-level definition for [evals] *)
Definition evals := evals_aux.(unseal).
Lemma fold_pre_evals :
  pre_evals eval = evals.
Proof. unfold evals; by rewrite seal_eq. Qed.

Local Definition evalfs_aux : seal (pre_evalfs eval).
Proof. by eexists. Qed.
(* Top-level definition for [evalfs] *)
Definition evalfs := evalfs_aux.(unseal).
Lemma fold_pre_evalfs :
  pre_evalfs eval = evalfs.
Proof. unfold evalfs; by rewrite seal_eq. Qed.

Local Definition eval_branches_aux : seal (pre_eval_branches eval).
Proof. by eexists. Qed.
Definition eval_branches := eval_branches_aux.(unseal).
Lemma fold_pre_eval_branches :
  pre_eval_branches eval = eval_branches.
Proof. unfold eval_branches; by rewrite seal_eq. Qed.

Local Definition wrap_eval_branches_aux : seal (pre_wrap_eval_branches eval_branches).
Proof. by eexists. Qed.
Definition wrap_eval_branches := wrap_eval_branches_aux.(unseal).
Lemma fold_pre_wrap_eval_branches :
  pre_wrap_eval_branches eval_branches = wrap_eval_branches.
Proof. unfold wrap_eval_branches; by rewrite seal_eq. Qed.

Local Definition shallow_eval_branches_aux : seal (pre_shallow_eval_branches eval).
Proof. by eexists. Qed.
Definition shallow_eval_branches := shallow_eval_branches_aux.(unseal).
Lemma fold_pre_shallow_eval_branches :
  pre_shallow_eval_branches eval = shallow_eval_branches.
  Proof. unfold shallow_eval_branches; by rewrite seal_eq. Qed.

(* [shallow_eval_branches] needs to keep the initial handler branches around
   for reinstallation. We use notations to hide this as it busies the
   goal. *)

Notation "'shallow_eval_branches' η o bs" :=
  (shallow_eval_branches η o bs _)
    (at level 8, only printing).

Local Definition eval_bindings_aux : seal (pre_eval_bindings eval).
Proof. by eexists. Qed.
(* Top-level definition for [eval_bindings] *)
Definition eval_bindings := eval_bindings_aux.(unseal).
Lemma fold_pre_eval_bindings :
  pre_eval_bindings eval = eval_bindings.
Proof. unfold eval_bindings; by rewrite seal_eq. Qed.

Local Definition eval_mexpr_aux : seal (pre_eval_mexpr eval_bindings eval).
Proof. by eexists. Qed.
(* Top-level definition for [eval_mexpr] *)
Definition eval_mexpr := eval_mexpr_aux.(unseal).
Lemma fold_pre_eval_mexpr :
  pre_eval_mexpr eval_bindings eval = eval_mexpr.
Proof. unfold eval_mexpr; by rewrite seal_eq. Qed.

Local Definition eval_sitem_aux : seal (pre_eval_sitem eval_bindings eval eval_mexpr).
Proof. by eexists. Qed.
(* Top-level definition for [eval_sitem] *)
Definition eval_sitem : envs → sitem → micro envs exn := eval_sitem_aux.(unseal).
Lemma fold_pre_eval_sitem :
  pre_eval_sitem eval_bindings eval eval_mexpr = eval_sitem.
Proof. unfold eval_sitem; by rewrite seal_eq. Qed.

Local Definition eval_sitems_aux : seal (pre_eval_sitems eval_bindings eval eval_mexpr).
Proof. by eexists. Qed.
(* Top-level definition for [eval_sitems] *)
Definition eval_sitems := eval_sitems_aux.(unseal).
Lemma fold_pre_eval_sitems :
  pre_eval_sitems eval_bindings eval eval_mexpr = eval_sitems.
Proof. unfold eval_sitems; by rewrite seal_eq. Qed.

(* -------------------------------------------------------------------------- *)

(* Unfolding and simplifying definitions. *)

Ltac simpl_eval :=
  (unfold eval;
   rewrite seal_eq;
   (progress simpl pre_eval);
   rewrite ?fold_pre_eval,
     ?fold_pre_evals,
     ?fold_pre_evalfs,
     ?fold_pre_eval_branches,
     ?fold_pre_eval_bindings,
     ?fold_pre_eval_mexpr,
     ?fold_pre_wrap_eval_branches)
  || fail "Unable to simplify application of eval".

Ltac simpl_evals :=
  (unfold evals;
   rewrite seal_eq;
   (progress simpl pre_evals);
   rewrite ?fold_pre_eval, ?fold_pre_evals)
  || idtac "Unable to simplify application of evals".

Ltac simpl_evalfs :=
  (unfold evalfs;
   rewrite seal_eq;
   (progress simpl pre_evalfs))
  || fail "Unable to simplify application of evalfs".

Ltac simpl_shallow_eval_branches :=
  (unfold shallow_eval_branches;
   rewrite seal_eq;
   (progress simpl pre_shallow_eval_branches);
  rewrite ?fold_pre_shallow_eval_branches)
  || fail "Unable to simplify application of shallow_eval_branches".

Ltac simpl_eval_branches :=
  (unfold eval_branches;
   rewrite seal_eq;
   (progress simpl pre_eval_branches);
   rewrite ?fold_pre_eval_branches)
  || fail "Unable to simplify application of eval_branches".

Ltac simpl_wrap_eval_branches :=
  (unfold wrap_eval_branches;
   rewrite seal_eq;
   (progress unfold pre_wrap_eval_branches; simpl);
   rewrite ?fold_pre_wrap_eval_branches)
  || fail "Unable to simplify application of wrap_eval_branches".

Ltac simpl_eval_bindings :=
  (unfold eval_bindings;
   rewrite seal_eq;
   (progress simpl pre_eval_bindings);
   rewrite ?fold_pre_eval_bindings;
   fold eval)
  || fail "Unable to simplify application of eval_bindings".

Ltac simpl_eval_sitem :=
  (unfold eval_sitem;
   rewrite seal_eq;
   (progress simpl pre_eval_sitem);
   rewrite ?fold_pre_eval_sitem;
  fold eval_bindings)
  || fail "Unable to simplify application of eval_sitem".

Ltac simpl_eval_sitems :=
  (unfold eval_sitems;
   rewrite seal_eq;
   (progress simpl pre_eval_sitems);
   rewrite ?fold_pre_eval_sitem, ?fold_pre_eval_sitems;
  fold eval_bindings)
  || fail "Unable to simplify application of eval_sitems".

Ltac simpl_eval_mexpr :=
  (unfold eval_mexpr;
   rewrite seal_eq;
   (progress simpl pre_eval_mexpr);
   (rewrite ?fold_pre_eval_mexpr,
     ?fold_pre_eval_sitems,
     ?fold_pre_eval_sitem);
  fold eval_bindings)
  || fail "Unable to simplify application of eval_mexpr".

Ltac simpl_eval_pats :=
  (unfold eval_pats;
   rewrite seal_eq;
   (progress simpl pre_eval_pats);
   rewrite ?fold_pre_eval_pats)
  || fail "Unable to simplify application of eval_pats".

Ltac simpl_eval_pat :=
  (unfold eval_pat;
   rewrite seal_eq;
   (progress simpl pre_eval_pat);
   rewrite ?fold_pre_eval_pat, ?fold_pre_eval_pats)
  || fail "Unable to simplify application of eval_pat".

Ltac unfold_all :=
  unfold eval, evals, evalfs,
    eval_branches, shallow_eval_branches,
    eval_bindings, eval_sitem, eval_sitems, eval_mexpr,
    eval_pats, eval_pat;
  rewrite ?seal_eq.

Ltac fold_all :=
  repeat first [ rewrite fold_pre_eval
               | rewrite fold_pre_evals
               | rewrite fold_pre_evalfs
               | rewrite fold_pre_eval_branches
               | rewrite fold_pre_wrap_eval_branches
               | rewrite fold_pre_shallow_eval_branches
               | rewrite fold_pre_eval_bindings
               | rewrite fold_pre_eval_mexpr
               | rewrite fold_pre_eval_sitem
               | rewrite fold_pre_eval_sitems
               | rewrite fold_pre_eval_pat
               | rewrite fold_pre_eval_pats
    ].

(* -------------------------------------------------------------------------- *)
(* Auxiliary functions on [eval] *)

Definition eval_anonfun η fn := eval η (EAnonFun fn).

(* [call_anonfun η fn args] calls the anonymous function expression [fn] with
  a list of arguments [args] in environment [η]. *)

(* N-ary application on function calls *)
Fixpoint nary_call (arg : list val) (acc : microvx) : microvx :=
  match arg with
    | nil => acc
    | x :: tl => nary_call tl (bind acc (fun v => call v x))
  end.

Definition call_anonfun η fn args := nary_call args (eval_anonfun η fn).

Definition ncall fn args := match args with
                            | [] => ret fn
                            | x :: args => nary_call args (call fn x)
                            end.

(* -------------------------------------------------------------------------- *)
(* [loop η x i1 i2 e] executes the loop [for x = i1 to i2 do e done]
   in the environment [η]. *)

Definition loop η x i1 i2 e : microvx :=
  if int.eq i1 i2 then
    (* If [i1 = i2], then we execute the body once.

       We need to add this test for the case where
       [i1 = i2 = max_int], and we cannot rely on testing that
       [i1 + 1 < i2] on the next iteration. *)
    let η' := (x, (VInt i1)) :: η in
    _v ← eval η' e ;
    ok
  else if int.lt i2 i1 then
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

End EvalF.

Module E := EvalF(LiberalStrategy).
Export E.
