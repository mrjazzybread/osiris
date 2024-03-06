open Printf
let map = List.map

(* ocaml-compiler-libs: *)
open Longident
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/longident.mli *)
open Asttypes
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/asttypes.mli *)
open Primitive
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/primitive.mli *)
open Types
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/types.ml *)
open Path
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/path.mli *)
open Typedtree
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/typedtree.ml *)

(* Osiris: *)
open Fail
open Settings
open Syntax

(* -------------------------------------------------------------------------- *)

(* Printers (for debugging only). *)

let rec show_longident (i : Longident.t) =
  match i with
  | Lident x ->
      x
  | Ldot (i, x) ->
      sprintf "%s.%s" (show_longident i) x
  | Lapply (i1, i2) ->
      sprintf "%s(%s)" (show_longident i1) (show_longident i2)

let rec show_path (p : Path.t) =
  match p with
  | Pident i ->
      Ident.name i
  | Pdot (p, x) ->
      sprintf "%s.%s" (show_path p) x
  | Papply (p1, p2) ->
      sprintf "%s(%s)" (show_path p1) (show_path p2)
  | Pextra_ty (p1, p2) ->
      match p2 with
      | Pcstr_ty x ->
	  sprintf "%s{%s}" x (show_path p1)
      | Pext_ty ->
	  sprintf "+=%s" (show_path p1)

(* -------------------------------------------------------------------------- *)

(* Warnings. *)

let prerr_loc (loc : Location.t) =
  Location.print_loc Format.err_formatter loc;
  Format.pp_print_flush Format.err_formatter ()

let unsupported loc construct v =
  if warnings then begin
    prerr_loc loc;
    eprintf ":\n";
    eprintf "Warning: unsupported construct (%s).\n" construct;
    flush stderr
  end;
  v

let eunsupported loc construct : expr =
  unsupported loc construct EUnsupported

let punsupported loc construct : pat =
  unsupported loc construct PUnsupported

let ounsupported loc construct : _ option =
  unsupported loc construct None

let munsupported loc construct : mexpr =
  unsupported loc construct MUnsupported

exception Unsupported

(* -------------------------------------------------------------------------- *)

(* Auxiliary exceptions and functions. *)

exception NotExactKnownPrimitive

let is_Stdlib path =
  match path with
  | Pident m when Ident.name m = "Stdlib" ->
      true
  | _ ->
      false

let is_Obj path =
  match path with
  | Pdot (parent, "Obj") when is_Stdlib parent ->
      true
  | _ ->
      false

(* -------------------------------------------------------------------------- *)

(* If the source file is available, then we insert decorations into the
   generated AST. *)

module Run (X : sig val source : string option end) = struct

(* A source code location (a pair of positions) is converted to a string.
   This can fail if [source] is [None], which means that [--decorate] is
   off or that the soure file could not be found. It can also fail if
   [extract] fails, which can happen if the source code positions are
   out of range. *)

(* [2k+3] is the maximum length of a snippet. *)

let k =
  15

let return =
  Option.some

let (let*) =
  Option.bind

let convert (loc : Location.t) : string option =
  let* source = X.source in
  let startp, endp = Location.(loc.loc_start, loc.loc_end) in
  let* snippet = ErrorReports.(extract source (startp, endp)) in
  return ErrorReports.(snippet |> sanitize |> compress |> shorten k)

(* Decorating an expression with a location. *)

let decorate (loc : Location.t) (e : expr) : expr =
  match convert loc with
  | Some snippet ->
      EDecorate (snippet, e)
  | None ->
      (* If we are unable to produce a decoration, forget about it. *)
      e

(* -------------------------------------------------------------------------- *)

(* Stripping off a location. *)

let txt (x : 'a loc) : 'a =
  x.txt

(* -------------------------------------------------------------------------- *)

(* Long identifiers are preserved when they designate a value or module. *)

let rec translate_longident (i : Longident.t) : path =
  match i with
  | Lident x ->
      [x]
  | Ldot (i, x) ->
      translate_longident i @ [x]
  | Lapply _ ->
      (* I believe that a functor application inside a path that designates
         a *value* or *module* are not permitted by OCaml. It is permitted
         inside a path that designates a *type* or *module type*. *)
      fail "Error: functor application inside a path: %s\n" (show_longident i)

let debug_ident kind path id =
  (* [id] is the long identifier that appears in the source code.
     [path] is the corresponding resolved path. *)
  debug "    %s\n" kind;
  debug "      id = %s\n" (show_longident id);
  debug "      path = %s\n" (show_path path)

let translate_exp_ident path id : path =
  let id = txt id in
  debug_ident "Texp_ident" path id;
  (* For the moment, we ignore [path] and keep [id]. However, [path]
     could be used to identify references to the OCaml standard library. *)
  translate_longident id

let translate_mod_ident path id : path =
  let id = txt id in
  debug_ident "Tmod_ident" path id;
  translate_longident id

(* Long identifiers are unqualified (turned into short identifiers) when
   they designate data constructors or record fields. *)

let translate_data_constructor id constructor_desc : data =
  (* [id] is the record field that appears in the source code, possibly
     a long identifier. *)
  (* [constructor_desc] is the constructor description constructed by
     the OCaml type-checker. *)
  assert (Longident.last (txt id) = constructor_desc.cstr_name);
  constructor_desc.cstr_name

let translate_record_field id label_desc : field =
  (* [id] is the record field that appears in the source code, possibly
     a long identifier. *)
  (* [label_desc] is the field description constructed by the OCaml
     type-checker. *)
  assert (Longident.last (txt id) = label_desc.lbl_name);
  label_desc.lbl_name

(* -------------------------------------------------------------------------- *)

(* Constants. *)

(* We may wish to check that integer constants are definitely representable
   (i.e., fit in 31 bits). Otherwise, the code would be non-portable and
   non-verifiable. TODO *)

let translate_exp_constant loc (c : constant) : expr =
  match c with
  | Const_int i ->
      EInt i
  | Const_char c ->
      EChar c
  | Const_string (s, _, _) ->
      EString s
  | Const_float f ->
      EFloat f
  | Const_int32 _ ->
      eunsupported loc "32-bit integer literal"
  | Const_int64 _ ->
      eunsupported loc "64-bit integer literal"
  | Const_nativeint _ ->
      eunsupported loc "native integer literal"

let translate_pat_constant loc (c : constant) : pat =
  match c with
  | Const_int i ->
      PInt i
  | Const_char c ->
      PChar c
  | Const_string (s, _, _) ->
      PString s
  | Const_float _ ->
      punsupported loc "floating-point literal"
  | Const_int32 _ ->
      punsupported loc "32-bit integer literal"
  | Const_int64 _ ->
      punsupported loc "64-bit integer literal"
  | Const_nativeint _ ->
      punsupported loc "native integer literal"

(* -------------------------------------------------------------------------- *)

(* Patterns, also known as value patterns. *)

(* The type [pattern] is a synonym for [value general_pattern]. *)

let rec translate_pat (pat: pattern) : pat =
  let loc = pat.pat_loc in
  match pat.pat_desc with

  | Tpat_any ->
      PAny

  | Tpat_var (_, x) ->
      PVar (txt x)

  | Tpat_alias (pat, _, x) ->
      PAlias (translate_pat pat, txt x)

  | Tpat_constant c ->
      translate_pat_constant loc c

  | Tpat_tuple pats ->
      PTuple (translate_pats pats)

  | Tpat_construct (id, constructor_desc, pats, _optional_type_annotation) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
      let data = translate_data_constructor id constructor_desc in
      PData (data, PTuple (translate_pats pats))

  | Tpat_variant _ ->
      punsupported loc "polymorphic variant pattern"

  | Tpat_record (fields, _closed_flag) ->
      PRecord (translate_field_patterns fields)

  | Tpat_array _ ->
      punsupported loc "array pattern"

  | Tpat_lazy _ ->
      punsupported loc "lazy pattern"

  | Tpat_or (pat1, pat2, _) ->
      POr (translate_pat pat1, translate_pat pat2)

and translate_pats pats : pats =
  map translate_pat pats

and translate_field_patterns fields : fpats =
  map translate_field_pattern fields

and translate_field_pattern (i, label_desc, pat) : field * pat =
  translate_record_field i label_desc,
  translate_pat pat

(* -------------------------------------------------------------------------- *)

(* Computation patterns distinguish normal termination and exceptions. *)

let translate_computation_pattern (pat : computation general_pattern) : pat =
  let loc = pat.pat_loc in
  match split_pattern pat with
  | Some pat, None ->
      (* A normal termination pattern. *)
      translate_pat pat
  | None, Some _ ->
      (* An exception pattern. *)
      punsupported loc "exception pattern"
  | _ ->
      assert false

(* -------------------------------------------------------------------------- *)

(* N-ary function applications are encoded in terms of nested binary function
   applications. *)

let apply e1 e2 =
  EApp (e1, e2)

let apply e1 e2s =
  List.fold_left apply e1 e2s

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec translate_expr (e: expression) : expr =
  let loc = e.exp_loc in
  decorate loc @@
  match e.exp_desc with

  | Texp_ident (path, id, _) ->
      EPath (translate_exp_ident path id)

  | Texp_constant c ->
      translate_exp_constant loc c

  | Texp_let (Nonrecursive, vbs, e) ->
      ELet (translate_bindings vbs, translate_expr e)

  | Texp_let (Recursive, vbs, e) ->
      begin try
        ELetRec (translate_rec_bindings vbs, translate_expr e)
      with Unsupported ->
        eunsupported loc "recursive definition of values"
      end

  | Texp_function { arg_label = Nolabel; param = _; cases; partial } ->
      (* [param] is apparently meaningless. *)
      translate_function cases partial

  | Texp_function { arg_label = Labelled _; _ } ->
      eunsupported loc "labeled argument"

  | Texp_function { arg_label = Optional _; _ } ->
      eunsupported loc "optional argument"

  | Texp_apply (e, args) ->
      translate_application loc e args

  | Texp_match (e, cases, _partial) ->
      EMatch (translate_expr e, translate_computation_cases cases)

  | Texp_try _ ->
      eunsupported loc "try/with"

  | Texp_tuple es ->
      ETuple (translate_exprs es)

  | Texp_construct (id, constructor_desc, es) ->
      let data = translate_data_constructor id constructor_desc in
      EData (data, ETuple (translate_exprs es))

  | Texp_variant _ ->
      eunsupported loc "polymorphic variant"

  | Texp_record { fields; representation = _; extended_expression = None } ->
      translate_record_construction fields

  | Texp_record { fields; representation = _; extended_expression = Some e } ->
      translate_record_update e fields

  | Texp_field (e, id, label_desc) ->
      let field = translate_record_field id label_desc in
      ERecordAccess (translate_expr e, field)

  | Texp_setfield (_e1, _id, _label_desc, _e2) ->
      eunsupported loc "mutable record"

  | Texp_array _ ->
      eunsupported loc "array expression"

  | Texp_ifthenelse (e1, e2, Some e3) ->
      EIfThenElse (translate_expr e1, translate_expr e2, translate_expr e3)

  | Texp_ifthenelse (e1, e2, None) ->
      EIfThen (translate_expr e1, translate_expr e2)

  | Texp_sequence (e1, e2) ->
      ESeq (translate_expr e1, translate_expr e2)

  | Texp_while (e, body) ->
      EWhile (translate_expr e, translate_expr body)

  | Texp_for (i, _, e1, e2, Upto, e3) ->
      let i = Ident.name i in
      EFor (i, translate_expr e1, translate_expr e2, translate_expr e3)

  | Texp_for (_i, _, _e1, _e2, Downto, _e3) ->
      eunsupported loc "downto"

  | Texp_send _
  | Texp_new _
  | Texp_instvar _
  | Texp_setinstvar _
  | Texp_override _ ->
      eunsupported loc "objects"

  | Texp_letmodule (Some id, _, _, me, e) ->
      let m = Ident.name id in
      ELetModule (m, translate_mod_expr me, translate_expr e)

  | Texp_assert
      { exp_desc = Texp_construct ({ txt = Lident "false"; _}, _, []); _ }
  | Texp_unreachable ->
      (* [assert false] and [.] are both translated to [EAssertFalse]. *)
      EAssertFalse

  | Texp_assert e ->
      EAssert (translate_expr e)

  | Texp_lazy _ ->
      eunsupported loc "lazy"

  | Texp_object _ ->
      eunsupported loc "objects"

  | Texp_pack _ ->
      eunsupported loc "first-class modules"

  | Texp_letop _ ->
      eunsupported loc "let operators"

  | Texp_extension_constructor _ ->
      eunsupported loc "extension constructors"

  | Texp_open ({ open_expr = me; _ }, e) ->
      ELetOpen (translate_mod_expr me, translate_expr e)

and translate_exprs es : exprs =
  map translate_expr es

(* -------------------------------------------------------------------------- *)

(* Expressions: function applications. *)

(* We first check whether this is an exact application of a known primitive
   operation. If so, it is given special treatment. Otherwise, it is viewed
   as a normal application. *)

(* Thus, an under- or over-application of a primitive operation, or an exact
   application of an unknown primitive operation, is naturally considered as a
   call to an external library function. No special treatment is required. *)

and translate_application loc e args =
  try
    translate_primitive_application loc e args
  with NotExactKnownPrimitive ->
    apply (translate_expr e) (translate_labeled_arguments loc args)

and translate_primitive_application loc e args =
  match e.exp_desc with
  | Texp_ident (path, _, { val_kind = Val_prim p; _ })
    when List.length args = p.prim_arity ->
      (* This is an exact application of a primitive operation. *)
      translate_exact_primitive_application loc path p args
  | _ ->
      (* This is either not a primitive operation,
         or not an exact application. *)
      raise NotExactKnownPrimitive

(* -------------------------------------------------------------------------- *)

(* Expressions: exact applications of primitive operations. *)

(* An exact application of a primitive operation is recognized as such. *)

(* In the case of Boolean conjunction (&&) and disjunction (||), this is
   crucial in order to obtain the correct (short-circuit) semantics. *)

(* This is otherwise not crucial for soundness, but this should help us by
   allowing us to produce simpler code. *)

(* Some primitive operations are intentionally not recognized as such. They
   are treated as standard library functions. These include %ignore, %incr,
   %decr, %field0 (fst), %field1 (snd). *)

(* Some primitive operations have multiple distinct meanings. For instance,
   [%identity] can represent [Obj.magic], [Char.code], or unary integer [+].
   As another example, [%field0] can represents [fst] on pairs or [!] on
   references. We must distinguish between these meanings. To do so, we use
   both the OCaml identifier and the primitive operation. This is not 100%
   bulletproof. *)

and translate_exact_primitive_application loc path p args =
  assert (List.length args = p.prim_arity);
  match path, p.prim_name, translate_labeled_arguments loc args with

  (* Erasing applications of [Obj.magic] is an experimental feature. It takes
     careful consideration and arguments to ascertain that this is sound. *)
  | Pdot (parent, "magic"), "%identity", [e]
    when is_Obj parent ->
      e

  (* Integers. *)

  | _, "%negint", [e] ->
      EIntNeg e
  | _, "%addint", [e1; e2] ->
      EIntAdd (e1, e2)
  | _, "%subint", [e1; e2] ->
      EIntSub (e1, e2)
  | _, "%mulint", [e1; e2] ->
      EIntMul (e1, e2)
  | _, "%divint", [e1; e2] ->
      EIntDiv (e1, e2)
  | _, "%modint", [e1; e2] ->
      EIntMod (e1, e2)
  | _, "%predint", [e] ->
      EIntSub (e, EInt 1)
  | _, "%succint", [e] ->
      EIntAdd (e, EInt 1)

  (* Structural equality and comparison. *)

  | _, "%equal", [e1; e2] ->
      EOpEq (e1, e2)
  | _, "%notequal", [e1; e2] ->
      EOpNe (e1, e2)
  | _, "%lessthan", [e1; e2] ->
      EOpLt (e1, e2)
  | _, "%greaterthan", [e1; e2] ->
      EOpGt (e1, e2)
  | _, "%lessequal", [e1; e2] ->
      EOpLe (e1, e2)
  | _, "%greaterequal", [e1; e2] ->
      EOpGe (e1, e2)

  (* Physical equality. *)

  | _, "%eq", [e1; e2] ->
      EOpPhysEq (e1, e2)
  | _, "%noteq", [e1; e2] ->
      EBoolNeg (EOpPhysEq (e1, e2))

  (* Booleans. *)

  | _, "%boolnot", [e] ->
      EBoolNeg e
  | _, "%sequand", [e1; e2] ->
      EBoolConj (e1, e2)
  | _, "%sequor", [e1; e2] ->
      EBoolDisj (e1, e2)

  (* Functions. *)

  | _, "%apply", [e1; e2] ->
      (* We assume that [e1] is not itself a primitive operation. *)
      apply e1 [e2]
  | _, "%revapply", [e1; e2] ->
      (* We assume that [e2] is not itself a primitive operation. *)
      apply e2 [e1]

  (* References. *)

  | Pdot (parent, "ref"), "%makemutable", [e]
    when is_Stdlib parent ->
      ERef e
  | Pdot (parent, "!"), "%field0", [e]
    when is_Stdlib parent ->
      ELoad e
  | Pdot (parent, ":="), "%setfield0", [e1; e2]
    when is_Stdlib parent ->
      EStore (e1, e2)

  | _, _, _ ->
      raise NotExactKnownPrimitive

(* -------------------------------------------------------------------------- *)

(* Expressions: anonymous functions. *)

and translate_function cases partial : expr =
  match cases with
  | [{ c_lhs = { pat_desc = Tpat_var (_, x); _ };
       c_guard = None;
       c_rhs = e
     }] ->
      (* We recognize the special case of [fun x -> e]. In this case
         we can use [AnonFun], a primitive form in the Osiris AST. *)
      assert (partial = Total);
      EAnonFun (AnonFun (txt x, translate_expr e))
  | _ ->
      (* In the general case, this function has the form [function bs].
         Then we use [AnonFunction], a derived form in Osiris. *)
      EAnonFun (AnonFunction (translate_value_cases cases))

(* -------------------------------------------------------------------------- *)

(* Expressions: actual arguments in applications. *)

and translate_labeled_arguments loc args =
  map (translate_labeled_argument loc) args

and translate_labeled_argument loc arg : expr =
  match arg with
  | Nolabel, Some e ->
      (* An ordinary unlabeled argument. *)
      translate_expr e
  | _, _ ->
      (* A labeled argument, or an unlabeled argument that participates
         in a labeled function application. *)
      eunsupported loc "labeled arguments"

(* -------------------------------------------------------------------------- *)

(* Cases in [fun], [match], [try] constructs. *)

and translate_case : type k . (k general_pattern -> pat) -> k case -> branch =
  fun translate_pat case ->
  let pat = case.c_lhs
  and e = case.c_rhs in
  Branch (
    translate_pat pat,
    match case.c_guard with
    | None ->
        translate_expr e
    | Some guard ->
        let loc = guard.exp_loc in
        eunsupported loc "when clause"
  )

and translate_value_case (case : value case) : branch =
  translate_case translate_pat case

and translate_value_cases cases =
  map translate_value_case cases

and translate_computation_case (case : computation case) : branch =
  translate_case translate_computation_pattern case

and translate_computation_cases cases =
  map translate_computation_case cases

(* -------------------------------------------------------------------------- *)

(* Non-recursive bindings. *)

and translate_binding (vb : value_binding) : binding =
  Binding (translate_pat vb.vb_pat, translate_expr vb.vb_expr)

and translate_bindings vbs =
  map translate_binding vbs

(* -------------------------------------------------------------------------- *)

(* Recursive bindings. *)

(* In a recursive binding [p = e], the pattern [p] must be a variable,
   and the right-hand side [e] must be an anonymous function.
   OCaml enforces the first restriction.
   We impose the second restriction. *)

and project_EAnonFun (e : expr) : anonfun =
  match e with
  | EDecorate (_, e) ->
      project_EAnonFun e
  | EAnonFun a -> a
  | _ -> raise Unsupported

and project_Tpat_var (pat : value general_pattern) : var =
  match pat.pat_desc with
  | Tpat_var (_, v) -> txt v
  | _ -> assert false

and translate_rec_binding (vb : value_binding) : rec_binding =
  let x = project_Tpat_var vb.vb_pat
  and a = project_EAnonFun (translate_expr vb.vb_expr) in
  RecBinding (x, a)

and translate_rec_bindings vbs =
  map translate_rec_binding vbs

(* -------------------------------------------------------------------------- *)

(* Records. *)

and translate_record_construction fields : expr =
  ERecord (translate_record_field_defs fields)

and translate_record_update e fields : expr =
  ERecordUpdate (translate_expr e, translate_record_field_defs fields)

and translate_record_field_defs fields : fexprs =
  List.filter_map translate_record_field_def (Array.to_list fields)

and translate_record_field_def (label_desc, label_def) : fexpr option =
  match label_def with
  | Kept _ ->
      (* This field is omitted. This can occur only in a record update
          expression. *)
      None
  | Overridden (id, e) ->
      (* This field is defined. *)
      Some (
        Fexpr (
          translate_record_field id label_desc,
          translate_expr e)
      )

(* -------------------------------------------------------------------------- *)

(* Structure items. *)

and translate_structure_item (item : structure_item) : sitem option =
  let loc = item.str_loc in
  match item.str_desc with

  | Tstr_eval (e, _) ->
      (* An expression [e] at the toplevel is translated in the same way
         as the toplevel binding [let _ = e]. *)
      Some (ILet [Binding (PAny, translate_expr e)])

  | Tstr_value (Nonrecursive, vbs) ->
      Some (ILet (translate_bindings vbs))

  | Tstr_value (Recursive, vbs) ->
      begin try
        Some (ILetRec (translate_rec_bindings vbs))
      with Unsupported ->
        ounsupported loc "recursive definition of values"
      end

  | Tstr_primitive _ ->
      (* Declarations of external primitive operations are skipped. We do not
         expect ordinary programs to contain such declarations. The OCaml
         standard library does contain many such declarations; we give it
         special treatment. *)
     ounsupported loc "declaration of primitive operation"

  | Tstr_type _ ->
      (* A type definition is silently ignored. *)
      None

  | Tstr_typext _ ->
      ounsupported loc "extending an extensible algebraic data type"

  | Tstr_exception _ ->
      ounsupported loc "exception declaration"

  | Tstr_module { mb_id = Some id; mb_expr = me; _} ->
      let m = Ident.name id in
      Some (IModule (m, translate_mod_expr me))

  | Tstr_module { mb_id = None; _} ->
      ounsupported loc "module _"

  | Tstr_recmodule _ ->
      ounsupported loc "recursive module"

  | Tstr_modtype _ ->
      (* A module type definition is silently ignored. *)
      None

  | Tstr_open { open_expr = me; _ } ->
      Some (IOpen (translate_mod_expr me))

  | Tstr_class _ ->
      ounsupported loc "class definition"

  | Tstr_class_type _ ->
      (* A class type definition is silently ignored. *)
      None

  | Tstr_include { incl_mod = me; _ } ->
     Some (IInclude (translate_mod_expr me))

  | Tstr_attribute _ ->
      (* An attribute is silently ignored. *)
      None

and translate_structure_items items =
  List.filter_map translate_structure_item items

(* -------------------------------------------------------------------------- *)

(* Module expressions. *)

and translate_structure (str : structure) : mexpr =
  MStruct (translate_structure_items str.str_items)

and translate_mod_expr (me : module_expr) : mexpr =
  let loc = me.mod_loc in
  match me.mod_desc with

  | Tmod_ident (path, id) ->
      MPath (translate_mod_ident path id)

  | Tmod_structure str ->
      translate_structure str

  | Tmod_functor _ ->
      munsupported loc "functor"

  | Tmod_apply _ ->
      munsupported loc "functor application"

  | Tmod_apply_unit _ ->
      munsupported loc "functor unit application"

  | Tmod_constraint _ ->
      munsupported loc "signature ascription"

  | Tmod_unpack _ ->
      munsupported loc "first-class modules"

(* -------------------------------------------------------------------------- *)

end (* Run *)

(* The main function. *)

let unit source str =
  let open Run(struct let source = source end) in
  translate_structure str
