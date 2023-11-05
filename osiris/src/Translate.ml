open Printf
let map = List.map

(* ocaml-compiler-libs: *)
open Longident
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/longident.mli *)
open Asttypes
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/asttypes.mli *)
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

let eunsupported loc construct =
  unsupported loc construct EUnsupported

let punsupported loc construct =
  unsupported loc construct PUnsupported

exception Unsupported

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

let unqualify : Longident.t -> data =
  Longident.last

let translate_record_field id label_desc : field =
  (* [id] is the record field that appears in the source code, possibly
     a long identifier. *)
  (* [label_desc] is the field description constructed by the OCaml
     type-checker. *)
  assert (unqualify (txt id) = label_desc.lbl_name);
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
  | Const_float _ ->
      eunsupported loc "floating-point literal"
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

  | Tpat_construct (i, _constructor_desc, pats, _optional_type_annotation) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
      let data = unqualify (txt i) in
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
      apply (translate_expr e) (translate_labeled_arguments loc args)

  | Texp_match (e, cases, _partial) ->
      EMatch (translate_expr e, translate_computation_cases cases)

  | Texp_try _ ->
      eunsupported loc "try/with"

  | Texp_tuple es ->
      ETuple (translate_exprs es)

  | Texp_construct (c, _constructor_desc, es) ->
      let data = unqualify (txt c) in
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

  | Texp_letmodule (None, _, _, _, _) ->
      eunsupported loc "let module _"

  | Texp_letexception _ ->
      eunsupported loc "let exception"

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
      (* We support [open] followed with a path, not followed with an
         arbitrary module expression. *)
      begin try
        ELetOpen (translate_mod_path me, translate_expr e)
      with Unsupported ->
        eunsupported loc "open module expression"
      end

and translate_exprs es : exprs =
  map translate_expr es

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
  | EAnonFun a -> a
  | _ -> raise Unsupported

and project_Tpat_var (pat : value general_pattern) : var =
  match pat.pat_desc with
  | Tpat_var (_, v) -> txt v
  | _ -> assert false

and translate_rec_binding (vb : value_binding) : rec_binding =
  let x = project_Tpat_var vb.vb_pat
  and e = project_EAnonFun (translate_expr vb.vb_expr) in
  RecBinding (x, e)

and translate_rec_bindings vbs =
  map translate_rec_binding vbs

(* -------------------------------------------------------------------------- *)

and translate_record_construction
  (fields: (label_description * record_label_definition) array)
: expr =
       let body =
         (* Each element of the array defines a new field of the record. *)
         Array.fold_right
           (fun (label_desc, e) expr ->
             match e with
             | Kept _ -> assert false
             | Overridden (_, e) ->
                let name : string = label_desc.lbl_name in
                let body : expr = translate_expr e in
                (name, body) :: expr)
           fields []
       in
       ERecord (body)

and translate_record_update
  (e : expression)
  (fields: (label_description * record_label_definition) array)
: expr =
       let body =
         (* Each element of the array defines a new field of the record. *)
         Array.fold_right
           (fun (_elt, e) expr ->
             match e with
             | Kept _ -> expr
             | Overridden (li, e) ->
                let name : string = unqualify (txt li) in
                let body : expr = translate_expr e in
                (name, body) :: expr)
           fields []
       in
       ERecordUpdate (translate_expr e, body)

(* -------------------------------------------------------------------------- *)

and translate_structure_item
      (sitm: structure_item) : sitem option =
  match sitm.str_desc with
  (* Non-recursive top-level bindings. *)
  | Tstr_value (Nonrecursive, vbs) ->
     let (r(*, t*)) = translate_bindings vbs in
     Some (ILet r)
  (* Recursive top-level bindings. *)
  | Tstr_value (Recursive, vbs) ->
     let (r(*, t*)) = translate_rec_bindings vbs in
     Some (ILetRec r)

  | Tstr_module {mb_id = Some mb_id;
                 mb_expr = me; _} ->
     let m = translate_mod_expr me in
     Some (IModule (Ident.name mb_id, m))

  (* Ignoring the type-related definitions. *)
  | Tstr_type _ (* of rec_flag * type_declaration list *)
  | Tstr_modtype _ (* of module_type_declaration *)
  | Tstr_class_type _
  (* of (Ident.t * string Location.loc * class_type_declaration) list *)
  | Tstr_attribute _ (*of attribute*)
    -> None

  (* TODO: update me once the semantics has become exception-aware. *)
  | Tstr_exception _ ->
      None

  | Tstr_module {mb_id; mb_expr; _} -> (* of module_binding *)
     let name =
       match mb_id with
       | None -> Fresh.fresh_name "let_module"
       | Some name -> Ident.name name
     in
     Some (IModule (name, translate_mod_expr mb_expr))

  | Tstr_include {incl_mod = me; _} ->
     (* of include_declaration *)
     Some (IInclude (translate_mod_expr me))

  | Tstr_open {open_expr={mod_desc;_};_} -> (* of open_declaration *)
     (match mod_desc with
     | Tmod_ident (path, id) -> Some (IOpen (translate_mod_ident path id))
     | _ -> assert false)

  | Tstr_primitive _ ->
     (* Declarations of external primitive operations are skipped. We do not
        expect ordinary programs to contain such declarations. The OCaml
        standard library does contain many such declarations; we give it
        special treatment. *)
     None

  | Tstr_eval _ -> assert false (* of expression * attributes *)
  | Tstr_typext _ -> assert false (* of type_extension *)
  | Tstr_recmodule _ -> assert false (* of module_binding list *)
  | Tstr_class _ -> assert false (* of (class_declaration * string list) list *)

(* -------------------------------------------------------------------------- *)

and translate_mod_expr (me : module_expr) : mexpr =
  translate_module me.mod_desc

and translate_module (ast: module_expr_desc) : mexpr =
  match ast with
  | Tmod_ident (path, id) ->
      MPath (translate_mod_ident path id)

  | Tmod_structure ast -> (* of structure *)
     let (itms) =
       List.filter_map translate_structure_item ast.str_items
     in
     MStruct (itms)
  | Tmod_functor (_, _) -> MStruct [] (* TODO. *)
  | Tmod_apply (_, _, _) -> assert false
  | Tmod_constraint (_, _, _, _) -> MStruct [] (* TODO. *)
  | Tmod_unpack (_, _) -> assert false

and translate_mod_path (me : module_expr) : path =
  match me.mod_desc with
  | Tmod_ident (path, id) ->
      translate_mod_ident path id
  | _ ->
      raise Unsupported

(* -------------------------------------------------------------------------- *)

let typedtree m (ast: structure) : def =
  { lhs = m ;
    rhs = OModule (translate_module (Tmod_structure ast)) }

(* TODO do something about && and || *)
