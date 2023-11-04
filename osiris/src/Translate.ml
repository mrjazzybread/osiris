open Printf

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

let rec show_longident = function
  | Lident x ->
      x
  | Ldot (i, x) ->
      sprintf "%s.%s" (show_longident i) x
  | Lapply (i1, i2) ->
      sprintf "%s(%s)" (show_longident i1) (show_longident i2)

let rec show_path = function
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
         a *value* are not permitted by OCaml. *)
      fail "Error: functor application inside a path: %s\n" (show_longident i)

(* Long identifiers are unqualified (turned into short identifiers) when
   they designate data constructors or record fields. *)

let unqualify : Longident.t -> data =
  Longident.last

(* -------------------------------------------------------------------------- *)

(* Constants. *)

(* We may wish to check that integer constants are definitely representable
   (i.e., fit in 31 bits). Otherwise, the code would be non-portable and
   non-verifiable. TODO *)

let translate_exp_constant loc = function
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

let translate_pat_constant loc = function
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

(* Patterns. *)

let rec translate_pattern (pat: Typedtree.pattern) : pat =
  let loc = pat.pat_loc in
  match pat.pat_desc with

  | Tpat_any ->
      PAny

  | Tpat_var (_, x) ->
      PVar (txt x)

  | Tpat_alias (pat, _, x) ->
      PAlias (translate_pattern pat, txt x)

  | Tpat_constant c ->
      translate_pat_constant loc c

  | Tpat_tuple pats ->
      PTuple (translate_patterns pats)

  | Tpat_construct (i, _constructor_desc, pats, _optional_type_annotation) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
      let data = unqualify (txt i) in
     PData (data, PTuple (translate_patterns pats))

  | Tpat_variant _ ->
      punsupported loc "polymorphic variant pattern"

  | Tpat_record (fields, _closed_flag) ->
      PRecord (translate_field_patterns fields)

  | Tpat_array _ ->
      punsupported loc "array pattern"

  | Tpat_lazy _ ->
      punsupported loc "lazy pattern"

  | Tpat_or (pat1, pat2, _) ->
      POr (translate_pattern pat1, translate_pattern pat2)

and translate_patterns pats : pats =
  List.map translate_pattern pats

and translate_field_patterns fields : fpats =
  List.map translate_field_pattern fields

and translate_field_pattern (i, _label_desc, pat) : field * pat =
  unqualify (txt i),
  translate_pattern pat

(* Computation patterns distinguish normal termination and exceptions. *)

let translate_computation_pattern pat : pat =
  let loc = pat.pat_loc in
  match split_pattern pat with
  | Some pat, None ->
      (* A normal termination pattern. *)
      translate_pattern pat
  | None, Some _ ->
      (* An exception pattern. *)
      punsupported loc "exception pattern"
  | _ ->
      assert false

(* -------------------------------------------------------------------------- *)

let anonfun_of_expr : expr -> anonfun = function
  | EAnonFun a ->
      a
  | _ -> assert false

let unvarpat (p : value general_pattern) : string =
  match p.pat_desc with
  | Tpat_var (_, v) -> txt v
  | _ -> assert false

(* -------------------------------------------------------------------------- *)

let translate_record
      (fields: (Types.label_description * record_label_definition) array)
      (representation : Types.record_representation)
      (extended_expression : expression option)
      trans_expr : expr =
  match extended_expression, representation with
  | None, Record_regular ->
     (* This explicitly defines the whole record in the expected way. *)
     begin
       let body =
         (* Each element of the array defines a new field of the record. *)
         Array.fold_right
           (fun (elt, e) expr ->
             match e with
             | Kept _ -> assert false
             | Overridden (_, e) ->
                let name : string = elt.lbl_name in
                let body : expr = trans_expr e in
                (name, body) :: expr)
           fields []
       in
       ERecord (body)
     end
  | Some e, Record_regular ->
     (* This defines a modification to an existing record *)
     begin
       let body =
         (* Each element of the array defines a new field of the record. *)
         Array.fold_right
           (fun (_elt, e) expr ->
             match e with
             | Kept _ -> expr
             | Overridden (li, e) ->
                let name : string = unqualify (txt li) in
                let body : expr = trans_expr e in
                (name, body) :: expr)
           fields []
       in
       ERecordUpdate (trans_expr e, body)
     end
  | _, r ->
     (match r with
      | Record_regular -> assert false
      | Record_float -> assert false
      | Record_unboxed _ -> assert false
      | Record_inlined _ ->
         (* Inlined records are not supported yet. *)
         EString "TODO: inlined record are not supported yet."
      | Record_extension _ -> assert false)

(* -------------------------------------------------------------------------- *)

let rec translate_case (case : value case) : branch =
  let pat = case.c_lhs
  and e = case.c_rhs in
  Branch (
    translate_pattern pat,
    match case.c_guard with
    | None ->
        translate_expression e
    | Some guard ->
        let loc = guard.exp_loc in
        eunsupported loc "when clause"
  )

and translate_cases cases =
  List.map translate_case cases

and branches_of_computation_cases (cases : computation case list) : branches =
  List.fold_right
    (fun (case: computation case) (cases: branches) ->
      begin match case with
      | { c_lhs=pat; c_guard=None; c_rhs=e } ->
         Branch (translate_computation_pattern pat,
                 translate_expression e)
      | { c_lhs=pat; c_guard=Some guard; c_rhs=_e } ->
          let loc = guard.exp_loc in
         Branch (translate_computation_pattern pat,
                   eunsupported loc "when clause")
      end :: cases)
    cases []

(* -------------------------------------------------------------------------- *)

and translate_exp_ident path id : path =
  let id = txt id in
  (* [id] is the long identifier that appears in the source code.
     [path] is the corresponding resolved path. *)
  debug "    Texp_ident\n";
  debug "      id = %s\n" (show_longident id);
  debug "      path = %s\n" (show_path path);
  (* For the moment, we ignore [path] and keep [id]. However, [path]
     could be used to identify references to the OCaml standard library. *)
  translate_longident id

and translate_mod_ident path id : path =
  let id = txt id in
  (* [id] is the long identifier that appears in the source code.
     [path] is the corresponding resolved path. *)
  debug "    Tmod_ident\n";
  debug "      id = %s\n" (show_longident id);
  debug "      path = %s\n" (show_path path);
  (* For the moment, we ignore [path] and keep [id]. However, [path]
     could be used to identify references to the OCaml standard library. *)
  translate_longident id

and translate_expression (e: Typedtree.expression) =
  let loc = e.exp_loc in
  match e.exp_desc with
  | Texp_constant c -> translate_exp_constant loc c

  | Texp_function { arg_label = Nolabel; param; cases; partial } ->
      debug "Texp_function param = %s\n" (Ident.name param); (* TODO *)
      (* TODO recognize special case of [fun x -> e] *)
      ignore partial;
      EAnonFun (AnonFunction (translate_cases cases))

  | Texp_function { arg_label = Labelled _; _ } ->
      eunsupported loc "labeled argument"

  | Texp_function { arg_label = Optional _; _ } ->
      eunsupported loc "optional argument"

  | Texp_apply (f, el) ->
     List.fold_left
       (fun f a ->
         (* Labels are completely ignored here. *)
         match a with
         | _, None -> assert false
         | _, Some e ->
            let e = translate_expression e in
            EApp (f, e))
       (translate_expression f) el

  | Texp_assert e -> EAssert (translate_expression e)

  | Texp_ident (path, id, _) ->
      EPath (translate_exp_ident path id)

  | Texp_let (Nonrecursive, vbs, e) ->
     ELet (translate_bindings vbs, translate_expression e)

  | Texp_let (Recursive, vbs, e) ->
     ELetRec (translate_rec_bindings vbs, translate_expression e)

  | Texp_tuple el -> ETuple (List.map translate_expression el)

  | Texp_match (e, cases, _) ->
     EMatch (translate_expression e, branches_of_computation_cases cases)

  | Texp_sequence (e1, e2) ->
     ESeq (translate_expression e1,
           translate_expression e2)

  | Texp_ifthenelse (e1, e2, Some e3) ->
     EIfThenElse (translate_expression e1,
                  translate_expression e2,
                  translate_expression e3)

  | Texp_ifthenelse (e1, e2, None) ->
     EIfThen (translate_expression e1,
              translate_expression e2)
  | Texp_record { fields; representation; extended_expression } ->
     translate_record
       fields representation extended_expression
       translate_expression

  | Texp_construct (c, _, el) ->
     let name = unqualify (txt c) in
     let args =
       List.fold_right (fun e res -> translate_expression e :: res) el [] in
     EData (name, ETuple args)

  | Texp_field (e, _, label) ->
     ERecordAccess (translate_expression e,
                    label.lbl_name)

  | Texp_while (e, body) -> EWhile (translate_expression e,
                                    translate_expression body)

  | Texp_for (i, _, e1, e2, _, e3) ->
     EFor (Ident.name i,
           translate_expression e1,
           translate_expression e2,
           translate_expression e3)

  | Texp_try (_e, _cases) ->
      eunsupported loc "try/with"

  | Texp_array _ ->
      eunsupported loc "array expression"

  | Texp_variant (_, _) -> assert false
  | Texp_setfield (_, _, _, _) ->
     EString "Mutable records and arrays are not supported yet."


  | Texp_pack _ ->
     EString "TODO: Texp_pack."
  (* TODO. *)

  | Texp_letmodule (_, _, _, _, _) ->
     EString "TODO: ELetModule."
  | Texp_open (_, _) ->
     (* TODO. *)
     EString "TODO: local module open statement."

  | Texp_send (_, _) -> assert false
  | Texp_new (_, _, _) -> assert false
  | Texp_instvar (_, _, _) -> assert false
  | Texp_setinstvar (_, _, _, _) -> assert false
  | Texp_override (_, _) -> assert false
  | Texp_letexception (_, _) -> assert false
  | Texp_lazy _ -> assert false
  | Texp_object (_, _) -> assert false
  | Texp_letop _ -> assert false
  | Texp_unreachable -> assert false
  | Texp_extension_constructor (_, _) -> assert false

(* -------------------------------------------------------------------------- *)

and translate_binding (vb: Typedtree.value_binding): binding =
  let pattern = translate_pattern vb.vb_pat in
  let expression = translate_expression vb.vb_expr in
  Binding (pattern, expression)

and translate_bindings vbs =
  List.fold_right
    (fun vb (rv(*,rt*)) ->
      let (v(*, t*)) = translate_binding vb in
      v :: rv(*, t @ rt*))
    vbs ([](*, []*))

and translate_rec_binding (vb: Typedtree.value_binding) =
  let name = unvarpat vb.vb_pat in
  let expression = translate_expression vb.vb_expr in
  RecBinding (name, anonfun_of_expr expression)

and translate_rec_bindings vbs =
  List.fold_right
    (fun vb (rv(*,rt*)) ->
      let (v(*, t*)) = translate_rec_binding vb in
              v :: rv(*, t @ rt*))
    vbs ([](*, []*))

(* -------------------------------------------------------------------------- *)

let translate_structure_item
      translate_module
      (sitm: Typedtree.structure_item) : sitem option =
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
                 mb_expr = {mod_desc; _}; _} ->
     let m = translate_module mod_desc in
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
     let e = mb_expr.mod_desc in
     Some (IModule (name, translate_module e))

  | Tstr_include {incl_mod = {mod_desc;_}; _} ->
     (* of include_declaration *)
     Some (IInclude (translate_module mod_desc))

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

let rec translate_module (ast: module_expr_desc) : mexpr =
  match ast with
  | Tmod_ident (path, id) ->
      MPath (translate_mod_ident path id)

  | Tmod_structure ast -> (* of structure *)
     let (itms) =
       List.filter_map (translate_structure_item translate_module) ast.str_items
     in
     MStruct (itms)
  | Tmod_functor (_, _) -> MStruct [] (* TODO. *)
  | Tmod_apply (_, _, _) -> assert false
  | Tmod_constraint (_, _, _, _) -> MStruct [] (* TODO. *)
  | Tmod_unpack (_, _) -> assert false

(* -------------------------------------------------------------------------- *)

let typedtree m (ast: Typedtree.structure) : Syntax.def =
  { lhs = m ;
    rhs = OModule (translate_module (Tmod_structure ast)) }

(* TODO do something about && and || *)
