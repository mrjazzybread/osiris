open Syntax
open Typedtree
open Types

(* -------------------------------------------------------------------------- *)

let string_of_longident (i: Longident.t) : string =
  let rec last = function
    | [] -> assert false
    | h :: [] -> h
    | _ :: t -> last t
  in
  Longident.flatten i
  |> last

let translate_longident (i: Longident.t) : path =
  Longident.flatten i

(* -------------------------------------------------------------------------- *)

let rec translate_path : Path.t -> path = function
  | Pident i ->
     [Ident.name i]
  | Pdot (path, i) ->
     translate_path path @ [i]
  | _ -> assert false

(* -------------------------------------------------------------------------- *)

let translate_constant = function
  | Asttypes.Const_int i -> EInt i
  | Asttypes.Const_string (s, _, _) -> EString s

  (* Not yet translated: integers.
     Do we want several instantiations of the CompCert integers library, or
     should we simply define modules [Int32], [Int64] and [NativeInt] ? *)
  | Asttypes.Const_int32 i -> EInt (Int32.to_int i) (* TODO? *)
  | Asttypes.Const_int64 i -> EInt (Int64.to_int i) (* TODO? *)
  | Asttypes.Const_nativeint i -> EInt (Nativeint.to_int i) (* TODO? *)

  (* Not yet supported by the semantics: *)
  | Asttypes.Const_char c -> EChar c

  (* It is necessary to translate floats.
     As they are not supported by the semantics (yet?), I simply keep their
     string representation.
     If floats are to be added t the semantics, this should convert the string
     into a proper float. *)
  | Asttypes.Const_float s -> EString s

(* -------------------------------------------------------------------------- *)

let translate_primitive (name: string) (v : var) : sitem option =
  Some (
      ILet (
          [
            Binding (PVar name, EPath ["Externals"; v])
          ]
        )
    )

(* -------------------------------------------------------------------------- *)

let anonfun_of_expr : expr -> anonfun = function
  | EAnonFun f -> f
  | _ -> assert false

let unvarpat (p : value general_pattern) : string =
  match p.pat_desc with
  | Tpat_var (_, v) -> v.txt
  | _ -> assert false

(* -------------------------------------------------------------------------- *)

  (* [tanslate_pattern pat] translate the [Typedtree] pattern [pat] into an
     Osiris one.
     The only interesting case if [Tpat_construct] in which some constructors
     are to be recognized as primitive. *)
let rec translate_pattern (pat: Typedtree.value Typedtree.general_pattern) : pat =
  match pat.pat_desc with
  | Tpat_any -> PAny
  | Tpat_var (v, _) -> PVar (Ident.name v)
  | Tpat_tuple pl -> PTuple (List.map translate_pattern pl)

  | Tpat_constant c ->
     begin match c with
      | Asttypes.Const_int i -> PInt i
      | Asttypes.Const_char c -> PChar c
      | Asttypes.Const_string (_s, _, _) ->
          assert false (* TODO unsupported *)
      | Asttypes.Const_float _f ->
          assert false (* TODO unsupported *)
      | Asttypes.Const_int32 _ -> assert false
      | Asttypes.Const_int64 _ -> assert false
      | Asttypes.Const_nativeint _ ->
         (* [Nativeint] is not currently supported. Once it is, should we
            rather translate this directly, or see it as
            [Tpat_or (Tpat_constant (int32 _), Tpat_constant (int64 _))] ? *)
         assert false
     end

  | Tpat_construct ({txt = i;_}, _, args, _) ->
     (* Careful: It is possible to overload [()], [true], ... Therefore, they
        should be treated as any other constructor. *)
     PData ( string_of_longident i,
             PTuple (List.map translate_pattern args))
  | Tpat_alias (pat, var, _) ->
      PAlias (translate_pattern pat, Ident.name var)
  | Tpat_or (p1, p2, _) ->
      POr ( translate_pattern p1,
            translate_pattern p2 )

  | Tpat_record (rl, _) ->
     PRecord (
         List.map
           (fun (i, _, pat) ->
             (*FIXME*)let i: Longident.t Location.loc = i in
             let field = string_of_longident i.txt in
             let pat = translate_pattern pat in
             (field, pat))
           rl
       )

  | Tpat_variant (_, _, _) -> assert false
  | Tpat_array _ -> assert false
  | Tpat_lazy _ -> assert false


let translate_computation_pattern p =
  match split_pattern p with
  | Some p, None -> translate_pattern p
  | None, Some p ->
     (* TODO?  The pattern [p] is an exception pattern.  For now, I treat it as
        any pattern. *)
     translate_pattern p
  | _ ->
     (* It should not be allowed to match on both expressions and exceptions. *)
     assert false

(* -------------------------------------------------------------------------- *)

let translate_branch translate_expression (p, e) =
  Branch (translate_pattern p, translate_expression e)

let translate_branches translate_expression branches =
  List.map (translate_branch translate_expression) branches

(* -------------------------------------------------------------------------- *)

let translate_lambda translate_expression branches =
  AnonFun ("__osiris_anonymous_arg",
           EMatch
             (EPath ["__osiris_anonymous_arg"],
              (translate_branches translate_expression) branches))

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
                let name : string = string_of_longident li.txt in
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

let list_of_cases cases =
  List.fold_right
    (fun {c_lhs;c_rhs;_} res ->
      (c_lhs, c_rhs) :: res)
    cases []

let rec branches_of_cases cases =
  List.fold_right
    (fun (case: value case) (cases: branches) ->
      match case with
      | { c_lhs=pat; c_guard=None; c_rhs=e } ->
         Branch (translate_pattern pat,
                 translate_expression e)
         :: cases
      | _ -> cases (* TODO. *))
    cases []

and branches_of_computation_cases (cases : computation case list) : branches =
  List.fold_right
    (fun (case: computation case) (cases: branches) ->
      begin match case with
      | { c_lhs=pat; c_guard=None; c_rhs=e } ->
         Branch (translate_computation_pattern pat,
                 translate_expression e)
      | { c_lhs=pat; c_guard=Some cond; c_rhs=e } ->
         BranchWhen (translate_computation_pattern pat,
                   translate_expression cond,
                   translate_expression e)
      end :: cases)
    cases []

(* -------------------------------------------------------------------------- *)

and translate_expression (e: Typedtree.expression) =
  match e.exp_desc with
  | Texp_constant c -> translate_constant c

  | Texp_function {cases;_} ->
     let branches = list_of_cases cases in
     EAnonFun (translate_lambda translate_expression branches)

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

  | Texp_ident (_path, id, _) ->
     (* [_path] contains the fully-resolved path of the ident.
        => EPath (translate_path path) could be used to represent such a path.
        [id] contains the local path of the ident (the one that appears in the
        source code). *)
     EPath (translate_longident id.txt)

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
     let name = string_of_longident c.txt in
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

  | Texp_try (e, cases) ->
     ETry (translate_expression e, branches_of_cases cases)

  | Texp_array el ->
     EArray (List.map translate_expression el)

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

and translate_binding (vb: Typedtree.value_binding): binding (* * types*) =
  let pattern = translate_pattern vb.vb_pat in
  let expression(*, types*) = translate_expression vb.vb_expr in
  Binding (pattern, expression)(*, types*)

and translate_bindings vbs =
  List.fold_right
    (fun vb (rv(*,rt*)) ->
      let (v(*, t*)) = translate_binding vb in
      v :: rv(*, t @ rt*))
    vbs ([](*, []*))

and translate_rec_binding (vb: Typedtree.value_binding) (* * types*) =
  let name = unvarpat vb.vb_pat in
  let expression(* , types*) = translate_expression vb.vb_expr in
  RecBinding (name, anonfun_of_expr expression)(*, types*)

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
  | Tstr_type _ (* of Asttypes.rec_flag * type_declaration list *)
  | Tstr_modtype _ (* of module_type_declaration *)
  | Tstr_class_type _
  (* of (Ident.t * string Location.loc * class_type_declaration) list *)
  | Tstr_attribute _ (*of attribute*)
    -> None

  (* TODO: update me once the semantics has become exception-aware. *)
  | Tstr_exception {tyexn_constructor = {ext_id; _}; _} ->
     (* of type_exception *)
     Some (ILet [Binding (PVar (Ident.name ext_id), ERef EUnit)])

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
     | Tmod_ident (p, _) -> Some (IOpen (translate_path p))
     | _ -> assert false)

  | Tstr_primitive {val_id; val_prim = v :: _; _} -> (* of value_description *)
     (* Primitives are [external] statements.
        They are dealt with in [translate_primitive]. *)
     translate_primitive (Ident.name val_id) v

  |  Tstr_primitive _ -> assert false

  | Tstr_eval _ -> assert false (* of expression * attributes *)
  | Tstr_typext _ -> assert false (* of type_extension *)
  | Tstr_recmodule _ -> assert false (* of module_binding list *)
  | Tstr_class _ -> assert false (* of (class_declaration * string list) list *)

(* -------------------------------------------------------------------------- *)

let rec translate_module (ast: module_expr_desc) : mexpr (* * types*) =
  match ast with
  | Tmod_ident (p, _) ->
     MPath (translate_path p)
  | Tmod_structure ast -> (* of structure *)
     let (itms(*, types*)) =
       List.filter_map (translate_structure_item translate_module) ast.str_items
     (*    |> List.split *) in
     MStruct (itms)(*, List.flatten types*)
  | Tmod_functor (_, _) -> MStruct [] (* TODO. *)
  | Tmod_apply (_, _, _) -> assert false
  | Tmod_constraint (_, _, _, _) -> MStruct [] (* TODO. *)
  | Tmod_unpack (_, _) -> assert false

(* -------------------------------------------------------------------------- *)

let of_typedtree m (ast: Typedtree.structure) : Syntax.ast =
  Some m,
  OModule (translate_module (Tmod_structure ast))
