open OsirisAst
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


(* -------------------------------------------------------------------------- *)

let translate_constant = function
  | Asttypes.Const_int i -> EInt i
  | Asttypes.Const_string (s, _, _) -> EString s

  (* Not yet translated: integers.
     Do we want several instantiations of the CompCert integers library, or
     should we simply define modules [Int32], [Int64] and [NativeInt] ? *)
  | Asttypes.Const_int32 _ -> assert false
  | Asttypes.Const_int64 _ -> assert false
  | Asttypes.Const_nativeint _ -> assert false

  (* Not yet supported by the semantics: *)
  | Asttypes.Const_char _ -> assert false
  | Asttypes.Const_float _ -> assert false


(* -------------------------------------------------------------------------- *)

  (* [tanslate_pattern pat] translate the [Typedtree] pattern [pat] into an
     Osiris one.
     The only interesting case if [Tpat_construct], which needs to
 *)
let rec translate_pattern (pat: Typedtree.value Typedtree.general_pattern) : pat =
  match pat.pat_desc with
  | Tpat_any -> PAny
  | Tpat_var (v, _) -> PVar (Ident.name v)
  | Tpat_tuple pl -> PTuple (List.map translate_pattern pl)
  | Tpat_constant (Const_int i) -> PInt i
  | Tpat_construct ({txt = i;_}, _, args, _) ->
      if Longident.flatten i = ["()"]
      then PUnit
      else if Longident.flatten i = ["true"]
      then PData ("true", PTuple [])
      else if Longident.flatten i = ["false"]
      then PData ("false", PTuple [])
      else
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

  (* Only interger constants are supported for now. *)
  | Tpat_constant _ -> assert false

  | Tpat_variant (_, _, _) -> assert false
  | Tpat_array _ -> assert false
  | Tpat_lazy _ -> assert false


(* -------------------------------------------------------------------------- *)

let translate_branch translate_expression (p, e) =
  Branch (translate_pattern p, translate_expression e)

let translate_branches translate_expression branches =
  List.map (translate_branch
              translate_expression)
    branches

(* -------------------------------------------------------------------------- *)

let translate_lambda translate_expression branches =
  AnonFun ("__osiris_anonymous_arg",
           EMatch
             (EPath (PathBase "__osiris_anonymous_arg"),
              (translate_branches translate_expression) branches))

(* -------------------------------------------------------------------------- *)

let rec translate_path : Path.t -> path = function
  | Pident i ->
     PathBase (Ident.name i)
  | Pdot (path, i) ->
     PathDot (translate_path path, i)
  | _ -> assert false

let translate_computation_pattern p =
  match split_pattern p with
  | Some p, None -> translate_pattern p
  | _ -> assert false



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
  | _ -> assert false


(* -------------------------------------------------------------------------- *)

let rec translate_expression (e: Typedtree.expression) =
  match e.exp_desc with
  | Texp_constant c -> translate_constant c

  | Texp_function {cases;_} ->
     let branches =
       List.fold_right
         (fun {c_lhs;c_rhs;_} res ->
           (c_lhs, c_rhs) :: res)
         cases []
     in
     EAnonFun (translate_lambda translate_expression branches)

  | Texp_apply (f, el) ->
     List.fold_left
       (fun f a ->
         match a with
         | _, None -> f
         | _, Some e ->
            let e = translate_expression e in
            EApp (f, e))
       (translate_expression f) el

  | Texp_assert e -> EAssert (translate_expression e)

  | Texp_ident (path, _, _) ->
      EPath (translate_path path)

  | Texp_let (Nonrecursive, vbs, e) ->
     ELet (translate_bindings vbs, translate_expression e)

  | Texp_tuple el -> ETuple (List.map translate_expression el)

  | Texp_match (e, cl, _) ->
     (* [e]  : expression
        [cl] : computation case list *)
     let cases =
       List.fold_right
         (fun (case: computation case) (cases: branches) ->
           match case with
           | { c_lhs=pat; c_guard=None; c_rhs=e } ->
              Branch (translate_computation_pattern pat,
                      translate_expression e)
              :: cases
           | _ -> assert false)
         cl [] in
     EMatch (translate_expression e, cases)

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
     (* Some OCaml constructors directly have counterpart in the syntax, as :
        - Unit: ["()"]
      *)
     let name = string_of_longident c.txt in
     if name = "()" && el = []
     then EUnit
     else if name = "true" && el = []
     then EConstant "true"
     else if name = "false" && el = []
     then EConstant "false"
     else
       begin
         let args =
           List.fold_right
             (fun e res ->
               translate_expression e :: res)
             el []
         in
         EData (name,
                ETuple args)
       end

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

  | Texp_try (_, _) -> assert false
  | Texp_variant (_, _) -> assert false
  | Texp_setfield (_, _, _, _) -> assert false
  | Texp_array _ -> assert false
  | Texp_send (_, _) -> assert false
  | Texp_new (_, _, _) -> assert false
  | Texp_instvar (_, _, _) -> assert false
  | Texp_setinstvar (_, _, _, _) -> assert false
  | Texp_override (_, _) -> assert false
  | Texp_letmodule (_, _, _, _, _) -> assert false
  | Texp_letexception (_, _) -> assert false
  | Texp_lazy _ -> assert false
  | Texp_object (_, _) -> assert false
  | Texp_pack _ -> assert false
  | Texp_letop _ -> assert false
  | Texp_unreachable -> assert false
  | Texp_extension_constructor (_, _) -> assert false
  | Texp_open (_, _) -> assert false
  | _ -> assert false

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



(* -------------------------------------------------------------------------- *)

let anonfun_of_expr : expr -> anonfun = function
  | EAnonFun f -> f
  | _ -> assert false

let unvarpat (p : value general_pattern) : string =
  match p.pat_desc with
  | Tpat_var (_, v) -> v.txt
  | _ -> assert false

let translate_rec_binding (vb: Typedtree.value_binding): rec_binding (* * types*) =
  let name = unvarpat vb.vb_pat in
  let expression(* , types*) = translate_expression vb.vb_expr in
  RecBinding (name, anonfun_of_expr expression)(*, types*)

let translate_rec_bindings vbs =
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
                 mb_expr = {mod_desc = Tmod_structure module_structure ;
                            _}; _} ->
     let m = translate_module module_structure in
     Some (IModule (Ident.name mb_id, m))

  (*| Tstr_exception {tyexn_constructor = {ext_id; _}; _} -> (* of type_exception *)
     Some (
         EPlain ("(ILet (Binding1 (PVar \""^(Ident.name ext_id)^"\")\
                                (ERef EUnit)))")) *)

  (* Ignoring the type-related definitions. *)
  | Tstr_type _ (* of Asttypes.rec_flag * type_declaration list *)
  | Tstr_modtype _ (* of module_type_declaration *)
  | Tstr_class_type _ (* of (Ident.t * string Location.loc * class_type_declaration) list *)
  | Tstr_attribute _ (*of attribute*)
    -> None

  | Tstr_module _ -> assert false (* of module_binding *)
  | Tstr_eval _ -> assert false (* of expression * attributes *)
  | Tstr_primitive _ -> assert false (* of value_description *)
  | Tstr_typext _ -> assert false (* of type_extension *)
  | Tstr_recmodule _ -> assert false (* of module_binding list *)
  | Tstr_open _ -> assert false (* of open_declaration *)
  | Tstr_class _ -> assert false (* of (class_declaration * string list) list *)
  | Tstr_include _ -> assert false (* of include_declaration *)
  | _ -> assert false


(* -------------------------------------------------------------------------- *)

let rec map_option f l =
  match l with
  | [] -> []
  | h :: t ->
     match f h with
     | Some r -> r :: map_option f t
     | None -> map_option f t

let rec translate_module (ast: Typedtree.structure) : mexpr (* * types*) =
  let (itms(*, types*)) =
    map_option (translate_structure_item translate_module) ast.str_items
  (*    |> List.split *) in
  MStruct (itms)(*, List.flatten types*)

(* -------------------------------------------------------------------------- *)

let of_typedtree (verbose_msg: (string -> unit))
                 (_debug_msg: (string -> unit))
                 (ast: Typedtree.structure) =
  let () = verbose_msg "Translation « Typed-tree => Osiris »: begin." in
  OModule (translate_module ast)
