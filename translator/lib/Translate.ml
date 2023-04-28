open Ast
open Typedtree

let rec string_of_path : Path.t -> string = function
  | Pident i -> Ident.name i
  | Pdot (p, s) -> (string_of_path p) ^ "." ^ s
  | _ -> assert false

let rec trans_value_bindings vbs =
  List.fold_right
    (fun vb e ->
      match (vb.vb_pat).pat_desc with
      | Tpat_var (_, v) ->
         EConstr
           ("BiCons",
            [EConstr
               ("Binding",
                [ EConstr ("PVar", [EPlain v.txt]);
                  trans_tl_expr vb.vb_expr]); e])
      | Tpat_any -> assert false
      | Tpat_alias (_, _, _) -> assert false
      | Tpat_constant _ -> assert false
      | Tpat_tuple _ -> assert false
      | Tpat_construct (_, _, _, _) -> assert false
      | Tpat_variant (_, _, _) -> assert false
      | Tpat_record (_, _) -> assert false
      | Tpat_array _ -> assert false
      | Tpat_lazy _ -> assert false
      | Tpat_or (_, _, _) -> assert false)
    vbs (EPlain "BiNil")

and trans_tl_expr (e: expression) =
  match e.exp_desc with
  | Texp_constant c ->
     begin
       match c with
       | Asttypes.Const_int i -> EConstr ("EInt", [EPlain (string_of_int i)])
       | Asttypes.Const_char _ -> assert false
       | Asttypes.Const_string (_, _, _) -> EPlain "TODO: strings"
       | Asttypes.Const_float _ -> assert false
       | Asttypes.Const_int32 _ -> assert false
       | Asttypes.Const_int64 _ -> assert false
       | Asttypes.Const_nativeint _ -> assert false
     end

  | Texp_function {cases = [{c_lhs=p; c_guard=None; c_rhs=e}]; _} ->
     (* param: Ident.t
        cases: value case list *)
     (* f: x => e *)
     let body: expr =
         match p.pat_desc with
         | Tpat_var (i, _) ->
            EConstr ("EFun", [EPlain ("\"" ^ Ident.name i ^ "\"");
                              trans_tl_expr e])
         | _ -> assert false
       in
       (* The EFun and variable would be redundant otherwise
         EConstr
       ("EFun",
        [EPlain ("\"" ^ Ident.name param ^ "\""); (* x *)
        body]) *)
       body

  | Texp_function _ -> assert false

  | Texp_apply (f, el) ->
     List.fold_right
       ( fun a f -> match a with
                 | (_, None) -> f
                 | (_, Some e) -> EConstr ("EApp", [f; trans_tl_expr e]))
       el (trans_tl_expr f)

  | Texp_assert e -> EConstr ("EAssert", [trans_tl_expr e])

  | Texp_ident (p, _, _) -> EConstr ("EVar", [EPlain (string_of_path p)])

  | Texp_let (_, vbl, e) ->
     EConstr ("ELet", [trans_value_bindings vbl; trans_tl_expr e])

  | Texp_match (_, _, _) -> assert false
  | Texp_try (_, _) -> assert false
  | Texp_tuple _ -> assert false
  | Texp_construct (_, _, _) -> assert false
  | Texp_variant (_, _) -> assert false
  | Texp_record _ -> assert false
  | Texp_field (_, _, _) -> assert false
  | Texp_setfield (_, _, _, _) -> assert false
  | Texp_array _ -> assert false
  | Texp_ifthenelse (_, _, _) -> assert false
  | Texp_sequence (_, _) -> assert false
  | Texp_while (_, _) -> assert false
  | Texp_for (_, _, _, _, _, _) -> assert false
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

(* TODO: Other patterns should be supported once the type of [AnnonFun] changes.
   For example, tuples should be allowed. *)
and trans_tl_value_binding (vb: Typedtree.value_binding): string option * expr =
  match vb.vb_pat.pat_desc with
  | Tpat_any -> None, trans_tl_expr vb.vb_expr
  | Tpat_var (i, _) -> Some (Ident.name i), trans_tl_expr vb.vb_expr
  | Tpat_construct (_, i, _, _) ->
     (* [let () = e] bahaves as [let _ = e] at top-level. *)
     if i.cstr_name = "()"
     then None, trans_tl_expr vb.vb_expr
     else assert false
  | _ -> assert false


(* [translate_structure] traslates a typed program into a value of type [Ast].
   Note: if need be, it is possible to query the environment at the
   ````` [structure_item] at hand, which might be useful if the translation tool
   ever need to generate environment in the Coq development. *)
let trans_tl_structure (si: Typedtree.structure_item) =
  match si.str_desc with
  (* Non-recursive top-level bindings. *)
  | Tstr_value (Nonrecursive, vbl) ->
     List.map trans_tl_value_binding vbl
  (* Recursive top-level bindings. *)
  | Tstr_value (Recursive, vbl) ->
     List.map trans_tl_value_binding vbl
  | Tstr_eval _ -> assert false (* of expression * attributes *)
  | Tstr_primitive _ -> assert false (* of value_description *)
  | Tstr_type _ -> assert false (* of Asttypes.rec_flag * type_declaration list *)
  | Tstr_typext _ -> assert false (* of type_extension *)
  | Tstr_exception _ -> assert false (* of type_exception *)
  | Tstr_module _ -> assert false (* of module_binding *)
  | Tstr_recmodule _ -> assert false (* of module_binding list *)
  | Tstr_modtype _ -> assert false (* of module_type_declaration *)
  | Tstr_open _ -> assert false (* of open_declaration *)
  | Tstr_class _ -> assert false (* of (class_declaration * string list) list *)
  | Tstr_class_type _ -> assert false
  (* of
     (Ident.t * string Location.loc * class_type_declaration) list *)
  | Tstr_include _ -> assert false (* of include_declaration *)
  | Tstr_attribute _ -> assert false (*of attribute*)

let translate (t: Typedtree.structure) =
  List.flatten (List.map trans_tl_structure t.str_items)
