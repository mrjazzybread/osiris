open Ast
open Typedtree
open Types



(* -------------------------------------------------------------------------- *)
(* Definition of several constructors for our custom lists. *)

type adhoc_list = {
    cons: string ;
    nil: string ;
    wrapper: string ;
  }

(* Tuples within expressions *)
let etuple = { cons = "ECons" ;
               nil = "ENil" ;
               wrapper = "ETuple" }

(* Tuples within patterns *)
let ptuple = { cons = "PCons" ;
               nil = "PNil" ;
               wrapper = "PTuple" }

let btuple = { cons = "BrCons" ;
               nil = "BrNil" ;
               wrapper = "" }


(* -------------------------------------------------------------------------- *)
(* The following function transforms identifiers into strings. *)

(* In the Typedtree, OCaml identifiers and symbols are addressed in several
   formats. The following functions translates these representations to
   strings. Note that the result of these functions contains quotes, which can
   be confusing sometimes, but avoids adding them at every call site. *)
let string_of_longident (i: Longident.t): string =
  Longident.flatten i
  |> List.map (fun s -> "\"" ^ s ^ "\"")
  |> String.concat "." (* TODO what does this mean? *)

let rec translate_path (path : Path.t) : expr =
  match path with
  | Pident i ->
      EConstr ("PathBase", [string_literal (Ident.name i)])
  | Pdot (path, s) ->
      EConstr ("PathDot", [translate_path path; string_literal s])
  | _ ->
      assert false (* TODO *)

(* Unified translation of tuples represented by ad-hoc lists in the Coq
   files. *)
let translate_tuple ({cons; nil; wrapper}: adhoc_list)
          (translator: 'a -> expr) (lily: 'a list) =
  let body =
    List.fold_right
      (fun elt res ->
        EConstr (cons, [ translator elt ;
                         res ]))
      lily (EPlain nil) in
  EConstr (wrapper, [body])



(* -------------------------------------------------------------------------- *)
(* The following functions translate small pieces of the AST into expressions of
   type [expr]. *)

let translate_constant = function
  | Asttypes.Const_int i -> EConstr ("EInt", [EPlain (string_of_int i)])

  (* Not yet translated: integers.
     Do we want several instantiations of the CompCert integers library, or
     should we simply define modules [Int32], [Int64] and [NativeInt] ? *)
  | Asttypes.Const_int32 _ -> assert false
  | Asttypes.Const_int64 _ -> assert false
  | Asttypes.Const_nativeint _ -> assert false

  (* Not yet supported by the semantics: *)
  | Asttypes.Const_char _ -> assert false
  | Asttypes.Const_string (_, _, _) -> assert false
  | Asttypes.Const_float _ -> assert false



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
                let name : string = "\"" ^ elt.lbl_name ^ "\"" in
                let body : expr = trans_expr e in
                EConstr ("FECons",
                         [ EPlain name ;
                           body ;
                           expr ]))
           fields (EPlain "FENil")
       in
       EConstr ("ERecord", [body])
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
                EConstr ("FECons",
                         [ EPlain name ;
                           body ;
                           expr ]))
           fields (EPlain "FENil")
       in
       EConstr ("ERecordUpdate",
                [ trans_expr e ;
                  body])
     end
  | _ -> assert false

let unvarpat (p : value general_pattern) : string =
  match p.pat_desc with
  | Tpat_var (_, x) ->
      x.txt
  | _ ->
      (* A variable pattern was expected. *)
      assert false

let unlambda (e : expression) : (value general_pattern * expression) list =
  match e.exp_desc with
  | Texp_function {cases; _} ->
     List.fold_right
       (fun {c_lhs; c_rhs; _} res ->
         (c_lhs, c_rhs) :: res)
       cases []
  | _ ->
      (* An anonymous function was expected. *)
      assert false

let rec trans_computation_pat (p: computation general_pattern): expr =
  (* p.pat_desc => Tpat_value v, with v of type tpat_value_argument.
     Hence, working with v would be difficult.
   *)
  match split_pattern p with
  | (Some p, None) ->
     trans_pat p
  | _ -> assert false

and trans_pat (p: value general_pattern): expr =
  match p.pat_desc with
  | Tpat_any -> EPlain "PAny"
  | Tpat_var (_, v) -> EConstr ("PVar", [string_literal v.txt])
  | Tpat_tuple pl -> translate_tuple ptuple trans_pat pl

  | Tpat_construct (i, _, args, _) ->
     (* Note that by the definition of [string_of_longident], [name] will
        contain quotes. *)
     let name = string_of_longident i.txt in
     if name = "\"()\"" && args = []
     then EPlain "PUnit"
     else if name = "\"true\"" && args = []
     then EPlain "(PBool true)"
     else if name = "\"false\"" && args = []
     then EPlain "(PBool false)"
     else
       let args = translate_tuple ptuple trans_pat args in
       EConstr ("PData", [ EPlain name; args ])

  | Tpat_alias (_, _, _) -> assert false
  | Tpat_constant _ -> assert false
  | Tpat_variant (_, _, _) -> assert false
  | Tpat_record (_, _) -> assert false
  | Tpat_array _ -> assert false
  | Tpat_lazy _ -> assert false
  | Tpat_or (_, _, _) -> assert false



(* -------------------------------------------------------------------------- *)

(* Main translation function for expressions.
   This function relies on all of the above.*)
let rec translate_lambda branches =
  EConstr ("AnonFunction", [
    translate_branches branches
  ])

and translate_branch (p, e) =
  EConstr ("Branch", [trans_pat p; trans_tl_expr e])

and translate_branches branches =
  translate_tuple btuple translate_branch branches

and trans_tl_expr (e: expression) =
  match e.exp_desc with
  | Texp_constant c -> translate_constant c

  | Texp_function {cases = [case]; _} ->
     let cases = [case] in
     let branches =
       List.fold_right
         (fun {c_lhs;c_rhs;_} res ->
           (c_lhs, c_rhs) :: res)
         cases []
     in
     EConstr ("EAnonFun", [translate_lambda branches])
  | Texp_function _ -> assert false
  | Texp_apply (f, el) ->
     List.fold_left
       ( fun f a -> match a with
                 | (_, None) -> f
                 | (_, Some e) -> EConstr ("EApp", [f; trans_tl_expr e]))
       (trans_tl_expr f) el

  | Texp_assert e -> EConstr ("EAssert", [trans_tl_expr e])

  | Texp_ident (path, _, _) ->
      EConstr ("EPath", [translate_path path])

  | Texp_let (_, vbs, e) ->
     EConstr ("ELet", [translate_bindings vbs; trans_tl_expr e])

  | Texp_tuple el -> translate_tuple etuple trans_tl_expr el

  | Texp_match (e, cl, _) ->
     (* [e]  : expression
        [cl] : computation case list *)
     let cases =
       List.fold_right
         (fun (case: computation case) (cases: expr) ->
           match case with
           | { c_lhs=pat; c_guard=None; c_rhs=e } ->
              EConstr ("BrCons",
                       [EConstr ("Branch",
                                 [trans_computation_pat pat; trans_tl_expr e])
                       ; cases])
           | _ -> assert false)
         cl (EPlain "BrNil") in
     EConstr ("EMatch", [trans_tl_expr e; cases])

  | Texp_construct (c, _, el) ->
     (* Some OCaml constructors directly have counterpart in the syntax, as :
        - Unit: ["()"]
      *)
     let name = string_of_longident c.txt in
     if name = "\"()\"" && el = [] then EPlain "EUnit"
     else
       begin
         let args =
           List.fold_right
             (fun e res ->
               EConstr ("ECons",
                        [trans_tl_expr e;
                         res]))
             el (EPlain "ENil")
         in
         EConstr ("EData",
                  [EPlain name;
                   EConstr ("ETuple", [args])])
       end

  | Texp_sequence (e1, e2) ->
     EConstr ("ESeq",
              [ trans_tl_expr e1;
                trans_tl_expr e2 ])

  | Texp_ifthenelse (e1, e2, Some e3) ->
     EConstr ("EIfThenElse",
              [ trans_tl_expr e1;
                trans_tl_expr e2;
                trans_tl_expr e3 ])

  | Texp_ifthenelse (e1, e2, None) ->
     EConstr ("EIfThen",
              [ trans_tl_expr e1;
                trans_tl_expr e2 ])

  | Texp_record { fields; representation; extended_expression } ->
     translate_record
       fields representation extended_expression
       trans_tl_expr

  | Texp_field (e, _, label) ->
     EConstr ("ERecordAccess",
              [ trans_tl_expr e ;
                string_literal label.lbl_name
       ])

  | Texp_try (_, _) -> assert false
  | Texp_variant (_, _) -> assert false
  | Texp_setfield (_, _, _, _) -> assert false
  | Texp_array _ -> assert false
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



(* -------------------------------------------------------------------------- *)

and translate_binding (vb: Typedtree.value_binding) : expr =
  EConstr ("Binding", [
    trans_pat vb.vb_pat;
    trans_tl_expr vb.vb_expr
  ])

and translate_rec_binding vb : expr =
  EConstr ("RecBinding", [
    string_literal (unvarpat vb.vb_pat);
    translate_lambda (unlambda vb.vb_expr)
  ])

and translate_bindings vbs : expr =
  list "BiNil" "BiCons" (List.map translate_binding vbs)

and translate_rec_bindings vbs : expr =
  list "RecBiNil" "RecBiCons" (List.map translate_rec_binding vbs)

(* -------------------------------------------------------------------------- *)
(* The OCaml Typedtree is a list of structures. Each structure either represents
   - type-related declarations
   - [let (rec)] declarations
   - module-related declarations

   Current issue :
     mutually recursive definitions are represented as two distinct
     [let (rec)? ...] constructs, which does not allow them to be verified.

     The [translate] function should not flatten the definitions, but rather
     return a list of lists of declarations. This way, the [and] constructs
     could be respected by the translator. *)


(* [translate_structure] translates a typed program into a value of type [ast].
   Note: if need be, it is possible to query the environment at the
   ````` [structure_item] at hand, which might be useful if the translation tool
   ever need to generate environment in the Coq development. *)
let translate_sitem (si: Typedtree.structure_item) : expr option =
  match si.str_desc with
  (* Non-recursive top-level bindings. *)
  | Tstr_value (Nonrecursive, vbs) ->
      Some (EConstr ("ILet", [translate_bindings vbs]))
  (* Recursive top-level bindings. *)
  | Tstr_value (Recursive, vbs) ->
      Some (EConstr ("ILetRec", [translate_rec_bindings vbs]))

  (* Ignoring the type-related definitions. *)
  | Tstr_type _ (* of Asttypes.rec_flag * type_declaration list *)
  | Tstr_modtype _ (* of module_type_declaration *)
  | Tstr_class_type _ (* of (Ident.t * string Location.loc * class_type_declaration) list *)
      -> None

  | Tstr_eval _ -> assert false (* of expression * attributes *)
  | Tstr_primitive _ -> assert false (* of value_description *)
  | Tstr_typext _ -> assert false (* of type_extension *)
  | Tstr_exception _ -> assert false (* of type_exception *)
  | Tstr_module _ -> assert false (* of module_binding *)
  | Tstr_recmodule _ -> assert false (* of module_binding list *)
  | Tstr_open _ -> assert false (* of open_declaration *)
  | Tstr_class _ -> assert false (* of (class_declaration * string list) list *)
  | Tstr_include _ -> assert false (* of include_declaration *)
  | Tstr_attribute _ -> assert false (*of attribute*)

let translate_sitems items =
  list "INil" "ICons" (List.filter_map translate_sitem items)

let translate (t: Typedtree.structure) : expr =
  EConstr ("MStruct", [translate_sitems t.str_items])
