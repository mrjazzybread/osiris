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



(* -------------------------------------------------------------------------- *)
(* The following function transforms identifiers into strings. *)

(* In the Typedtree, OCaml identifiers and symbols are addressed in several
   formats. The following functions translates these representations to
   strings. Note that the result of these functions contains quotes, which can
   be confusing sometimes, but avoids adding them at every call site. *)
let string_of_longident (i: Longident.t): string =
  Longident.flatten i
  |> List.map (fun s -> "\"" ^ s ^ "\"")
  |> String.concat "."

let rec string_of_path : Path.t -> string = function
  | Pident i -> Ident.name i
  | Pdot (p, s) -> (string_of_path p) ^ "." ^ s
  | _ -> assert false

let string_of_ident (i: Ident.t) : string =
  "\"" ^ Ident.name i ^ "\""


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
     (* This explicitely defines the whole record in the expected way. *)
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
  | Tpat_var (_, v) -> EConstr ("PVar", [EPlain v.txt])
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



let rec trans_value_bindings vbs =
  List.fold_right
    (fun vb e ->
      EConstr
        ("BiCons",
         [EConstr
            ("Binding",
             [ trans_pat vb.vb_pat;
               trans_tl_expr vb.vb_expr]); e]))
    vbs (EPlain "BiNil")



(* -------------------------------------------------------------------------- *)

(* Main translation function for expressions.
   This function relies on all of the above.*)
and trans_tl_expr (e: expression) =
  match e.exp_desc with
  | Texp_constant c -> translate_constant c

  (* The translation of functions needs to know what kind of pattern is
     used to decide what syntactic sugar to use. It might be interesting to
     partition the OCaml constructs according to their translations and use
     [trans_pat] defined above + transformation functions for each case. *)
  | Texp_function {cases = [{c_lhs=p; c_guard=None; c_rhs=e}]; _} ->
     (* param: Ident.t
        cases: value case list *)
     (* f: x => e *)
     let body: expr =
         match p.pat_desc with
         | Tpat_var (i, _) ->
            EConstr ("EFun1Var", [EPlain (string_of_ident i);
                                  trans_tl_expr e])
         | Tpat_any ->
            EConstr ("EFun1Pat", [EPlain "PAny";
                                  trans_tl_expr e])

         | Tpat_construct (i, desc, _, _) ->
            (* This construction should only be used for [()].
               Here, [()] is translated to [EPlain "()"], not
               [EConstr ("EData", [EPlain "()"])]. *)
            if desc.cstr_arity = 0 && (string_of_longident i.txt = "\"()\"")
            then EConstr ("EFun1Pat", [EPlain ("PAny");
                                   trans_tl_expr e])
            else assert false

         | Tpat_tuple l ->
            let arg = translate_tuple ptuple trans_pat l in
            EConstr ("EFun1Pat", [arg; trans_tl_expr e])

         | Tpat_alias _ -> assert false
         | Tpat_constant _ -> assert false
         | Tpat_variant _ -> assert false
         | Tpat_record _ -> assert false
         | Tpat_array _ | Tpat_lazy _ | Tpat_or _ -> assert false
       in
       body

  | Texp_function _ -> assert false

  | Texp_apply (f, el) ->
     List.fold_left
       ( fun f a -> match a with
                 | (_, None) -> f
                 | (_, Some e) -> EConstr ("EApp", [f; trans_tl_expr e]))
       (trans_tl_expr f) el

  | Texp_assert e -> EConstr ("EAssert", [trans_tl_expr e])

  | Texp_ident (p, _, _) -> EConstr ("EVar", [EPlain (string_of_path p)])

  | Texp_let (_, vbl, e) ->
     EConstr ("ELet", [trans_value_bindings vbl; trans_tl_expr e])

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
                EPlain ("\"" ^ label.lbl_name ^ "\"")
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
(* [trans_tl_value_binding] translates a top-level binding into an element of
   type [string option * bool * expr], where :
   - the [string] element represents the name of the OCaml declaration if it
     exists.
   - the [bool] element is a recursivity flag : [true] means that the function is
     recursive, [false] that it is not
   - the [expr] element represents the body of the declaration. *)


(* TODO: Other patterns should be supported. *)
and trans_tl_value_binding (recursive: bool) (vb: Typedtree.value_binding):
      string option * bool * expr =
  match vb.vb_pat.pat_desc with
  | Tpat_any -> None, recursive, trans_tl_expr vb.vb_expr
  | Tpat_var (i, _) -> Some (Ident.name i), recursive, trans_tl_expr vb.vb_expr
  | Tpat_construct (_, i, _, _) ->
     (* [let () = e] bahaves as [let _ = e] at top-level. *)
     if i.cstr_name = "()"
     then None, recursive, trans_tl_expr vb.vb_expr
     else assert false
  | _ -> assert false



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
let trans_tl_structure (si: Typedtree.structure_item) =
  match si.str_desc with
  (* Non-recursive top-level bindings. *)
  | Tstr_value (Nonrecursive, vbl) ->
     List.map (trans_tl_value_binding false) vbl
  (* Recursive top-level bindings. *)
  | Tstr_value (Recursive, vbl) ->
  (* List.map trans_tl_value_binding vbl *)
     List.map (trans_tl_value_binding true) vbl

  (* Ignoring the type-related definitions. *)
  | Tstr_type _ (* of Asttypes.rec_flag * type_declaration list *)
  | Tstr_modtype _ (* of module_type_declaration *)
  | Tstr_class_type _ (* of (Ident.t * string Location.loc * class_type_declaration) list *)
      -> []

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

let translate (t: Typedtree.structure): ast =
  List.flatten (List.map trans_tl_structure t.str_items)
