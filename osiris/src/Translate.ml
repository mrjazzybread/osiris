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
      (* A variable or module identifier. *)
      Ident.name i
  | Pdot (p, x) ->
      (* A field selection in a structure. *)
      sprintf "%s.%s" (show_path p) x
  | Papply (p1, p2) ->
      (* A functor application. *)
      sprintf "%s(%s)" (show_path p1) (show_path p2)
  | Pextra_ty (p, Pcstr_ty data) ->
      (* This path names the inline record carried by the data constructor
         [data] of the algebraic data type [p]. See [path.mli]. *)
      (* OCaml has no agreed-upon surface syntax for this concept. *)
      sprintf "%s/%s{}" (show_path p) data
  | Pextra_ty (p, Pext_ty) ->
      (* This path names the inline record carried by the extensible data
         constructor [p]. See [path.mli]. *)
      (* OCaml has no agreed-upon surface syntax for this concept. *)
      sprintf "%s{}" (show_path p)

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

(* Recognizing global identifiers and paths. *)

exception Unrecognized

(* [recognize_global_ident id] checks that [id] is a global identifier, and
   if so, returns its name. Otherwise, [Unrecognized] is raised. *)

let recognize_global_ident (id : Ident.t) : string =
  if Ident.global id then
    Ident.name id
  else
    raise Unrecognized

(* [recognize_global_path path] checks that [path] is rooted at a global
   identifier, and if so, converts this path to a list of strings, where
   the first element of the list represents the root of the path.
   Otherwise, [Unrecognized] is raised. *)

let rec recognize_global_path path : string list =
  match path with
  | Pident id ->
      [recognize_global_ident id]
  | Pdot (parent, field) ->
      recognize_global_path parent @ [field]
  | Papply _
  | Pextra_ty _ ->
      raise Unrecognized

(* Recognizing the Boolean expression [false]. *)

(* This code is a bit fragile, as the user might find a way of redefining
   the identifier [false] to mean something else. The risk seems low. *)

let is_false (e : expression) : bool =
  match e.exp_desc with
  | Texp_construct ({ txt = Lident "false"; _}, _, []) ->
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

let rec undecorate : expr -> expr = function
  | EDecorate (_, e) -> undecorate e
  | e -> e

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
  debug_ident "Texp_ident" path id;
  (* For the moment, we ignore [path] and keep [id]. However, [path]
     could be used to identify references to the OCaml standard library. *)
  translate_longident id

let translate_mod_ident path id : path =
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

(* Recognizing a constructor in an extensible algebraic data type,
   as opposed to a constructor in an ordinary algebraic data type. *)

(* See [types.mli]. *)

let is_extensible constructor_desc =
  match constructor_desc.cstr_tag with
  | Cstr_constant _
  | Cstr_block _
  | Cstr_unboxed ->
      false
  | Cstr_extension _ ->
      true

(* -------------------------------------------------------------------------- *)

(* Patterns, also known as value patterns. *)

(* The type [pattern] is a synonym for [value general_pattern]. *)

let rec translate_pat (pat: pattern) : pat =
  let loc = pat.pat_loc in
  match pat.pat_desc with

  | Tpat_any ->
      PAny

  | Tpat_var (_, x, _) ->
      PVar (txt x)

  | Tpat_alias (pat, _, x, _) ->
      PAlias (translate_pat pat, txt x)

  | Tpat_constant c ->
      translate_pat_constant loc c

  | Tpat_tuple pats ->
      PTuple (translate_pats pats)

  | Tpat_construct (id, constructor_desc, pats, _optional_type_annotation) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
     let tuple = PTuple (translate_pats pats) in
     if is_extensible constructor_desc then
       PXData (translate_longident (txt id), tuple)
     else
       let data = translate_data_constructor id constructor_desc in
       PData  (data, tuple)

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

let rec translate_computation_pattern (pat : computation general_pattern) : cpat =
  match pat.pat_desc with
  | Tpat_value p ->
     (* We need a coercion because the type of Tpat_value is private. *)
     CVal (translate_pat (p :> pattern))

  | Tpat_exception p ->
     CExc (translate_pat p)

  | Tpat_or (p1, p2, _) ->
     let cp1 = translate_computation_pattern p1 in
     let cp2 = translate_computation_pattern p2 in
     COr (cp1, cp2)

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
      EPath (translate_exp_ident path (txt id))

  | Texp_constant c ->
      translate_exp_constant loc c

  | Texp_let (Nonrecursive, vbs, e) ->
      ELet (translate_bindings vbs, translate_expr e)

  | Texp_let (Recursive, vbs, e) ->
      begin try
        ELetRec (translate_rec_bindings vbs, translate_expr e)
      with Unsupported ->
        printf "failed recursive letrec translation\n";
        eunsupported loc "recursive definition of values"
      end

  | Texp_function (params, body) ->
     if List.exists
          (fun (param : function_param) -> match (param.fp_arg_label) with
                        | Nolabel -> false
                        | Labelled _ | Optional _ -> true) params
     then
       eunsupported loc "labelled or optional argument"
     else
      translate_function params body

  | Texp_apply (e, args) ->
      translate_application loc e args

  | Texp_match (e, cases, _partial) ->
      EMatch (translate_expr e, translate_computation_cases cases)

  | Texp_try (e, cases) ->
      ETryWith (translate_expr e, translate_exception_cases cases)

  | Texp_tuple es ->
      ETuple (translate_exprs es)

  | Texp_construct (id, constructor_desc, es) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
     let tuple = ETuple (translate_exprs es) in
     if is_extensible constructor_desc then
       EXData (translate_longident (txt id), tuple)
     else
       let data = translate_data_constructor id constructor_desc in
       EData  (data, tuple)

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

  | Texp_assert (e, _) ->
      if is_false e then
        EAssertFalse
      else
        EAssert (translate_expr e)

  | Texp_lazy _ ->
      eunsupported loc "lazy"

  | Texp_object _ ->
      eunsupported loc "objects"

  | Texp_pack _ ->
      eunsupported loc "first-class modules"

  | Texp_letop _ ->
      eunsupported loc "let operators"

  | Texp_unreachable ->
      (* [assert false] and [.] are both translated to [EAssertFalse]. *)
      EAssertFalse

  | Texp_extension_constructor _ ->
      eunsupported loc "extension constructors"

  | Texp_open ({ open_expr = me; _ }, e) ->
      ELetOpen (translate_mod_expr me, translate_expr e)

and translate_exprs es : exprs =
  map translate_expr es

(* -------------------------------------------------------------------------- *)

(* Expressions: function applications. *)

(* We first check whether this is application is recognized as a special
   application. If so, it receives special treatment. Otherwise, it is
   treated as a normal application. *)

and translate_application loc e args =
  try
    translate_special_application loc e args
  with Unrecognized ->
    let e = translate_expr e in
    match undecorate e with

    (* Recognize [match_with f arg e] as primitive. *)
    | EPath [ "match_with" ]  ->
       assert (List.length args = 3);
       (match args with
        | [(Nolabel, Some f); (Nolabel, Some arg); (Nolabel, Some e)] ->
           (* We expect the body to be a record *)
           (match e.exp_desc with
            | Texp_record
              { fields; representation = _; extended_expression = None } ->
               EMatch (
                   EApp (translate_expr f, translate_expr arg),
                   translate_record_fields_as_branches fields
                 )
            | _ ->
               eunsupported loc "Syntax error in [match_with] body")
        | _ ->
           assert false)

    (* Recognize [try_with f arg e] as primitive. *)
    | EPath [ "try_with" ]  ->
       assert (List.length args = 3);
       (match args with
        | [(Nolabel, Some f); (Nolabel, Some arg); (Nolabel, Some e)] ->
           (* We expect the body to be a record *)
           (match e.exp_desc with
            | Texp_record
              { fields; representation = _; extended_expression = None } ->
               let bs = translate_record_fields_as_branches fields in
               (* [try_with] carries two implicit branches,
                  these branches propagate return values and exceptions. *)
               let bs = Branch (CVal (PVar "x"), EPath [ "x" ]) ::
                          Branch (CExc (PVar "x"), ERaise (EPath [ "x" ])) ::
                            bs in
               EMatch (EApp (translate_expr f, translate_expr arg), bs)
            | _ ->
               eunsupported loc "Syntax error in [match_with] body")
        | _ ->
           assert false)

    (* Default case: [e args]. *)
    | _ ->
       apply e (translate_labeled_arguments loc args)

(* -------------------------------------------------------------------------- *)

(* Expressions: recognition of special applications, that is,
   applications of primitive operations and
   applications of standard library functions. *)

(* If this application is not recognized, then [Unrecognized] is raised. *)

and translate_special_application loc e args =
  match e.exp_desc with

  | Texp_ident (path, _, { val_kind = Val_prim p; _ }) ->
      let path = recognize_global_path path in
      (* This is an application of a primitive operation (to an
         as-yet-undetermined number of arguments). *)
      translate_primitive_application loc path p args

  | Texp_ident (path, _, _) ->
      let path = recognize_global_path path in
      (* This may be an application of a standard library function. *)
      translate_stdlib_application loc path args

  | _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: applications of standard library functions. *)

(* If this application is not recognized, then [Unrecognized] is raised. *)

and translate_stdlib_application loc path args =
  match path, translate_labeled_arguments loc args with
  | ["Stdlib"; "Effect"; "Deep"; "continue"], [e1; e2] ->
      EContinue (e1, e2)
  | ["Stdlib"; "Effect"; "Deep"; "discontinue"], [e1; e2] ->
      EDiscontinue (e1, e2)
  | _, _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: applications of primitive operations. *)

(* An application of a primitive operation (to a correct number of arguments)
   is recognized as such. If the primitive operation is not recognized or is
   applied to an incorrect number of arguments, then [Unrecognized] is
   raised. *)

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

and translate_primitive_application loc path p args =
  match path, p.prim_name, translate_labeled_arguments loc args with

  (* Erasing applications of [Obj.magic] is an experimental feature. It takes
     careful consideration and arguments to ascertain that this is sound. *)
  | ["Stdlib"; "Obj"; "magic"], "%identity", [e] ->
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

  | ["Stdlib"; "ref"], "%makemutable", [e] ->
      ERef e
  | ["Stdlib"; "!"], "%field0", [e] ->
      ELoad e
  | ["Stdlib"; ":="], "%setfield0", [e1; e2] ->
      EStore (e1, e2)

  (* Exceptions. *)

  | ["Stdlib"; "raise"], "%raise", [e] ->
      ERaise e

  (* Effects. *)

  | ["Stdlib"; "Effect"; "perform"], "%perform", [e] ->
      EPerform e

  | _, _, _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: anonymous functions. *)

and translate_function params body : expr =
  match body with
  | Tfunction_body e ->
     let rec talt params (acc : expr -> expr) =
       match params with
       | [] -> acc
       | p :: params ->
          match p.fp_kind with
          | Tparam_pat p ->
             (match p.pat_desc with
              | Tpat_var (_, x, _) ->
                 talt params (fun e -> acc (EAnonFun (AnonFun (txt x, e))))
              | _ ->
                 talt params (fun e -> acc (EAnonFun (AnonFunction [Branch (CVal (translate_pat p), e)]))))
          | Tparam_optional_default (_, _) ->
             talt params (fun _ -> acc (EUnsupported))
     in
     talt params (fun e -> e) (translate_expr e)
  | Tfunction_cases { cases; partial; param = _; loc = _; exp_extra = _; attributes = _ } ->
     match cases with
     | [{ c_lhs = { pat_desc = Tpat_var (_, x, _); _ };
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

(* Expressions: fields in the body of a [match_with] application. *)

and translate_record_fields_as_branches fields =
  List.concat_map translate_record_field_as_branches (Array.to_list fields)

(* We restrict the syntax of the body of a match_with. We expect
   the value and exception fields to be of the form [fun v -> e].
   The effect field should be of the form [fun v -> match v with bs].  *)

and translate_record_field_as_branches (_, label_def) : branch list =
  match label_def with
  | Kept _ ->
     (* This field is omitted. This can occur only in a record update
        expression. *)
     []
  | Overridden (id, e) when (Longident.flatten id.txt) = ["retc"] ->
     (match undecorate (translate_expr e) with
      | EAnonFun (AnonFunction bs) -> bs
      | EAnonFun (AnonFun (v, e)) -> [Branch (CVal (PVar v), e)]
      | e -> printf "%s\n" (show_expr e); [])
      (* | _ -> assert false) *)

  | Overridden (id, e) when (Longident.flatten id.txt) = ["exnc"] ->
     (match undecorate (translate_expr e) with
      | EAnonFun (AnonFunction bs) -> bs
      | EAnonFun (AnonFun (v, e)) -> [Branch (CExc (PVar v), e)]
      | e -> printf "%s\n" (show_expr e); [])
      (* | _ -> assert false) *)

  | Overridden (id, e) when (Longident.flatten id.txt) = ["effc"] ->
     (match undecorate (translate_expr e) with
      (* For now, we ignore the pattern matching on the arguments bound
         by the anonymous function.

         Due to the signature of [handler] in Effect.Deep, we know that
         there is only one argument to this anonymous function. *)
      | EAnonFun (AnonFunction [Branch (_, e)])
      | EAnonFun (AnonFun (_, e)) ->
         (match undecorate e with
          | EMatch (_, bs) ->
             translate_branches_to_effect_branches bs
          | _ -> assert false)
      | e -> printf "%s\n" (show_expr e); [])
   (* | _ -> assert false) *)
  | _ -> []

(* We expect the branches in our effect field to be of the following form:
   [ | Eff -> Some (fun k -> e) ]. *)

and translate_branch_to_effect_branch b =
  match b with

  | Branch (CVal peff, e) ->
     (match (undecorate e) with
      | EData ("None", _) ->
         None
      | EData (_, e) ->
         (match (undecorate e) with
          | ETuple [ e ] ->
             (match (undecorate e) with
              (* | p -> Some (fun k -> e) *)
              | EAnonFun (AnonFun (k, e)) ->
                 Some (Branch (CEff (peff, PVar k), e))
              (* | peff -> Some (fun pk -> e) *)
              | EAnonFun (AnonFunction [Branch (CVal pk, e)]) ->
                 Some (Branch (CEff (peff, pk), e))
              | _ -> assert false)
          | ETuple [] ->
             None
          | _ -> assert false)
      | _ -> assert false)
  | _ ->
     Some (Branch (CEff (PAny, PAny), EUnsupported))

and translate_branches_to_effect_branches bs =
  List.filter_map translate_branch_to_effect_branch bs

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

and translate_case : type k . (k general_pattern -> cpat) -> k case -> branch =
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
  translate_case (fun p -> CVal (translate_pat p)) case

and translate_value_cases cases =
  map translate_value_case cases

and translate_exception_case (case : value case) : branch =
  translate_case (fun p -> CExc (translate_pat p)) case

and translate_exception_cases cases =
  map translate_exception_case cases

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
  | e -> printf "%s\n" (show_expr e); raise Unsupported

and project_Tpat_var (pat : value general_pattern) : var =
  match pat.pat_desc with
  | Tpat_var (_, v, _) -> txt v
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
      MPath (translate_mod_ident path (txt id))

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
