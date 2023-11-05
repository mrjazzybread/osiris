open Syntax

(* -------------------------------------------------------------------------- *)

type expression =
  | EPlain of string
  | EConstr of string * expression list
  | EList of string * expression list

(* -------------------------------------------------------------------------- *)

(* Miscellaneous functions. *)

let list nil cons translate lily =
  List.fold_right
    (fun elt res ->
      EConstr (cons, [ translate elt ;
                       res ]))
    lily (EPlain nil)

let alist nil cons translate_key translate_elt lily =
  let nil = EPlain nil in
  List.fold_right
    (fun (k, e) res ->
      EConstr (cons, [ translate_key k ;
                       translate_elt e ;
                       res ]))
    lily nil

let string_literal s = EPlain (Printf.sprintf "\"%s\"" s)

(* -------------------------------------------------------------------------- *)

let translate_bool b =
  if b then EPlain "true" else EPlain "false"

let translate_char (c: char) : expression =
  let i = int_of_char c in
  let d0 = i land 1 <> 0
  and d1 = i land 2 <> 0
  and d2 = i land 4 <> 0
  and d3 = i land 8 <> 0
  and d4 = i land 16 <> 0
  and d5 = i land 32 <> 0
  and d6 = i land 64 <> 0
  and d7 = i land 128 <> 0
  in
  (* In Coq, a [char] is represented by the type [ascii]. Each character is
     represented by eight booleans. *)
  EConstr ("Ascii", List.map translate_bool [ d0; d1; d2; d3; d4; d5; d6; d7 ])

let rec translate_pattern (p: pat) : expression =
  match p with

  | PUnsupported ->
      EPlain "PUnsupported"
  (* The wildcard pattern *)
  | PAny -> EPlain "PAny"
  (* A variable *)
  | PVar  v -> (* of variable *)
     EConstr ("PVar", [string_literal v])
  (* An alias pattern [p as x] *)
  | PAlias (p, v) -> (* of pat * variable *)
     EConstr ("PAlias", [ translate_pattern p ;
                          string_literal v ])
  (* A disjunction pattern [p1 | p2] *)
  | POr (p1, p2) -> (* of pat * pat *)
     EConstr ("POr", [ translate_pattern p1 ;
                       translate_pattern p2 ])
  (* A tuple pattern *)
  | PTuple [] -> EPlain "(PTuple PNil)"
  | PTuple ps -> (* of pats *)
     EList ("PMkTuple", List.map translate_pattern ps)
  (* A data constructor pattern *)
  | PData (d, p) -> (* of data * pat *)
     EConstr ("PData", [ string_literal d ;
                         translate_pattern p ])
  (* A record pattern *)
  | PRecord fps -> (* of fpats *)
     EConstr ("PRecord", [translate_fpats fps])
  (* Constant patterns *)
  | PInt i -> (* of int *)
     EConstr ("PInt", [EPlain (string_of_int i)])
  | PChar c ->
     EConstr ("PChar", [translate_char c])
  | PString s ->
     EConstr ("PString", [string_literal (String.escaped s)])

and translate_fpats fpats =
  match fpats with
  | [] -> EPlain "FPNil"
  | (f, pat) :: fpats ->
     EConstr ("FPCons", [ string_literal f ;
                          translate_pattern pat ;
                          translate_fpats fpats ])

let translate_path (x: path) : expression =
  (* We could use [MkPath], but its definition in Coq involves [rev].
     This is very bad, because using [rev] is bad in the first place
     and because [rev] is itself defined in an inefficient way.
     So, better use [MkPathRev]. *)
  EList ("MkPathRev", List.rev (List.map string_literal x))

let rec translate_anonfun (a : anonfun) : expression =
  match a with
  | AnonFun (x, e) ->
      EConstr ("AnonFun", [ string_literal x ;
                          translate_expression e ])
  | AnonFunction bs ->
      EConstr ("AnonFunction", [translate_branches bs])

and translate_branch : branch -> expression = function
  | Branch (p, e) ->
     EConstr ("Branch", [ translate_pattern p ;
                          translate_expression e ])

and translate_branches (bs: branches) : expression =
  EList ("MkBranches", List.map translate_branch bs)

and translate_fexprs (fs: fexprs) : expression =
  alist "FENil" "FECons"
    string_literal
    translate_expression
    fs

and translate_expression (e: expr) : expression =
  match e with

  | EUnsupported ->
      EPlain "EUnsupported"

  | ELink e -> EPlain e

  | EChar c -> EConstr ("EChar", [translate_char c])

  (* Path: [x] or [πx] *)
  | EPath x -> (* of path *)
     EConstr ("EPath", [translate_path x])

  (* An anonymous function *)
  | EAnonFun a -> (* of anonfun *)
     EConstr ("EAnonFun", [translate_anonfun a])

  (* Function application: [e1 e2] *)
  (* Every function is considered unary *)
  | EApp (e1, e2) -> (* of expr * expr *)
     EConstr ("EApp", [ translate_expression e1 ;
                        translate_expression e2 ])

  (* Tuple construction: [(e1, e2, )] *)
  | ETuple el -> (* of exprs *)
     EList ("EMkTuple", List.map translate_expression el)

  (* Data constructor application: [A (e)] *)
  (* Every data constructor is considered unary *)
  | EData (a, e) -> (* of data * expr *)
     EConstr ("EData", [ string_literal a ;
                         translate_expression e ])

  (* Record construction: [{ fs = es }] *)
  | ERecord fs -> (* of fexprs *)
     EConstr ("ERecord", [translate_fexprs fs])

  (* Record update: [{ e and fs = es }] *)
  | ERecordUpdate (er, fs) -> (* of expr * fexprs *)
     EConstr ("ERecordUpdate",
              [ translate_expression er ;
                translate_fexprs fs ])

  (* Record access: [ef] *)
  | ERecordAccess (er, field) -> (* of expr * field *)
     EConstr ("ERecordAccess", [ translate_expression er ;
                                 string_literal field ])

  (* Strings *)
  | EString s -> (* of string *)
     EConstr ("EString", [string_literal (String.escaped s)])

  (* Integer literals *)
  | EInt i -> (* of int *)
     EConstr ("EInt", [EPlain (string_of_int i)])

  (* Polymorphic comparison operators *)

  (* Non-recursive local definition: [let bs in e] *)
  | ELet (bds, e) -> (* of bindings * expr *)
     EConstr ("ELet", [ translate_bindings bds ;
                        translate_expression e ])

  (* Recursive local definition: [let rbs in e] *)
  | ELetRec (rbds, e) -> (* of rec_bindings * expr *)
     EConstr ("ELetRec", [ translate_rec_bindings rbds ;
                           translate_expression e ])

  (* Local module definition: [let module M = me in e] *)
  | ELetModule (name, m, e) -> (* of name * mexpr * expr *)
     EConstr ("ELetModule", [ string_literal name ;
                              translate_module m ;
                              translate_expression e ])

  (* Local [open] directive: [let open me in e] *)
  | ELetOpen (me, e) ->
     EConstr ("ELetOpen", [ translate_module me ;
                            translate_expression e ])

  (* Sequence: [e1; e2] *)
  | ESeq (e1, e2) -> (* of expr * expr *)
     EConstr ("ESeq", [ translate_expression e1 ;
                        translate_expression e2 ])

  (* Conditional: [if e then e1] and [if e then e1 else e2] *)
  | EIfThen (c, e) -> (* of expr * expr *)
     EConstr ("EIfThen", [ translate_expression c ;
                           translate_expression e ])
  | EIfThenElse (c, e1, e2) -> (* of expr * expr * expr *)
     EConstr ("EIfThenElse", [ translate_expression c ;
                               translate_expression e1 ;
                               translate_expression e2 ])

  (* Pattern matching: [match e and bs] *)
  | EMatch (e, bs) -> (* of expr * branches *)
     EConstr ("EMatch", [ translate_expression e ;
                          translate_branches bs ])

  (* Loop: [while e do body done] *)
  | EWhile (c, e) -> (* of expr * expr *)
     EConstr ("EWhile", [ translate_expression c ;
                          translate_expression e ])
  (* Loop: [for x = e1 to e2 do e done] *)
  | EFor (x, e1, e2, e3) -> (* of variable * expr * expr * expr *)
     EConstr ("EFor", [ string_literal x ;
                        translate_expression e1 ;
                        translate_expression e2 ;
                        translate_expression e3 ])

  (* Runtime assertion: [assert(e)] *)
  | EAssert (e) ->
     EConstr ("EAssert", [translate_expression e])

  | ERef e -> (* of expr *)
     EConstr ("ERef", [translate_expression e])

  | EAssertFalse
    -> EPlain "EAssertFalse"

  | EBoolConj (e1, e2) ->
      EConstr ("EBoolConj", [ translate_expression e1; translate_expression e2 ])

  | EBoolDisj (e1, e2) ->
      EConstr ("EBoolDisj", [ translate_expression e1; translate_expression e2 ])

  | EBoolNeg e ->
      EConstr ("EBoolNeg", [ translate_expression e ])

  (* Reference: dereference. *)
  | ELoad e -> (* of expr *)
     EConstr ("ELoad", [translate_expression e])

  (* Reference: update *)
  | EStore (e1, e2) -> (* of expr * expr *)
     EConstr ("EStore", [translate_expression e1; translate_expression e2])

  | EIntNeg e -> (* of expr *)
     EConstr ("EIntNeg", [translate_expression e])
  | EIntAdd (e1, e2) -> (* of expr * expr *)
     EConstr ("EIntAdd", [translate_expression e1; translate_expression e2])
  | EIntSub (e1, e2) -> (* of expr * expr *)
     EConstr ("EIntSub", [translate_expression e1; translate_expression e2])
  | EIntMul (e1, e2) -> (* of expr * expr *)
     EConstr ("EIntMul", [translate_expression e1; translate_expression e2])
  | EIntDiv (e1, e2) -> (* of expr * expr *)
     EConstr ("EIntDiv", [translate_expression e1; translate_expression e2])
  | EIntMod (e1, e2) -> (* of expr * expr *)
     EConstr ("EIntMod", [translate_expression e1; translate_expression e2])

  | EMaxInt
  | EMinInt
  | EOpEq _ (* of expr * expr *)
  | EOpNe _ (* of expr * expr *)
  | EOpLt _ (* of expr * expr *)
  | EOpLe _ (* of expr * expr *)
  | EOpGt _ (* of expr * expr *)
  | EOpGe _ (* of expr * expr *)
    -> assert false

(* -------------------------------------------------------------------------- *)

(* On bindings translation. *)

and translate_binding  = function
  | BLink s -> EPlain s
  | Binding (p, e) ->
     EConstr ("Binding", [
           translate_pattern p;
           translate_expression e
       ])

and translate_rec_binding = function
  | RecBLink s -> EPlain s
  | RecBinding (v, a) ->
     EConstr ("RecBinding", [
           string_literal v ;
           translate_anonfun a
       ])

and translate_bindings (bds: bindings) : expression =
  list "BiNil" "BiCons" translate_binding bds

and translate_rec_bindings (rbds: rec_bindings) : expression =
  list "RecBiNil" "RecBiCons" translate_rec_binding rbds

(* -------------------------------------------------------------------------- *)

(* On module translation. *)

and translate_sitem : sitem -> expression option = function
  (* An auxiliary Coq top-level definition *)
  | ILink name ->
     Some (EPlain name)

  (* A non-recursive toplevel definition [let bs] *)
  | ILet (bindings) ->
     Some (EConstr ("ILet", [translate_bindings bindings]))

  (* A recursive toplevel definition [let rec rbs] *)
  | ILetRec (rec_bindings) ->
     Some (EConstr ("ILetRec", [translate_rec_bindings rec_bindings]))

  (* A module definition [M = me] *)
  | IModule (name, mexpr) ->
     Some (EConstr ("IModule",
                    [ EPlain ("\"" ^ name ^ "\"");
                      translate_module mexpr]))

  (* An [open] directive [open me] *)
  | IOpen me ->
     Some (EConstr ("IOpen", [translate_module me]))

  (* An [include] directive [include me] *)
  | IInclude (mexpr) ->
     Some (EConstr ("IInclude", [translate_module mexpr]))

and translate_sitems l = List.filter_map translate_sitem l

and translate_module = function
  | MUnsupported ->
      EPlain "MUnsupported"
  | MStruct sitems ->
     EList ("MkStruct", translate_sitems sitems)

  (* Auxiliary top-level Coq definition. *)
  | MLink s -> EPlain s

  | MPath p -> EConstr ("MPath", [translate_path p])
  | MCoercion _ -> assert false

(* -------------------------------------------------------------------------- *)

let translate_sitem sitem =
  match translate_sitem sitem with
  | Some e -> e
  | None -> assert false

let definition_of_ast = function
  | OModule m -> "mexpr", translate_module m
  | OExpr e -> "expr", translate_expression e
  | ORecBinding rbd -> "rec_binding", translate_rec_binding rbd
  | OBinding bd -> "binding", translate_binding bd
  | OSItem sitem -> "sitem", translate_sitem sitem
