open OsirisAst

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

let rec translate_pattern (p: pat) : expression =
  match p with
  | PUnit -> EPlain "PUnit"

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
  | PTuple [] -> EPlain "PUnit"
  | PTuple ps -> (* of pats *)
     EList ("PMkTuple", List.map translate_pattern ps)
  (* A data constructor pattern *)
  | PData (d, p) -> (* of data * pat *)
     EConstr ("PData", [ string_literal d ;
                         translate_pattern p ])
  (* A record pattern *)
  | PRecord _fps -> (* of fpats *)
     assert false
  (* A literal integer pattern *)
  | PInt i -> (* of int *)
     if 0 <= i
     then EConstr ("PInt", [EPlain (string_of_int i)])
     else EConstr ("PInt", [EPlain ("("^string_of_int i^")%Z")])

let translate_path (x: path) : expression =
  let rec translate_path x =
    match x with
    | PathBase name ->
       EConstr ("PathBase", [string_literal name])
    | PathDot (x, name) ->
       EConstr ("PathDot", [translate_path x; string_literal name])
  in
  EConstr ("EPath", [translate_path x])

let rec translate_lambda (AnonFun (v, e)) : expression =
  EConstr ("AnonFun", [ string_literal v ;
                        translate_expression e ])

and translate_branch (Branch (p, e)) : expression =
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
  | EUnit -> EPlain "EUnit"
  | EConstant s -> EConstr ("EConstant", [string_literal  s])

  (* Path: [x] or [πx] *)
  | EPath x -> (* of path *)
     translate_path x

  (* An anonymous function *)
  | EAnonFun a -> (* of anonfun *)
     EConstr ("EAnonFun", [translate_lambda a])

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
                         translate_expression (ETuple [e]) ])

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
     EConstr ("EString", [string_literal s])

  (* Integer literals *)
  | EInt i -> (* of int *)
     if 0 <= i
     then EConstr ("EInt", [EPlain (string_of_int i)])
     else EConstr ("EInt", [EPlain ("("^string_of_int i^")%Z")])

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

  (* Local [open] directive: [let open π in e] *)
  | ELetOpen (p, e) -> (* of path * expr *)
     EConstr ("ELetOpen", [ translate_path p ;
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

  (* The following does not exist in OCaml. Therefore, it will not show up
     here. *)
  | EBoolConj _ (* of expr * expr *)
  | EBoolDisj _ (* of expr * expr *)
  | EBoolNeg _ (* of expr *)
  | EMaxInt
  | EMinInt
  | EIntNeg _ (* of expr *)
  | EIntAdd _ (* of expr * expr *)
  | EIntSub _ (* of expr * expr *)
  | EIntMul _ (* of expr * expr *)
  | EIntDiv _ (* of expr * expr *)
  | EIntMod _ (* of expr * expr *)
  | EOpEq _ (* of expr * expr *)
  | EOpNe _ (* of expr * expr *)
  | EOpLt _ (* of expr * expr *)
  | EOpLe _ (* of expr * expr *)
  | EOpGt _ (* of expr * expr *)
  | EOpGe _ (* of expr * expr *)
  | EAssertFalse
  | ERef _ (* of expr *)
  | ELoad _ (* of expr *)
  | EStore _ (* of expr * expr *)
    -> assert false

(* -------------------------------------------------------------------------- *)

(* On bindings translation. *)

and translate_binding (Binding (p, e)) : expression =
  EConstr ("Binding", [
    translate_pattern p;
    translate_expression e
  ])

and translate_rec_binding (RecBinding (v, a)) : expression =
  EConstr ("RecBinding", [
    string_literal v ;
    translate_lambda a
  ])

and translate_bindings (bds: bindings) : expression =
  list "BiNil" "BiCons" translate_binding bds

and translate_rec_bindings (rbds: rec_bindings) : expression =
  list "RecBiNil" "RecBiCons" translate_rec_binding rbds

(* -------------------------------------------------------------------------- *)

(* On module translation. *)

and translate_sitem : sitem -> expression option = function
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

  (* An [open] directive [open π] *)
  | IOpen (_path) -> assert false

  (* An [include] directive [include me] *)
  | IInclude (_mexpr) -> assert false

and translate_sitems l = Misc.filtermap translate_sitem l

and translate_module = function
  | MStruct sitems ->
     EList ("MkStruct", translate_sitems sitems)
  | MPath _ -> assert false
  | MCoercion _ -> assert false

(* -------------------------------------------------------------------------- *)

let definition_of_ast _verbose _debug : OsirisAst.ast -> string * expression =
  function
  | OModule m -> "mexpr", translate_module m
  | OExpr e -> "expr", translate_expression e
  | ORecBindings rbds -> "rec_bindings", translate_rec_bindings rbds
  | OBindings bds -> "bindings", translate_bindings bds
