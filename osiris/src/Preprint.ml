open Syntax
open Coq

let string_literal s = plain (Printf.sprintf "\"%s\"" s)

(* -------------------------------------------------------------------------- *)

let translate_bool b =
  if b then plain "true" else plain "false"

let translate_char (cc : char) : expression =
  let i = int_of_char cc in
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
  c "Ascii" (List.map translate_bool [ d0; d1; d2; d3; d4; d5; d6; d7 ])

let rec translate_pattern (p: pat) : expression =
  match p with

  | PUnsupported ->
      plain "PUnsupported"
  (* The wildcard pattern *)
  | PAny ->
      plain "PAny"
  (* A variable *)
  | PVar  v ->
      c "PVar" [string_literal v]
  (* An alias pattern [p as x] *)
  | PAlias (p, v) ->
      c "PAlias" [ translate_pattern p; string_literal v ]
  (* A disjunction pattern [p1 | p2] *)
  | POr (p1, p2) -> (* of pat * pat *)
     c "POr" [ translate_pattern p1; translate_pattern p2 ]
  (* A tuple pattern *)
  | PTuple [] ->
      plain "(PTuple PNil)"
  | PTuple ps -> (* of pats *)
      clist "PMkTuple" (List.map translate_pattern ps)
  (* A data constructor pattern *)
  | PData (d, p) ->
      c "PData" [ string_literal d; translate_pattern p ]
  (* A record pattern *)
  | PRecord fps ->
      c "PRecord" [translate_fpats fps]
  (* Constant patterns *)
  | PInt i ->
      c "PInt" [plain (string_of_int i)]
  | PChar c' ->
      c "PChar" [translate_char c']
  | PString s ->
     c "PString" [string_literal (String.escaped s)]

and translate_fpats fpats =
  match fpats with
  | [] ->
      plain "FPNil"
  | (f, pat) :: fpats ->
      c "FPCons" [ string_literal f ;
                          translate_pattern pat ;
                          translate_fpats fpats ]

let translate_path (x: path) : expression =
  (* We could use [MkPath], but its definition in Coq involves [rev].
     This is very bad, because using [rev] is bad in the first place
     and because [rev] is itself defined in an inefficient way.
     So, better use [MkPathRev]. *)
  clist "MkPathRev" (List.rev (List.map string_literal x))

let rec translate_anonfun (a : anonfun) : expression =
  match a with
  | AnonFun (x, e) ->
      c "AnonFun" [ string_literal x ;
                          translate_expression e ]
  | AnonFunction bs ->
      c "AnonFunction" [translate_branches bs]

and translate_branch : branch -> expression = function
  | Branch (p, e) ->
      c "Branch" [ translate_pattern p ;
                          translate_expression e ]

and translate_branches (bs: branches) : expression =
  clist "MkBranches" (List.map translate_branch bs)

and translate_fexprs (fs: fexprs) : expression =
  clist "MkFexprs" (List.map translate_fexpr fs)

and translate_fexpr (f, e) =
  pair (string_literal f) (translate_expression e)

and exprs es =
  List.map translate_expression es

and cexprs s es =
  c s (exprs es)

and translate_expression (e: expr) : expression =
  match e with

  | EUnsupported ->
      plain "EUnsupported"

  | ELink e -> plain e

  | EChar c' ->
      c "EChar" [translate_char c']

  (* Path: [x] or [πx] *)
  | EPath x ->
      c "EPath" [translate_path x]

  (* An anonymous function *)
  | EAnonFun a ->
      c "EAnonFun" [translate_anonfun a]

  (* Function application: [e1 e2] *)
  (* Every function is considered unary *)
  | EApp (e1, e2) ->
      c "EApp" [ translate_expression e1 ;
                        translate_expression e2 ]

  (* Tuple construction: [(e1, e2, )] *)
  | ETuple el ->
      clist "EMkTuple" (List.map translate_expression el)

  (* Data constructor application: [A (e)] *)
  (* Every data constructor is considered unary *)
  | EData (a, e) ->
      c "EData" [ string_literal a ;
                         translate_expression e ]

  (* Record construction: [{ fs = es }] *)
  | ERecord fs ->
      c "ERecord" [translate_fexprs fs]

  (* Record update: [{ e and fs = es }] *)
  | ERecordUpdate (er, fs) ->
     c "ERecordUpdate"
              [ translate_expression er ;
                translate_fexprs fs ]

  (* Record access: [ef] *)
  | ERecordAccess (er, field) ->
      c "ERecordAccess" [ translate_expression er ;
                                 string_literal field ]

  (* Strings *)
  | EString s ->
     c "EString" [string_literal (String.escaped s)]

  (* Integer literals *)
  | EInt i ->
     c "EInt" [plain (string_of_int i)]

  (* Polymorphic comparison operators *)

  (* Non-recursive local definition: [let bs in e] *)
  | ELet (bds, e) ->
      c "ELet" [ translate_bindings bds ;
                        translate_expression e ]

  (* Recursive local definition: [let rbs in e] *)
  | ELetRec (rbds, e) ->
      c "ELetRec" [ translate_rec_bindings rbds ;
                    translate_expression e ]

  (* Local module definition: [let module M = me in e] *)
  | ELetModule (name, m, e) ->
      c "ELetModule" [ string_literal name ;
                              translate_module m ;
                              translate_expression e ]

  (* Local [open] directive: [let open me in e] *)
  | ELetOpen (me, e) ->
     c "ELetOpen" [ translate_module me ;
                            translate_expression e ]

  (* Sequence: [e1; e2] *)
  | ESeq (e1, e2) ->
     c "ESeq" [ translate_expression e1 ;
                translate_expression e2 ]

  (* Conditional: [if e then e1] and [if e then e1 else e2] *)
  | EIfThen (e, e1) ->
      c "EIfThen" [ translate_expression e ;
                    translate_expression e1 ]
  | EIfThenElse (e, e1, e2) ->
     c "EIfThenElse" [ translate_expression e ;
                       translate_expression e1 ;
                       translate_expression e2 ]

  (* Pattern matching: [match e and bs] *)
  | EMatch (e, bs) ->
      c "EMatch" [ translate_expression e ;
                   translate_branches bs ]

  (* Loop: [while e do body done] *)
  | EWhile (e1, e2) ->
      c "EWhile" [ translate_expression e1 ;
                   translate_expression e2 ]
  (* Loop: [for x = e1 to e2 do e done] *)
  | EFor (x, e1, e2, e3) ->
      c "EFor" [ string_literal x ;
                 translate_expression e1 ;
                 translate_expression e2 ;
                 translate_expression e3 ]

  (* Runtime assertion: [assert(e)] *)
  | EAssert e ->
      c "EAssert" [translate_expression e]

  | ERef e -> (* of expr *)
      c "ERef" [translate_expression e]

  | EAssertFalse ->
      c "EAssertFalse" []

  | EBoolConj (e1, e2) ->
      cexprs "EBoolConj" [e1; e2]

  | EBoolDisj (e1, e2) ->
      cexprs "EBoolDisj" [e1; e2]

  | EBoolNeg e ->
      cexprs "EBoolNeg" [e]

  | ELoad e ->
      cexprs "ELoad" [e]

  | EStore (e1, e2) ->
      cexprs "EStore" [e1; e2]

  | EIntNeg e ->
      cexprs "EIntNeg" [e]
  | EIntAdd (e1, e2) ->
      cexprs "EIntAdd" [e1; e2]
  | EIntSub (e1, e2) ->
      cexprs "EIntSub" [e1; e2]
  | EIntMul (e1, e2) ->
      cexprs "EIntMul" [e1; e2]
  | EIntDiv (e1, e2) ->
      cexprs "EIntDiv" [e1; e2]
  | EIntMod (e1, e2) ->
      cexprs "EIntMod" [e1; e2]

  | EMaxInt ->
      c "EMaxInt" []
  | EMinInt ->
      c "EMinInt" []

  | EOpPhysEq (e1, e2) ->
      cexprs "EOpPhysEq" [e1; e2]
  | EOpEq (e1, e2) ->
      cexprs "EOpEq" [e1; e2]
  | EOpNe (e1, e2) ->
      cexprs "EOpNe" [e1; e2]
  | EOpLt (e1, e2) ->
      cexprs "EOpLt" [e1; e2]
  | EOpLe (e1, e2) ->
      cexprs "EOpLe" [e1; e2]
  | EOpGt (e1, e2) ->
      cexprs "EOpGt" [e1; e2]
  | EOpGe (e1, e2) ->
      cexprs "EOpGe" [e1; e2]

(* -------------------------------------------------------------------------- *)

(* On bindings translation. *)

and translate_binding  = function
  | BLink s -> plain s
  | Binding (p, e) ->
      c "Binding" [
           translate_pattern p;
           translate_expression e
       ]

and translate_rec_binding = function
  | RecBLink s -> plain s
  | RecBinding (v, a) ->
      c "RecBinding" [
           string_literal v ;
           translate_anonfun a
       ]

and translate_bindings (bs: bindings) : expression =
  clist "MkBindings" (List.map translate_binding bs)

and translate_rec_bindings (rbs: rec_bindings) : expression =
  clist "MkRecBindings" (List.map translate_rec_binding rbs)

(* -------------------------------------------------------------------------- *)

(* On module translation. *)

and translate_sitem : sitem -> expression = function
  (* An auxiliary Coq top-level definition *)
  | ILink name ->
     plain name

  (* A non-recursive toplevel definition [let bs] *)
  | ILet (bindings) ->
     c "ILet" [translate_bindings bindings]

  (* A recursive toplevel definition [let rec rbs] *)
  | ILetRec (rec_bindings) ->
     c "ILetRec" [translate_rec_bindings rec_bindings]

  (* A module definition [M = me] *)
  | IModule (name, mexpr) ->
      c "IModule"
                    [ plain ("\"" ^ name ^ "\"");
                      translate_module mexpr]

  (* An [open] directive [open me] *)
  | IOpen me ->
      c "IOpen" [translate_module me]

  (* An [include] directive [include me] *)
  | IInclude mexpr ->
      c "IInclude" [translate_module mexpr]

and translate_sitems l =
  List.map translate_sitem l

and translate_module = function
  | MUnsupported ->
      plain "MUnsupported"
  | MStruct sitems ->
     clist "MkStruct" (translate_sitems sitems)

  (* Auxiliary top-level Coq definition. *)
  | MLink s -> plain s

  | MPath p -> c "MPath" [translate_path p]
  | MCoercion _ -> assert false

(* -------------------------------------------------------------------------- *)

let definition_of_ast = function
  | OModule m -> "mexpr", translate_module m
  | OExpr e -> "expr", translate_expression e
  | ORecBinding rbd -> "rec_binding", translate_rec_binding rbd
  | OBinding bd -> "binding", translate_binding bd
  | OSItem sitem -> "sitem", translate_sitem sitem
