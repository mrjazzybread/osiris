open Printf
let map = List.map
open Syntax
open Coq

(* This module transforms the Osiris AST into the Coq AST. *)

(* Cut marks are inserted by invoking [cut] in several places: anonymous
   functions, recursive let bindings, branches of conditional constructs,
   right-hand sides of [let] expressions and sequences. This may help
   improve the readability of the generated definitions and reduce the
   size of the goals that appear while verifying the code in Coq. *)

(* -------------------------------------------------------------------------- *)

(* Variables, module names, data constructors, and field names are
   represented in Coq as strings. *)

let quote s =
  plain (sprintf "\"%s\"" s)

let var =
  quote

let data =
  quote

let field =
  quote

(* -------------------------------------------------------------------------- *)

(* Integer literals. *)

let int i =
  plain (string_of_int i)

(* -------------------------------------------------------------------------- *)

(* String literals. *)

let string s =
  quote (String.escaped s)

(* -------------------------------------------------------------------------- *)

(* Character literals. *)

let bool b =
  if b then plain "true" else plain "false"

let char (cc : char) =
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
     represented by eight Booleans. *)
  c "Ascii" (map bool [ d0; d1; d2; d3; d4; d5; d6; d7 ])

(* -------------------------------------------------------------------------- *)

(* Patterns. *)

let rec pat (p : pat) =
  match p with

  | PUnsupported ->
      c "PUnsupported" []

  | PAny ->
      c "PAny" []

  | PVar  x ->
      c "PVar" [ var x ]

  | PAlias (p, x) ->
      c "PAlias" [ pat p; var x ]

  | PTuple ps ->
      clist "PTuple" (map pat ps)

  | PData (d, p) ->
      c "PData" [ data d; pat p ]

  | PXData (d, p) ->
      c "PXData" [ data d; pat p ]

  | PRecord fps ->
      c "PRecord" [ fpats fps ]

  | PInt i ->
      c "PInt" [ int i ]

  | PChar cc ->
      c "PChar" [ char cc ]

  | PString s ->
     c "PString" [ string s ]

  | POr (p1, p2) ->
     c "POr" [ pat p1; pat p2 ]

and cpat (cp : cpat) =
  match cp with

  | CVal p ->
     c "CVal" [ pat p ]

  | CExc p ->
     c "CExc" [ pat p ]

  | CEff (p1, p2) ->
     c "CEff" [ pat p1; pat p2 ]

  | COr (p1, p2) ->
     c "COr" [ cpat p1; cpat p2 ]

and fpats fps =
  clist "MkFpats" (map fpat fps)

and fpat (f, p) =
  pair (field f) (pat p)

(* -------------------------------------------------------------------------- *)

(* Coercions. *)

let rec coercion = function
  | CIdentity ->
      c "CIdentity" []
  | CStruct fcs ->
      c "CStruct" [ fcoercions fcs ]

and fcoercions fcs =
  clist "MkFCoercions" (map fcoercion fcs)

and fcoercion (f, co) =
  pair (field f) (coercion co)

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec expr (e : expr) =
  match e with

  | EDecorate (snippet, e) ->
      c "deco" [ string snippet; expr e ]

  | EUnsupported ->
      c "EUnsupported" []

  | EPath pi ->
      clist "EPath" (map var pi)

  | EAnonFun a ->
      c "EAnonFun" [ cut "fun" (anonfun a) ]

  | EApp (e1, e2) ->
      c "EApp" [ expr e1; expr e2 ]

  | ETuple es ->
      clist "ETuple" (exprs es)

  | EData (d, e) ->
      c "EData" [ data d; expr e ]

  | EXData (d, e) ->
     c "EXData" [ data d; expr e ]

  | ERecord fs ->
      c "ERecord" [ fexprs fs ]

  | ERecordUpdate (e, fes) ->
      c "ERecordUpdate" [ expr e; fexprs fes ]

  | ERecordAccess (e, f) ->
      c "ERecordAccess" [ expr e; field f ]

  | EBoolConj (e1, e2) ->
      c "EBoolConj" [ expr e1; expr e2 ]

  | EBoolDisj (e1, e2) ->
      c "EBoolDisj" [ expr e1; expr e2 ]

  | EBoolNeg e ->
      c "EBoolNeg" [ expr e ]

  | EInt i ->
      c "EInt" [ int i ]

  | EMaxInt ->
      c "EMaxInt" []

  | EMinInt ->
      c "EMinInt" []

  | EIntNeg e ->
      c "EIntNeg" [ expr e ]

  | EIntAdd (e1, e2) ->
      c "EIntAdd" [ expr e1; expr e2 ]

  | EIntSub (e1, e2) ->
      c "EIntSub" [ expr e1; expr e2 ]

  | EIntMul (e1, e2) ->
      c "EIntMul" [ expr e1; expr e2 ]

  | EIntDiv (e1, e2) ->
      c "EIntDiv" [ expr e1; expr e2 ]

  | EIntMod (e1, e2) ->
      c "EIntMod" [ expr e1; expr e2 ]

  | EFloat f ->
      c "EFloat" [ plain (sprintf "(%s)%%float" f)]

  | EChar cc ->
      c "EChar" [char cc]

  | EString s ->
      c "EString" [string s]

  | EOpPhysEq (e1, e2) ->
      c "EOpPhysEq" [ expr e1; expr e2 ]

  | EOpEq (e1, e2) ->
      c "EOpEq" [ expr e1; expr e2 ]

  | EOpNe (e1, e2) ->
      c "EOpNe" [ expr e1; expr e2 ]

  | EOpLt (e1, e2) ->
      c "EOpLt" [ expr e1; expr e2 ]

  | EOpLe (e1, e2) ->
      c "EOpLe" [ expr e1; expr e2 ]

  | EOpGt (e1, e2) ->
      c "EOpGt" [ expr e1; expr e2 ]

  | EOpGe (e1, e2) ->
      c "EOpGe" [ expr e1; expr e2 ]

  | ELet (bs, e) ->
      c "ELet" [ bindings bs; cut_expr e ]

  | ELetRec (rbs, e) ->
      c "ELetRec" [ rec_bindings rbs; cut_expr e ]

  | ELetModule (m, me, e) ->
      c "ELetModule" [ var m; mexpr me; cut_expr e ]

  | ELetOpen (me, e) ->
      c "ELetOpen" [ mexpr me; cut_expr e ]

  | ESeq (e1, e2) ->
      c "ESeq" [ expr e1; cut_expr e2 ]

  | EIfThen (e, e1) ->
      c "EIfThen" [ expr e; cut_expr e1 ]

  | EIfThenElse (e, e1, e2) ->
      c "EIfThenElse" [ expr e; cut_expr e1; cut_expr e2 ]

  | EMatch (e, bs) ->
      c "EMatch" [ expr e; branches bs ]

  | ETryWith (e, bs) ->
     c "ETryWith" [ expr e; branches bs ]

  | ERaise e ->
     c "ERaise" [ expr e ]

  | EPerform e ->
     c "EPerform" [ expr e ]

  | EContinue (e1, e2) ->
     c "EContinue" [ expr e1; expr e2 ]

  | EDiscontinue (e1, e2) ->
     c "EDiscontinue" [ expr e1; expr e2 ]

  | EWhile (e1, e2) ->
      c "EWhile" [ expr e1; cut_expr e2 ]

  | EFor (x, e1, e2, e3) ->
      c "EFor" [ var x; expr e1; expr e2; cut_expr e3 ]

  | EAssertFalse ->
      c "EAssertFalse" []

  | EAssert e ->
      c "EAssert" [ expr e ]

  | ERef e ->
      c "ERef" [ expr e ]

  | ELoad e ->
      c "ELoad" [ expr e ]

  | EStore (e1, e2) ->
      c "EStore" [ expr e1; expr e2 ]

(* If [e] carries a decoration, then [cut_expr e] takes care of
   cutting below the decoration so the decoration hides the cut in the
   eyes of the end user. (If we cut above the decoration then the end
   user would see the Coq toplevel definition created by the cut, and
   would not see the decoration until they unfold this definition.) *)

and cut_expr e =
  match e with
  | EDecorate (snippet, e) ->
      c "deco" [ string snippet; cut_expr e ]
  | e ->
      cut "exp" (expr e)

and exprs es =
  map expr es

and anonfun = function
  | AnonFun (x, e) ->
      c "AnonFun" [ var x; expr e ]
  | AnonFunction bs ->
      c "AnonFunction" [ branches bs ]

and branch = function
  | Branch (p, e) ->
      c "Branch" [ cpat p; expr e ]

and branches (bs : branches) =
  cut "branches" (list (map branch bs))

and fexpr = function
  | Fexpr (f, e) ->
    c "Fexpr" [ field f; expr e ]

and fexprs (fes : fexprs) =
  list (map fexpr fes)


(* -------------------------------------------------------------------------- *)

(* Bindings. *)

and binding = function
  | Binding (p, e) ->
      c "Binding" [ pat p; expr e ]

and rec_binding = function
  | RecBinding (x, a) ->
      c "RecBinding" [ var x; anonfun a ]

and bindings (bs : bindings) =
  list (map binding bs)

and rec_bindings (rbs : rec_bindings) =
  cut "bindings" (list (map rec_binding rbs))

(* -------------------------------------------------------------------------- *)

(* Structure items. *)

and structure_item (item : sitem) =
  match item with

  | ILet bs ->
     c "ILet" [ bindings bs ]

  | ILetRec rbs ->
     c "ILetRec" [ rec_bindings rbs ]

  | IModule (m, me) ->
      c "IModule" [ var m; mexpr me]

  | IOpen me ->
      c "IOpen" [ mexpr me ]

  | IInclude me ->
      c "IInclude" [ mexpr me ]

and structure_items items =
  map structure_item items

(* -------------------------------------------------------------------------- *)

(* Module expressions. *)

and mexpr (me : mexpr) =
  match me with

  | MUnsupported ->
      c "MUnsupported" []

  | MPath pi ->
      clist "MPath" (map var pi)

  | MStruct items ->
      clist "MStruct" (structure_items items)

  | MFunctor (x, items) ->
      c "MFunctor" ([ var x ] @ structure_items items)

  | MCoercion (me, co) ->
      c "MCoercion" [ mexpr me; coercion co ]

(* -------------------------------------------------------------------------- *)

(* The main function. *)

let module_expression =
  mexpr
