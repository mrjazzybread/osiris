open Printf
let map = List.map
open Syntax
open Coq

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

(* Paths. *)

let path (pi : path) =
  (* We could use [MkPath], but its definition in Coq involves [rev].
     This is very bad, because using [rev] is bad in the first place
     and because [rev] is itself defined in an inefficient way.
     So, better use [MkPathRev]. *)
  clist "MkPathRev" (List.rev (map var pi))

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

  | POr (p1, p2) ->
      c "POr" [ pat p1; pat p2 ]

  | PTuple ps ->
      clist "PMkTuple" (map pat ps)

  | PData (d, p) ->
      c "PData" [ data d; pat p ]

  | PRecord fps ->
      c "PRecord" [ fpats fps ]

  | PInt i ->
      c "PInt" [ int i ]

  | PChar cc ->
      c "PChar" [ char cc ]

  | PString s ->
      c "PString" [ string s ]

and fpats fps =
  clist "MkFpats" (map fpat fps)

and fpat (f, p) =
  pair (field f) (pat p)

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec expr (e : expr) =
  match e with

  | ELink x ->
      plain x

  | EUnsupported ->
      c "EUnsupported" []

  | EPath x ->
      c "EPath" [ path x ]

  | EAnonFun a ->
      c "EAnonFun" [ anonfun a ]

  | EApp (e1, e2) ->
      c "EApp" [ expr e1; expr e2 ]

  | ETuple es ->
      clist "EMkTuple" (exprs es)

  | EData (d, e) ->
      c "EData" [ data d; expr e ]

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
      c "ELet" [ bindings bs; expr e ]

  | ELetRec (rbs, e) ->
      c "ELetRec" [ rec_bindings rbs; expr e ]

  | ELetModule (m, me, e) ->
      c "ELetModule" [ var m; mexpr me; expr e ]

  | ELetOpen (me, e) ->
      c "ELetOpen" [ mexpr me; expr e ]

  | ESeq (e1, e2) ->
      c "ESeq" [ expr e1; expr e2 ]

  | EIfThen (e, e1) ->
      c "EIfThen" [ expr e; expr e1 ]

  | EIfThenElse (e, e1, e2) ->
      c "EIfThenElse" [ expr e; expr e1; expr e2 ]

  | EMatch (e, bs) ->
      c "EMatch" [ expr e; branches bs ]

  | EWhile (e1, e2) ->
      c "EWhile" [ expr e1; expr e2 ]

  | EFor (x, e1, e2, e3) ->
      c "EFor" [ var x; expr e1; expr e2; expr e3 ]

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

and anonfun = function
  | AnonFun (x, e) ->
      c "AnonFun" [ var x; expr e ]
  | AnonFunction bs ->
      c "AnonFunction" [ branches bs ]

and branch = function
  | Branch (p, e) ->
      c "Branch" [ pat p; expr e ]

and branches (bs : branches) =
  clist "MkBranches" (map branch bs)

and fexprs (fes : fexprs) =
  clist "MkFexprs" (map fexpr fes)

and fexpr (f, e) =
  pair (field f) (expr e)

and exprs es =
  map expr es

(* -------------------------------------------------------------------------- *)

(* On bindings translation. *)

and binding  = function
  | BLink s -> plain s
  | Binding (p, e) ->
      c "Binding" [
           pat p;
           expr e
       ]

and rec_binding = function
  | RecBLink s -> plain s
  | RecBinding (x, a) ->
      c "RecBinding" [
           var x ;
           anonfun a
       ]

and bindings (bs : bindings) =
  clist "MkBindings" (map binding bs)

and rec_bindings (rbs : rec_bindings) =
  clist "MkRecBindings" (map rec_binding rbs)

(* -------------------------------------------------------------------------- *)

(* On module translation. *)

and structure_item = function
  (* An auxiliary Coq top-level definition *)
  | ILink name ->
     plain name

  (* A non-recursive toplevel definition [let bs] *)
  | ILet bs ->
     c "ILet" [bindings bs]

  (* A recursive toplevel definition [let rec rbs] *)
  | ILetRec rbs ->
     c "ILetRec" [rec_bindings rbs]

  (* A module definition [M = me] *)
  | IModule (name, me) ->
      c "IModule"
                    [ plain ("\"" ^ name ^ "\"");
                      mexpr me]

  (* An [open] directive [open me] *)
  | IOpen me ->
      c "IOpen" [mexpr me]

  (* An [include] directive [include me] *)
  | IInclude me ->
      c "IInclude" [mexpr me]

and structure_items l =
  map structure_item l

and mexpr = function
  | MUnsupported ->
      plain "MUnsupported"
  | MStruct is ->
     clist "MkStruct" (structure_items is)

  (* Auxiliary top-level Coq definition. *)
  | MLink s -> plain s

  | MPath p -> c "MPath" [path p]
  | MCoercion _ -> assert false

(* -------------------------------------------------------------------------- *)

let definition_of_ast = function
  | OModule m -> "mexpr", mexpr m
  | OExpr e -> "expr", expr e
  | ORecBinding rbd -> "rec_binding", rec_binding rbd
  | OBinding bd -> "binding", binding bd
  | OSItem sitem -> "sitem", structure_item sitem
