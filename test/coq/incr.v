(* Original file:
let new_counter () =
  let c = ref 0 in let upd i = c := i in let get () = !c in (get, upd)
let _ =
  let res = new_counter () in
  let get = fst res in
  let upd = snd res in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res
let _test =
  let (get, upd) = new_counter () in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res *)

(* Converting a single CMT file for [Incr]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
From osiris Require Import base.
From osiris.lang Require Import lang.

From osiris.libs Require Import Stdlib.


(* Generated code: *)
Definition Incr : mexpr := 
  
(MStruct (ICons (ILet (BiCons (Binding (PVar "new_counter") (EAnonFun
(AnonFun1Pat PUnit (ELet (BiCons (Binding (PVar "c") (EApp (EPath (PathDot
(PathBase "Stdlib") "ref")) (EInt 0))) (BiNil)) (ELet (BiCons (Binding (PVar
"upd") (EAnonFun (AnonFun1Pat (PVar "i") (EApp (EApp (EPath (PathDot
(PathBase "Stdlib") ":=")) (EPath (PathBase "c"))) (EPath (PathBase "i"))))))
(BiNil)) (ELet (BiCons (Binding (PVar "get") (EAnonFun (AnonFun1Pat PUnit
(EApp (EPath (PathDot (PathBase "Stdlib") "!")) (EPath (PathBase "c"))))))
(BiNil)) (ETuple (ECons (EPath (PathBase "get")) (ECons (EPath (PathBase
"upd")) ENil))))))))) (BiNil))) (ICons (ILet (BiCons (Binding PAny (ELet
(BiCons (Binding (PVar "res") (EApp (EPath (PathBase "new_counter")) EUnit))
(BiNil)) (ELet (BiCons (Binding (PVar "get") (EApp (EPath (PathDot (PathBase
"Stdlib") "fst")) (EPath (PathBase "res")))) (BiNil)) (ELet (BiCons (Binding
(PVar "upd") (EApp (EPath (PathDot (PathBase "Stdlib") "snd")) (EPath
(PathBase "res")))) (BiNil)) (ELet (BiCons (Binding (PVar "c") (EApp (EPath
(PathBase "get")) EUnit)) (BiNil)) (EMatch (EApp (EPath (PathBase "upd"))
(EInt 13)) (BrCons (Branch PUnit (ELet (BiCons (Binding (PVar "res") (EApp
(EApp (EPath (PathDot (PathBase "Stdlib") "-")) (EApp (EPath (PathBase
"get")) EUnit)) (EPath (PathBase "c")))) (BiNil)) (EPath (PathBase "res"))))
BrNil))))))) (BiNil))) (ICons (ILet (BiCons (Binding (PVar "_test") (ELet
(BiCons (Binding (PTuple (PCons (PVar "get") (PCons (PVar "upd") PNil)))
(EApp (EPath (PathBase "new_counter")) EUnit)) (BiNil)) (ELet (BiCons
(Binding (PVar "c") (EApp (EPath (PathBase "get")) EUnit)) (BiNil)) (EMatch
(EApp (EPath (PathBase "upd")) (EInt 13)) (BrCons (Branch PUnit (ELet (BiCons
(Binding (PVar "res") (EApp (EApp (EPath (PathDot (PathBase "Stdlib") "-"))
(EApp (EPath (PathBase "get")) EUnit)) (EPath (PathBase "c")))) (BiNil))
(EPath (PathBase "res")))) BrNil))))) (BiNil)))
(INil))))).

