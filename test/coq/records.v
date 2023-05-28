(* Original file:
type r = {
  i: int ;
  b: bool }
let r_elt : r = { b = true; i = 10 }
let flip r = { r with b = (not r.b) }
let lily = [r_elt; flip r_elt]
let r_val r = match r.b with | true -> (r.i * 2) - 1 | false -> r.i
let sum r1 r2 = (r_val r1) + (r_val r2)
let rec is_odd_naive n =
  assert (n >= 0);
  if n > 1 then is_odd_naive (n - 2) else if n = 0 then false else true
let is_odd n = (n mod 2) = 0 *)

(* Converting a single CMT file for [Records]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
From osiris Require Import base.
From osiris.lang Require Import lang.

From osiris.libs Require Import Stdlib.


(* Generated code: *)
Definition Records : mexpr := 
  MkStruct [ 
ILet (
  BiCons
    (Binding (PVar "r_elt")
      (ERecord (FECons "i" (EInt 10) (FECons "b" (EData "true" (ETuple ENil))
FENil)))) $
    BiNil)
;
ILet (
  BiCons
    (Binding (PVar "flip")
      (EAnonFun (AnonFun1Var "r" (ERecordUpdate (EVar "r") (FECons "b" (EApp
(EMkPath ["Stdlib";"not"]) (ERecordAccess (EVar "r") "b")) FENil))))) $
    BiNil)
;
ILet (
  BiCons
    (Binding (PVar "lily")
      (EData "::" (ETuple (ECons (EVar "r_elt") (ECons (EData "::" (ETuple
(ECons (EApp (EVar "flip") (EVar "r_elt")) (ECons (EData "[]" (ETuple ENil))
ENil)))) ENil))))) $
    BiNil)
;
ILet (
  BiCons
    (Binding (PVar "r_val")
      (EAnonFun (AnonFun1Var "r" (EMatch (ERecordAccess (EVar "r") "b")
(BrCons (Branch (PBool true) (EApp (EApp (EMkPath ["Stdlib";"-"]) (EApp (EApp
(EMkPath ["Stdlib";"*"]) (ERecordAccess (EVar "r") "i")) (EInt 2))) (EInt
1))) (BrCons (Branch (PBool false) (ERecordAccess (EVar "r") "i"))
BrNil)))))) $
    BiNil)
;
ILet (
  BiCons
    (Binding (PVar "sum")
      (EAnonFun (AnonFun1Var "r1" (EAnonFun (AnonFun1Var "r2" (EApp (EApp
(EMkPath ["Stdlib";"+"]) (EApp (EVar "r_val") (EVar "r1"))) (EApp (EVar
"r_val") (EVar "r2")))))))) $
    BiNil)
;
ILetRec (
  RecBiCons
    (RecBinding "is_odd_naive" $
      (AnonFun1Var "n" (ESeq (EAssert (EApp (EApp (EMkPath ["Stdlib";">="])
(EVar "n")) (EInt 0))) (EIfThenElse (EApp (EApp (EMkPath ["Stdlib";">"])
(EVar "n")) (EInt 1)) (EApp (EVar "is_odd_naive") (EApp (EApp (EMkPath
["Stdlib";"-"]) (EVar "n")) (EInt 2))) (EIfThenElse (EApp (EApp (EMkPath
["Stdlib";"="]) (EVar "n")) (EInt 0)) (EData "false" (ETuple ENil)) (EData
"true" (ETuple ENil))))))) $
    RecBiNil)
;
ILet (
  BiCons
    (Binding (PVar "is_odd")
      (EAnonFun (AnonFun1Var "n" (EApp (EApp (EMkPath ["Stdlib";"="]) (EApp
(EApp (EMkPath ["Stdlib";"mod"]) (EVar "n")) (EInt 2))) (EInt 0))))) $
   
BiNil)
 ].

