(* Original file:
let add x y =
  let z = y in
  let (t, v) = let t = z in let z = t in let t = 0 * z in (x, t) in
  t + (v + z)
let rec mult x y =
  if y = 0
  then 0
  else
    if y < 0
    then - (mult x (- y))
    else (assert (0 < y); x + (mult x (y - 1))) *)

(* Converting a single CMT file for [Arith]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
From osiris Require Import base.
From osiris.lang Require Import lang.

From osiris.libs Require Import Stdlib.


(* Generated code: *)
Definition Arith : mexpr := 
  MkStruct [ 
ILet (
  BiCons
    (Binding (PVar "add")
      (EFun1Var "x" $
      EFun1Var "y" $
      ELet
        (BiCons
          (Binding (PVar "z") (EVar "y")) $
        BiNil) $
      ELet
        (BiCons
          (Binding (PTuple (PCons (PVar "t") (PCons (PVar "v") PNil))) (ELet
            (BiCons
              (Binding (PVar "t") (EVar "z")) $
            BiNil) $
          ELet
            (BiCons
              (Binding (PVar "z") (EVar "t")) $
            BiNil) $
          ELet
            (BiCons
              (Binding (PVar "t") (EApp (EApp (EMkPath ["Stdlib";"*"]) (EInt
0)) (EVar "z"))) $
            BiNil) $
          ETuple (ECons (EVar "x") (ECons (EVar "t") ENil)))) $
        BiNil) $
      EApp (EApp (EMkPath ["Stdlib";"+"]) (EVar "t")) (EApp (EApp (EMkPath
["Stdlib";"+"]) (EVar "v")) (EVar "z")))) $
    BiNil)
;
ILetRec (
  RecBiCons
    (RecBinding "mult" $
      AnonFun "x"
      (EFun1Var "y" $
      EIfThenElse (EApp (EApp (EMkPath ["Stdlib";"="]) (EVar "y")) (EInt 0))
(EInt 0) (EIfThenElse (EApp (EApp (EMkPath ["Stdlib";"<"]) (EVar "y")) (EInt
0)) (EApp (EMkPath ["Stdlib";"~-"]) (EApp (EApp (EVar "mult") (EVar "x"))
(EApp (EMkPath ["Stdlib";"~-"]) (EVar "y")))) (ESeq (EAssert (EApp (EApp
(EMkPath ["Stdlib";"<"]) (EInt 0)) (EVar "y"))) (EApp (EApp (EMkPath
["Stdlib";"+"]) (EVar "x")) (EApp (EApp (EVar "mult") (EVar "x")) (EApp (EApp
(EMkPath ["Stdlib";"-"]) (EVar "y")) (EInt 1)))))))) $
   
RecBiNil)
 ].

(* END. *)