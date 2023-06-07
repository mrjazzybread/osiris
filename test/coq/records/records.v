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
let is_odd n = (n mod 2) = 0
type nat =
  | O 
  | S of nat 
let rec is_odd' = function | O -> true | S n -> not (is_odd' n) *)

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
(
  MStruct (
    ICons (
      ILet (
        BiCons (
          Binding (PVar "r_elt")
          (
            ERecord (
              FECons "i"
              (EInt 10)
              (FECons "b" (EData "true" (ETuple ENil)) FENil)
            )
          )
        )
        BiNil
      )
    )
    (
      ICons (
        ILet (
          BiCons (
            Binding (PVar "flip")
            (
              EAnonFun (
                AnonFunction (
                   (
                    BrCons (
                      Branch (PVar "r")
                      (
                        ERecordUpdate (EPath (PathBase "r"))
                        (
                          FECons "b"
                          (
                            EApp (EPath (PathDot (PathBase "Stdlib") "not"))
                            (ERecordAccess (EPath (PathBase "r")) "b")
                          )
                          FENil
                        )
                      )
                    )
                    BrNil
                  )
                )
              )
            )
          )
          BiNil
        )
      )
      (
        ICons (
          ILet (
            BiCons (
              Binding (PVar "lily")
              (
                EData "::"
                (
                  ETuple (
                    ECons (EPath (PathBase "r_elt"))
                    (
                      ECons (
                        EData "::"
                        (
                          ETuple (
                            ECons (
                              EApp (EPath (PathBase "flip"))
                              (EPath (PathBase "r_elt"))
                            )
                            (ECons (EData "[]" (ETuple ENil)) ENil)
                          )
                        )
                      )
                      ENil
                    )
                  )
                )
              )
            )
            BiNil
          )
        )
        (
          ICons (
            ILet (
              BiCons (
                Binding (PVar "r_val")
                (
                  EAnonFun (
                    AnonFunction (
                       (
                        BrCons (
                          Branch (PVar "r")
                          (
                            EMatch (ERecordAccess (EPath (PathBase "r")) "b")
                            (
                              BrCons (
                                Branch (PBool true)
                                (
                                  EApp (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
"-"))
                                    (
                                      EApp (
                                        EApp (EPath (PathDot (PathBase
"Stdlib") "*"))
                                        (ERecordAccess (EPath (PathBase "r"))
"i")
                                      )
                                      (EInt 2)
                                    )
                                  )
                                  (EInt 1)
                                )
                              )
                              (
                                BrCons (
                                  Branch (PBool false)
                                  (ERecordAccess (EPath (PathBase "r")) "i")
                                )
                                BrNil
                              )
                            )
                          )
                        )
                        BrNil
                      )
                    )
                  )
                )
              )
              BiNil
            )
          )
          (
            ICons (
              ILet (
                BiCons (
                  Binding (PVar "sum")
                  (
                    EAnonFun (
                      AnonFunction (
                         (
                          BrCons (
                            Branch (PVar "r1")
                            (
                              EAnonFun (
                                AnonFunction (
                                   (
                                    BrCons (
                                      Branch (PVar "r2")
                                      (
                                        EApp (
                                          EApp (EPath (PathDot (PathBase
"Stdlib") "+"))
                                          (
                                            EApp (EPath (PathBase "r_val"))
                                            (EPath (PathBase "r1"))
                                          )
                                        )
                                        (
                                          EApp (EPath (PathBase "r_val"))
                                          (EPath (PathBase "r2"))
                                        )
                                      )
                                    )
                                    BrNil
                                  )
                                )
                              )
                            )
                          )
                          BrNil
                        )
                      )
                    )
                  )
                )
                BiNil
              )
            )
            (
              ICons (
                ILetRec (
                  RecBiCons (
                    RecBinding "is_odd_naive"
                    (
                      AnonFunction (
                         (
                          BrCons (
                            Branch (PVar "n")
                            (
                              ESeq (
                                EAssert (
                                  EApp (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
">="))
                                    (EPath (PathBase "n"))
                                  )
                                  (EInt 0)
                                )
                              )
                              (
                                EIfThenElse (
                                  EApp (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
">"))
                                    (EPath (PathBase "n"))
                                  )
                                  (EInt 1)
                                )
                                (
                                  EApp (EPath (PathBase "is_odd_naive"))
                                  (
                                    EApp (
                                      EApp (EPath (PathDot (PathBase
"Stdlib") "-"))
                                      (EPath (PathBase "n"))
                                    )
                                    (EInt 2)
                                  )
                                )
                                (
                                  EIfThenElse (
                                    EApp (
                                      EApp (EPath (PathDot (PathBase
"Stdlib") "="))
                                      (EPath (PathBase "n"))
                                    )
                                    (EInt 0)
                                  )
                                  (EData "false" (ETuple ENil))
                                  (EData "true" (ETuple ENil))
                                )
                              )
                            )
                          )
                          BrNil
                        )
                      )
                    )
                  )
                  RecBiNil
                )
              )
              (
                ICons (
                  ILet (
                    BiCons (
                      Binding (PVar "is_odd")
                      (
                        EAnonFun (
                          AnonFunction (
                             (
                              BrCons (
                                Branch (PVar "n")
                                (
                                  EApp (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
"="))
                                    (
                                      EApp (
                                        EApp (EPath (PathDot (PathBase
"Stdlib") "mod"))
                                        (EPath (PathBase "n"))
                                      )
                                      (EInt 2)
                                    )
                                  )
                                  (EInt 0)
                                )
                              )
                              BrNil
                            )
                          )
                        )
                      )
                    )
                    BiNil
                  )
                )
                (
                  ICons (
                    ILetRec (
                      RecBiCons (
                        RecBinding "is_odd'"
                        (
                          AnonFunction (
                             (
                              BrCons (
                                Branch (PData "O" (PTuple PNil))
                                (EData "true" (ETuple ENil))
                              )
                              (
                                BrCons (
                                  Branch (
                                    PData "S"
                                    (PTuple (PCons (PVar "n") PNil))
                                  )
                                  (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
"not"))
                                    (
                                      EApp (EPath (PathBase "is_odd'"))
                                      (EPath (PathBase "n"))
                                    )
                                  )
                                )
                                BrNil
                              )
                            )
                          )
                        )
                      )
                      RecBiNil
                    )
                  )
                  INil
                )
              )
            )
          )
        )
      )
    )
 
)
).

