(* Original file:
let rec add x y = if y = 0 then mult x 1 else 1 + (add x (y - 1))
and mult x y =
  if y = 0 then 0 else if y = 1 then x else add x (mult x (y - 1))
let i3 = add 1 (add 2 0)
let i17 = add (mult 2 2) (add 1 (mult 2 (add 4 2))) *)

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
(
  MStruct (
    ICons (
      ILetRec (
        RecBiCons (
          RecBinding "add"
          (
            AnonFunction (
               (
                BrCons (
                  Branch (PVar "x")
                  (
                    EAnonFun (
                      AnonFunction (
                         (
                          BrCons (
                            Branch (PVar "y")
                            (
                              EIfThenElse (
                                EApp (
                                  EApp (EPath (PathDot (PathBase "Stdlib")
"="))
                                  (EPath (PathBase "y"))
                                )
                                (EInt 0)
                              )
                              (
                                EApp (
                                  EApp (EPath (PathBase "mult"))
                                  (EPath (PathBase "x"))
                                )
                                (EInt 1)
                              )
                              (
                                EApp (
                                  EApp (EPath (PathDot (PathBase "Stdlib")
"+"))
                                  (EInt 1)
                                )
                                (
                                  EApp (
                                    EApp (EPath (PathBase "add"))
                                    (EPath (PathBase "x"))
                                  )
                                  (
                                    EApp (
                                      EApp (EPath (PathDot (PathBase
"Stdlib") "-"))
                                      (EPath (PathBase "y"))
                                    )
                                    (EInt 1)
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
                BrNil
              )
            )
          )
        )
        (
          RecBiCons (
            RecBinding "mult"
            (
              AnonFunction (
                 (
                  BrCons (
                    Branch (PVar "x")
                    (
                      EAnonFun (
                        AnonFunction (
                           (
                            BrCons (
                              Branch (PVar "y")
                              (
                                EIfThenElse (
                                  EApp (
                                    EApp (EPath (PathDot (PathBase "Stdlib")
"="))
                                    (EPath (PathBase "y"))
                                  )
                                  (EInt 0)
                                )
                                (EInt 0)
                                (
                                  EIfThenElse (
                                    EApp (
                                      EApp (EPath (PathDot (PathBase
"Stdlib") "="))
                                      (EPath (PathBase "y"))
                                    )
                                    (EInt 1)
                                  )
                                  (EPath (PathBase "x"))
                                  (
                                    EApp (
                                      EApp (EPath (PathBase "add"))
                                      (EPath (PathBase "x"))
                                    )
                                    (
                                      EApp (
                                        EApp (EPath (PathBase "mult"))
                                        (EPath (PathBase "x"))
                                      )
                                      (
                                        EApp (
                                          EApp (EPath (PathDot (PathBase
"Stdlib") "-"))
                                          (EPath (PathBase "y"))
                                        )
                                        (EInt 1)
                                      )
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
                  BrNil
                )
              )
            )
          )
          RecBiNil
        )
      )
    )
    (
      ICons (
        ILet (
          BiCons (
            Binding (PVar "i3")
            (
              EApp (EApp (EPath (PathBase "add")) (EInt 1))
              (
                EApp (EApp (EPath (PathBase "add")) (EInt 2))
                (EInt 0)
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
              Binding (PVar "i17")
              (
                EApp (
                  EApp (EPath (PathBase "add"))
                  (
                    EApp (EApp (EPath (PathBase "mult")) (EInt 2))
                    (EInt 2)
                  )
                )
                (
                  EApp (EApp (EPath (PathBase "add")) (EInt 1))
                  (
                    EApp (EApp (EPath (PathBase "mult")) (EInt 2))
                    (
                      EApp (EApp (EPath (PathBase "add")) (EInt 4))
                      (EInt 2)
                    )
                  )
                )
              )
            )
            BiNil
          )
        )
        INil
      )
    )
 
)
).

