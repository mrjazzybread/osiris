From osiris Require Import osiris.



Definition Records : mexpr := (
                                MkStruct [(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "r_elt")
                                      (
                                        ERecord (
                                          FECons "i"
                                          (EInt 10)
                                          (FECons "b" (EConstant "true")
FENil)
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "flip")
                                      (
                                        EAnonFun (
                                          AnonFun "__osiris_anonymous_arg"
                                          (
                                            EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                            (
                                              MkBranches [(
                                                Branch (PVar "r")
                                                (
                                                  ERecordUpdate (EPath
(PathBase "r"))
                                                  (
                                                    FECons "b"
                                                    (
                                                      EApp (
                                                        EPath (PathDot
(PathBase "Stdlib") "not")
                                                      )
                                                      (ERecordAccess (EPath
(PathBase "r")) "b")
                                                    )
                                                    FENil
                                                  )
                                                )
                                              )]
                                            )
                                          )
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "lily")
                                      (
                                        EData "::"
                                        (
                                          EMkTuple [(EPath (PathBase
"r_elt"));(
                                            EData "::"
                                            (
                                              EMkTuple [(
                                                EApp (EPath (PathBase
"flip"))
                                                (EPath (PathBase "r_elt"))
                                              );(EData "[]" (EMkTuple[]))]
                                            )
                                          )]
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "r_val")
                                      (
                                        EAnonFun (
                                          AnonFun "__osiris_anonymous_arg"
                                          (
                                            EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                            (
                                              MkBranches [(
                                                Branch (PVar "r")
                                                (
                                                  EMatch (ERecordAccess
(EPath (PathBase "r")) "b")
                                                  (
                                                    MkBranches [(
                                                      Branch (PData "true"
PUnit)
                                                      (
                                                        EApp (
                                                          EApp (
                                                            EPath (PathDot
(PathBase "Stdlib") "-")
                                                          )
                                                          (
                                                            EApp (
                                                              EApp (
                                                                EPath (
                                                                  PathDot
(PathBase "Stdlib")
                                                                  "*"
                                                                )
                                                              )
                                                              (
                                                                ERecordAccess
(EPath (PathBase "r"))
                                                                "i"
                                                              )
                                                            )
                                                            (EInt 2)
                                                          )
                                                        )
                                                        (EInt 1)
                                                      )
                                                    );(
                                                      Branch (PData "false"
PUnit)
                                                      (ERecordAccess (EPath
(PathBase "r")) "i")
                                                    )]
                                                  )
                                                )
                                              )]
                                            )
                                          )
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "sum")
                                      (
                                        EAnonFun (
                                          AnonFun "__osiris_anonymous_arg"
                                          (
                                            EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                            (
                                              MkBranches [(
                                                Branch (PVar "r1")
                                                (
                                                  EAnonFun (
                                                    AnonFun
"__osiris_anonymous_arg"
                                                    (
                                                      EMatch (
                                                        EPath (PathBase
"__osiris_anonymous_arg")
                                                      )
                                                      (
                                                        MkBranches [(
                                                          Branch (PVar "r2")
                                                          (
                                                            EApp (
                                                              EApp (
                                                                EPath (
                                                                  PathDot
(PathBase "Stdlib")
                                                                  "+"
                                                                )
                                                              )
                                                              (
                                                                EApp (EPath
(PathBase "r_val"))
                                                                (EPath
(PathBase "r1"))
                                                              )
                                                            )
                                                            (
                                                              EApp (EPath
(PathBase "r_val"))
                                                              (EPath
(PathBase "r2"))
                                                            )
                                                          )
                                                        )]
                                                      )
                                                    )
                                                  )
                                                )
                                              )]
                                            )
                                          )
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILetRec (
                                    RecBiCons (
                                      RecBinding "is_odd_naive"
                                      (
                                        AnonFun "__osiris_anonymous_arg"
                                        (
                                          EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                          (
                                            MkBranches [(
                                              Branch (PVar "n")
                                              (
                                                ESeq (
                                                  EAssert (
                                                    EApp (
                                                      EApp (
                                                        EPath (PathDot
(PathBase "Stdlib") ">=")
                                                      )
                                                      (EPath (PathBase "n"))
                                                    )
                                                    (EInt 0)
                                                  )
                                                )
                                                (
                                                  EIfThenElse (
                                                    EApp (
                                                      EApp (EPath (PathDot
(PathBase "Stdlib") ">"))
                                                      (EPath (PathBase "n"))
                                                    )
                                                    (EInt 1)
                                                  )
                                                  (
                                                    EApp (EPath (PathBase
"is_odd_naive"))
                                                    (
                                                      EApp (
                                                        EApp (
                                                          EPath (PathDot
(PathBase "Stdlib") "-")
                                                        )
                                                        (EPath (PathBase
"n"))
                                                      )
                                                      (EInt 2)
                                                    )
                                                  )
                                                  (
                                                    EIfThenElse (
                                                      EApp (
                                                        EApp (
                                                          EPath (PathDot
(PathBase "Stdlib") "=")
                                                        )
                                                        (EPath (PathBase
"n"))
                                                      )
                                                      (EInt 0)
                                                    )
                                                    (EConstant "false")
                                                    (EConstant "true")
                                                  )
                                                )
                                              )
                                            )]
                                          )
                                        )
                                      )
                                    )
                                    RecBiNil
                                  )
                                );(
                                  ILet (
                                    BiCons (
                                      Binding (PVar "is_odd")
                                      (
                                        EAnonFun (
                                          AnonFun "__osiris_anonymous_arg"
                                          (
                                            EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                            (
                                              MkBranches [(
                                                Branch (PVar "n")
                                                (
                                                  EApp (
                                                    EApp (EPath (PathDot
(PathBase "Stdlib") "="))
                                                    (
                                                      EApp (
                                                        EApp (
                                                          EPath (PathDot
(PathBase "Stdlib") "mod")
                                                        )
                                                        (EPath (PathBase
"n"))
                                                      )
                                                      (EInt 2)
                                                    )
                                                  )
                                                  (EInt 0)
                                                )
                                              )]
                                            )
                                          )
                                        )
                                      )
                                    )
                                    BiNil
                                  )
                                );(
                                  ILetRec (
                                    RecBiCons (
                                      RecBinding "is_odd'"
                                      (
                                        AnonFun "__osiris_anonymous_arg"
                                        (
                                          EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                          (
                                            MkBranches [(
                                              Branch (PData "O" PUnit)
                                              (EConstant "true")
                                            );(
                                              Branch (PData "S" (PMkTuple
[(PVar "n")]))
                                              (
                                                EApp (EPath (PathDot
(PathBase "Stdlib") "not"))
                                                (
                                                  EApp (EPath (PathBase
"is_odd'"))
                                                  (EPath (PathBase "n"))
                                                )
                                              )
                                            )]
                                          )
                                        )
                                      )
                                    )
                                    RecBiNil
                                  )
                                )]
                             
).
(* Done. *)