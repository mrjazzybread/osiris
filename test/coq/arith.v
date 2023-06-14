From osiris Require Import osiris.



Definition Arith : mexpr := (
                              MkStruct [(
                                ILetRec (
                                  RecBiCons (
                                    RecBinding "add"
                                    (
                                      AnonFun "__osiris_anonymous_arg"
                                      (
                                        EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                        (
                                          MkBranches [(
                                            Branch (PVar "x")
                                            (
                                              EAnonFun (
                                                AnonFun
"__osiris_anonymous_arg"
                                                (
                                                  EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                                  (
                                                    MkBranches [(
                                                      Branch (PVar "y")
                                                      (
                                                        EIfThenElse (
                                                          EApp (
                                                            EApp (
                                                              EPath (
                                                                PathDot
(PathBase "Stdlib")
                                                                "="
                                                              )
                                                            )
                                                            (EPath (PathBase
"y"))
                                                          )
                                                          (EInt 0)
                                                        )
                                                        (
                                                          EApp (
                                                            EApp (EPath
(PathBase "mult"))
                                                            (EPath (PathBase
"x"))
                                                          )
                                                          (EInt 1)
                                                        )
                                                        (
                                                          EApp (
                                                            EApp (
                                                              EPath (
                                                                PathDot
(PathBase "Stdlib")
                                                                "+"
                                                              )
                                                            )
                                                            (EInt 1)
                                                          )
                                                          (
                                                            EApp (
                                                              EApp (EPath
(PathBase "add"))
                                                              (EPath
(PathBase "x"))
                                                            )
                                                            (
                                                              EApp (
                                                                EApp (
                                                                  EPath (
                                                                    PathDot
(PathBase "Stdlib")
                                                                    "-"
                                                                  )
                                                                )
                                                                (EPath
(PathBase "y"))
                                                              )
                                                              (EInt 1)
                                                            )
                                                          )
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
                                  (
                                    RecBiCons (
                                      RecBinding "mult"
                                      (
                                        AnonFun "__osiris_anonymous_arg"
                                        (
                                          EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                          (
                                            MkBranches [(
                                              Branch (PVar "x")
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
                                                        Branch (PVar "y")
                                                        (
                                                          EIfThenElse (
                                                            EApp (
                                                              EApp (
                                                                EPath (
                                                                  PathDot
(PathBase "Stdlib")
                                                                  "="
                                                                )
                                                              )
                                                              (EPath
(PathBase "y"))
                                                            )
                                                            (EInt 0)
                                                          )
                                                          (EInt 0)
                                                          (
                                                            EIfThenElse (
                                                              EApp (
                                                                EApp (
                                                                  EPath (
                                                                    PathDot
(PathBase "Stdlib")
                                                                    "="
                                                                  )
                                                                )
                                                                (EPath
(PathBase "y"))
                                                              )
                                                              (EInt 1)
                                                            )
                                                            (EPath (PathBase
"x"))
                                                            (
                                                              EApp (
                                                                EApp (EPath
(PathBase "add"))
                                                                (EPath
(PathBase "x"))
                                                              )
                                                              (
                                                                EApp (
                                                                  EApp (EPath
(PathBase "mult"))
                                                                  (EPath
(PathBase "x"))
                                                                )
                                                                (
                                                                  EApp (
                                                                    EApp (
                                                                      EPath (
                                                                       
PathDot (PathBase "Stdlib")
                                                                        "-"
                                                                      )
                                                                    )
                                                                    (EPath
(PathBase "y"))
                                                                  )
                                                                  (EInt 1)
                                                                )
                                                              )
                                                            )
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
                                    RecBiNil
                                  )
                                )
                              );(
                                ILet (
                                  BiCons (
                                    Binding (PVar "i3")
                                    (
                                      EApp (EApp (EPath (PathBase "add"))
(EInt 1))
                                      (
                                        EApp (EApp (EPath (PathBase "add"))
(EInt 2))
                                        (EInt 0)
                                      )
                                    )
                                  )
                                  BiNil
                                )
                              );(
                                ILet (
                                  BiCons (
                                    Binding (PVar "i17")
                                    (
                                      EApp (
                                        EApp (EPath (PathBase "add"))
                                        (
                                          EApp (EApp (EPath (PathBase
"mult")) (EInt 2))
                                          (EInt 2)
                                        )
                                      )
                                      (
                                        EApp (EApp (EPath (PathBase "add"))
(EInt 1))
                                        (
                                          EApp (EApp (EPath (PathBase
"mult")) (EInt 2))
                                          (
                                            EApp (EApp (EPath (PathBase
"add")) (EInt 4))
                                            (EInt 2)
                                          )
                                        )
                                      )
                                    )
                                  )
                                  BiNil
                                )
                              )]
                           
).
(* Done. *)