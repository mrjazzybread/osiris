From osiris Require Import osiris.



Definition _Stateless_uc : mexpr :=
(
  MkStruct [(
    IOpen (MkPath ["CounterExamples";"Stateless"])
  );(
    ILet (
      BiCons (
        Binding (PVar "do2")
        (
          EAnonFun (
            AnonFun "__osiris_anonymous_arg"
            (
              EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
              (
                MkBranches [(
                  Branch (PAlias PAny "f")
                  (
                    EAnonFun (
                      AnonFun "__osiris_anonymous_arg"
                      (
                        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                        (
                          MkBranches [(
                            Branch (PAlias PAny "a")
                            (
                              EMkTuple [(
                                EApp (EPath (MkPath ["f"]))
                                (EPath (MkPath ["a"]))
                              );(
                                EApp (EPath (MkPath ["f"]))
                                (EPath (MkPath ["a"]))
                              )]
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
    ILet (
      BiCons (
        Binding (PVar "count_for")
        (
          EAnonFun (
            AnonFun "__osiris_anonymous_arg"
            (
              EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
              (
                MkBranches [(
                  Branch (PVar "n")
                  (
                    ELet (
                      BiCons (
                        Binding (PMkTuple [(PVar "c");(PVar "c'")])
                        (
                          EApp (
                            EApp (EPath (MkPath ["do2"]))
                            (EPath (MkPath ["Counter";"make"]))
                          )
                          (EData "()" (EMkTuple[]))
                        )
                      )
                      BiNil
                    )
                    (
                      ESeq (
                        EApp (
                          EApp (EPath (MkPath ["Counter";"set"]))
                          (EPath (MkPath ["c'"]))
                        )
                        (EPath (MkPath ["n"]))
                      )
                      (
                        ESeq (
                          EFor "i"
                          (EInt 1)
                          (EPath (MkPath ["n"]))
                          (
                            ESeq (
                              EApp (EPath (MkPath ["Counter";"incr"]))
                              (EPath (MkPath ["c"]))
                            )
                            (
                              EApp (
                                EApp (EPath (MkPath ["Counter";"set"]))
                                (EPath (MkPath ["c'"]))
                              )
                              (
                                EApp (
                                  EApp (EPath (MkPath ["+"]))
                                  (EPath (MkPath ["n"]))
                                )
                                (EPath (MkPath ["i"]))
                              )
                            )
                          )
                        )
                        (
                          ESeq (
                            EAssert (
                              EApp (
                                EApp (EPath (MkPath ["="]))
                                (
                                  EApp (
                                    EApp (EPath (MkPath ["-"]))
                                    (
                                      EApp (EPath (MkPath ["Counter";"get"]))
                                      (EPath (MkPath ["c'"]))
                                    )
                                  )
                                  (
                                    EApp (EPath (MkPath ["Counter";"get"]))
                                    (EPath (MkPath ["c"]))
                                  )
                                )
                              )
                              (EPath (MkPath ["n"]))
                            )
                          )
                          (
                            EApp (EPath (MkPath ["Counter";"get"]))
                            (EPath (MkPath ["c"]))
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
      )
      BiNil
    )
  );(
    ILet (
      BiCons (
        Binding (PVar "count_rec")
        (
          EAnonFun (
            AnonFun "__osiris_anonymous_arg"
            (
              EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
              (
                MkBranches [(
                  Branch (PVar "n")
                  (
                    ELet (
                      BiCons (
                        Binding (PVar "c")
                        (
                          EApp (EPath (MkPath ["Counter";"make"]))
                          (EData "()" (EMkTuple[]))
                        )
                      )
                      BiNil
                    )
                    (
                      ELetRec (
                        RecBiCons (
                          RecBinding "aux"
                          (
                            AnonFun "__osiris_anonymous_arg"
                            (
                              EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                              (
                                MkBranches [(
                                  Branch (PVar "i")
                                  (
                                    EMatch (
                                      EAssert (
                                        EApp (EApp (EPath (MkPath ["<="])) (EInt 0))
                                        (EPath (MkPath ["i"]))
                                      )
                                    )
                                    (
                                      MkBranches [(
                                        Branch (PData "()" (PTuple PNil))
                                        (
                                          EMatch (EPath (MkPath ["i"]))
                                          (
                                            MkBranches [(
                                              Branch (PInt 0)
                                              (
                                                EApp (EPath (MkPath ["Counter";"get"]))
                                                (EPath (MkPath ["c"]))
                                              )
                                            );(
                                              Branch PAny
                                              (
                                                ESeq (
                                                  EApp (EPath (MkPath ["Counter";"incr"]))
                                                  (EPath (MkPath ["c"]))
                                                )
                                                (
                                                  EApp (EPath (MkPath ["aux"]))
                                                  (
                                                    EApp (
                                                      EApp (EPath (MkPath ["-"]))
                                                      (EPath (MkPath ["i"]))
                                                    )
                                                    (EInt 1)
                                                  )
                                                )
                                              )
                                            )]
                                          )
                                        )
                                      )]
                                    )
                                  )
                                )]
                              )
                            )
                          )
                        )
                        RecBiNil
                      )
                      (
                        EApp (EPath (MkPath ["aux"]))
                        (EPath (MkPath ["n"]))
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
    ILet (
      BiCons (
        Binding (PData "()" (PTuple PNil))
        (
          EAssert (
            EApp (EApp (EPath (MkPath ["="])) (EInt 2))
            (EApp (EPath (MkPath ["count_for"])) (EInt 2))
          )
        )
      )
      BiNil
    )
  );(
    ILet (
      BiCons (
        Binding (PData "()" (PTuple PNil))
        (
          EAssert (
            EApp (EApp (EPath (MkPath ["="])) (EInt 2))
            (EApp (EPath (MkPath ["count_rec"])) (EInt 2))
          )
        )
      )
      BiNil
    )
  )]
).

(* Done. *)