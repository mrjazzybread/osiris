From osiris Require Import osiris.



Definition _Stateful_uc : mexpr :=
(
  MkStruct [(
    IOpen (MkPath ["CounterExamples";"Stateful"])
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
                    ESeq (
                      EAssert (
                        EApp (
                          EApp (EPath (MkPath ["Stdlib";"="]))
                          (
                            EApp (
                              EPath (
                                MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                              )
                            )
                            (EData "()" (EMkTuple[]))
                          )
                        )
                        (EInt 0)
                      )
                    )
                    (
                      ESeq (
                        EFor "_for"
                        (EInt 1)
                        (EPath (MkPath ["n"]))
                        (
                          EApp (
                            EPath (
                              MkPath
["CounterExamples";"Stateful";"Counter";"incr"]
                            )
                          )
                          (EData "()" (EMkTuple[]))
                        )
                      )
                      (
                        EApp (
                          EPath (
                            MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                          )
                        )
                        (EData "()" (EMkTuple[]))
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
        Binding (PVar "count_for'")
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
                        Binding (PVar "i")
                        (
                          EApp (
                            EPath (
                              MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                            )
                          )
                          (EData "()" (EMkTuple[]))
                        )
                      )
                      BiNil
                    )
                    (
                      ESeq (
                        EFor "_for"
                        (EInt 1)
                        (EPath (MkPath ["n"]))
                        (
                          EApp (
                            EPath (
                              MkPath
["CounterExamples";"Stateful";"Counter";"incr"]
                            )
                          )
                          (EData "()" (EMkTuple[]))
                        )
                      )
                      (
                        EApp (
                          EApp (EPath (MkPath ["Stdlib";"-"]))
                          (
                            EApp (
                              EPath (
                                MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                              )
                            )
                            (EData "()" (EMkTuple[]))
                          )
                        )
                        (EPath (MkPath ["i"]))
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
                        Binding (PVar "i")
                        (
                          EApp (
                            EPath (
                              MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                            )
                          )
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
                              EMatch (EPath (MkPath
["__osiris_anonymous_arg"]))
                              (
                                MkBranches [(
                                  Branch (PVar "j")
                                  (
                                    EMatch (
                                      EAssert (
                                        EApp (
                                          EApp (EPath (MkPath
["Stdlib";"<="]))
                                          (EInt 0)
                                        )
                                        (EPath (MkPath ["j"]))
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
                                                EApp (
                                                  EApp (EPath (MkPath
["Stdlib";"-"]))
                                                  (
                                                    EApp (
                                                      EPath (
                                                        MkPath
["CounterExamples";"Stateful";"Counter";"get"]
                                                      )
                                                    )
                                                    (EData "()" (EMkTuple[]))
                                                  )
                                                )
                                                (EPath (MkPath ["i"]))
                                              )
                                            );(
                                              Branch PAny
                                              (
                                                ESeq (
                                                  EApp (
                                                    EPath (
                                                      MkPath
["CounterExamples";"Stateful";"Counter";"incr"]
                                                    )
                                                  )
                                                  (EData "()" (EMkTuple[]))
                                                )
                                                (
                                                  EApp (EPath (MkPath
["aux"]))
                                                  (
                                                    EApp (
                                                      EApp (EPath (MkPath
["Stdlib";"-"]))
                                                      (EPath (MkPath ["j"]))
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
            EApp (
              EApp (EPath (MkPath ["Stdlib";"="]))
              (EInt 2)
            )
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
            EApp (
              EApp (EPath (MkPath ["Stdlib";"="]))
              (EInt 2)
            )
            (EApp (EPath (MkPath ["count_for'"])) (EInt 2))
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
            EApp (
              EApp (EPath (MkPath ["Stdlib";"="]))
              (EInt 2)
            )
            (EApp (EPath (MkPath ["count_rec"])) (EInt 2))
          )
        )
      )
      BiNil
    )
 
)]
).

(* Done. *)