From osiris Require Import osiris.



Definition _Stateful : mexpr :=
(
  MkStruct [(
    IModule "Counter"
    (
      MkStruct [(
        ILet (
          BiCons (
            Binding (PVar "c")
            (EApp (EPath (MkPath ["Stdlib";"ref"])) (EInt 0))
          )
          BiNil
        )
      );(
        ILet (
          BiCons (
            Binding (PVar "incr")
            (
              EAnonFun (
                AnonFun "__osiris_anonymous_arg"
                (
                  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                  (
                    MkBranches [(
                      Branch (PData "()" (PTuple PNil))
                      (
                        EApp (
                          EApp (EPath (MkPath ["Stdlib";":="]))
                          (EPath (MkPath ["c"]))
                        )
                        (
                          EApp (
                            EApp (EPath (MkPath ["Stdlib";"+"]))
                            (
                              EApp (EPath (MkPath ["Stdlib";"!"]))
                              (EPath (MkPath ["c"]))
                            )
                          )
                          (EInt 1)
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
            Binding (PVar "set")
            (
              EAnonFun (
                AnonFun "__osiris_anonymous_arg"
                (
                  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                  (
                    MkBranches [(
                      Branch (PVar "v")
                      (
                        ESeq (
                          EAssert (
                            EApp (
                              EApp (EPath (MkPath ["Stdlib";"<="]))
                              (
                                EApp (EPath (MkPath ["Stdlib";"!"]))
                                (EPath (MkPath ["c"]))
                              )
                            )
                            (EPath (MkPath ["v"]))
                          )
                        )
                        (
                          EApp (
                            EApp (EPath (MkPath ["Stdlib";":="]))
                            (EPath (MkPath ["c"]))
                          )
                          (EPath (MkPath ["v"]))
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
            Binding (PVar "get")
            (
              EAnonFun (
                AnonFun "__osiris_anonymous_arg"
                (
                  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                  (
                    MkBranches [(
                      Branch (PData "()" (PTuple PNil))
                      (
                        EApp (EPath (MkPath ["Stdlib";"!"]))
                        (EPath (MkPath ["c"]))
                      )
                    )]
                  )
                )
              )
            )
          )
          BiNil
        )
      )]
    )
 
)]
).

(* Done. *)