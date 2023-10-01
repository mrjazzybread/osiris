From osiris Require Import osiris.



Definition __osiris__reservedsplit_all_sitem2 : binding :=
(
  Binding (PVar "new_counter")
  (
    EAnonFun (
      AnonFun "__osiris_anonymous_arg"
      (
        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
        (
          MkBranches [(
            Branch (PData "()" (PTuple PNil))
            (
              ELet (
                BiCons (
                  Binding (PVar "c")
                  (EApp (EPath (MkPath ["ref"])) (EInt 0))
                )
                BiNil
              )
              (
                ELet (
                  BiCons (
                    Binding (PVar "upd")
                    (
                      EAnonFun (
                        AnonFun "__osiris_anonymous_arg"
                        (
                          EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                          (
                            MkBranches [(
                              Branch (PVar "i")
                              (
                                EApp (
                                  EApp (EPath (MkPath [":="]))
                                  (EPath (MkPath ["c"]))
                                )
                                (EPath (MkPath ["i"]))
                              )
                            )]
                          )
                        )
                      )
                    )
                  )
                  BiNil
                )
                (
                  ELet (
                    BiCons (
                      Binding (PVar "get")
                      (
                        EAnonFun (
                          AnonFun "__osiris_anonymous_arg"
                          (
                            EMatch (EPath (MkPath
["__osiris_anonymous_arg"]))
                            (
                              MkBranches [(
                                Branch (PData "()" (PTuple PNil))
                                (
                                  EApp (EPath (MkPath ["!"]))
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
                  (
                    EMkTuple [(EPath (MkPath ["get"]));(
                      EPath (MkPath ["upd"])
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
).
Definition __osiris__reservedsplit_all_module1 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem2
    BiNil
  )
).
Definition __osiris__reservedsplit_all_sitem4 : binding :=
(
  Binding PAny
  (
    ELet (
      BiCons (
        Binding (PVar "res")
        (
          EApp (EPath (MkPath ["new_counter"]))
          (EData "()" (EMkTuple[]))
        )
      )
      BiNil
    )
    (
      ELet (
        BiCons (
          Binding (PVar "get")
          (
            EApp (EPath (MkPath ["fst"]))
            (EPath (MkPath ["res"]))
          )
        )
        BiNil
      )
      (
        ELet (
          BiCons (
            Binding (PVar "upd")
            (
              EApp (EPath (MkPath ["snd"]))
              (EPath (MkPath ["res"]))
            )
          )
          BiNil
        )
        (
          ELet (
            BiCons (
              Binding (PVar "c")
              (
                EApp (EPath (MkPath ["get"]))
                (EData "()" (EMkTuple[]))
              )
            )
            BiNil
          )
          (
            EMatch (EApp (EPath (MkPath ["upd"])) (EInt 13))
            (
              MkBranches [(
                Branch (PData "()" (PTuple PNil))
                (
                  ELet (
                    BiCons (
                      Binding (PVar "res")
                      (
                        EApp (
                          EApp (EPath (MkPath ["-"]))
                          (
                            EApp (EPath (MkPath ["get"]))
                            (EData "()" (EMkTuple[]))
                          )
                        )
                        (EPath (MkPath ["c"]))
                      )
                    )
                    BiNil
                  )
                  (EPath (MkPath ["res"]))
                )
              )]
            )
          )
        )
      )
    )
  )
).
Definition __osiris__reservedsplit_all_module3 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem4
    BiNil
  )
).
Definition __osiris__reservedsplit_all_sitem6 : binding :=
(
  Binding (PVar "_test")
  (
    ELet (
      BiCons (
        Binding (PMkTuple [(PVar "get");(PVar "upd")])
        (
          EApp (EPath (MkPath ["new_counter"]))
          (EData "()" (EMkTuple[]))
        )
      )
      BiNil
    )
    (
      ELet (
        BiCons (
          Binding (PVar "c")
          (
            EApp (EPath (MkPath ["get"]))
            (EData "()" (EMkTuple[]))
          )
        )
        BiNil
      )
      (
        EMatch (EApp (EPath (MkPath ["upd"])) (EInt 13))
        (
          MkBranches [(
            Branch (PData "()" (PTuple PNil))
            (
              ELet (
                BiCons (
                  Binding (PVar "res")
                  (
                    EApp (
                      EApp (EPath (MkPath ["-"]))
                      (
                        EApp (EPath (MkPath ["get"]))
                        (EData "()" (EMkTuple[]))
                      )
                    )
                    (EPath (MkPath ["c"]))
                  )
                )
                BiNil
              )
              (EPath (MkPath ["res"]))
            )
          )]
        )
      )
    )
  )
).
Definition __osiris__reservedsplit_all_module5 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem6
    BiNil
  )
).
Definition _Incr : mexpr :=
(
  MkStruct
[__osiris__reservedsplit_all_module1;__osiris__reservedsplit_all_module3;__osiris__reservedsplit_all_module5]
).

(* Done. *)