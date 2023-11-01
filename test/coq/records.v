From osiris Require Import osiris.



Definition __osiris__reservedsplit_all_sitem2 : binding :=
(
  Binding (PVar "r_elt")
  (
    ERecord (
      FECons "i"
      (EInt 10)
      (FECons "b" (EData "true" (EMkTuple[])) FENil)
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
  Binding (PVar "flip")
  (
    EAnonFun (
      AnonFun "__osiris_anonymous_arg"
      (
        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
        (
          MkBranches [(
            Branch (PVar "r")
            (
              ERecordUpdate (EPath (MkPath ["r"]))
              (
                FECons "b"
                (
                  EApp (EPath (MkPath ["not"]))
                  (ERecordAccess (EPath (MkPath ["r"])) "b")
                )
                FENil
              )
            )
          )]
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
  Binding (PVar "lily")
  (
    EData "::"
    (
      EMkTuple [(EPath (MkPath ["r_elt"]));(
        EData "::"
        (
          EMkTuple [(
            EApp (EPath (MkPath ["flip"]))
            (EPath (MkPath ["r_elt"]))
          );(EData "[]" (EMkTuple[]))]
        )
      )]
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
Definition __osiris__reservedsplit_all_sitem8 : binding :=
(
  Binding (PVar "r_val")
  (
    EAnonFun (
      AnonFun "__osiris_anonymous_arg"
      (
        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
        (
          MkBranches [(
            Branch (PVar "r")
            (
              EMatch (ERecordAccess (EPath (MkPath ["r"])) "b")
              (
                MkBranches [(
                  Branch (PData "true" (PTuple PNil))
                  (
                    EApp (
                      EApp (EPath (MkPath ["-"]))
                      (
                        EApp (
                          EApp (EPath (MkPath ["*"]))
                          (ERecordAccess (EPath (MkPath ["r"])) "i")
                        )
                        (EInt 2)
                      )
                    )
                    (EInt 1)
                  )
                );(
                  Branch (PData "false" (PTuple PNil))
                  (ERecordAccess (EPath (MkPath ["r"])) "i")
                )]
              )
            )
          )]
        )
      )
    )
  )
).
Definition __osiris__reservedsplit_all_module7 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem8
    BiNil
  )
).
Definition __osiris__reservedsplit_all_sitem10 : binding :=
(
  Binding (PVar "sum")
  (
    EAnonFun (
      AnonFun "__osiris_anonymous_arg"
      (
        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
        (
          MkBranches [(
            Branch (PVar "r1")
            (
              EAnonFun (
                AnonFun "__osiris_anonymous_arg"
                (
                  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
                  (
                    MkBranches [(
                      Branch (PVar "r2")
                      (
                        EApp (
                          EApp (EPath (MkPath ["+"]))
                          (
                            EApp (EPath (MkPath ["r_val"]))
                            (EPath (MkPath ["r1"]))
                          )
                        )
                        (
                          EApp (EPath (MkPath ["r_val"]))
                          (EPath (MkPath ["r2"]))
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
).
Definition __osiris__reservedsplit_all_module9 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem10
    BiNil
  )
).
Definition _Records : mexpr :=
(
  MkStruct [__osiris__reservedsplit_all_module1;__osiris__reservedsplit_all_module3;__osiris__reservedsplit_all_module5;__osiris__reservedsplit_all_module7;__osiris__reservedsplit_all_module9]
).

(* Done. *)