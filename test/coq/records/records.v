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
                  EApp (EPath (MkPath ["Stdlib";"not"]))
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
                      EApp (EPath (MkPath ["Stdlib";"-"]))
                      (
                        EApp (
                          EApp (EPath (MkPath ["Stdlib";"*"]))
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
                          EApp (EPath (MkPath ["Stdlib";"+"]))
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
Definition __osiris__reservedsplit_all_rec_binding13 : expr :=
(
  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
  (
    MkBranches [(
      Branch (PVar "n")
      (
        ESeq (
          EAssert (
            EApp (
              EApp (EPath (MkPath ["Stdlib";">="]))
              (EPath (MkPath ["n"]))
            )
            (EInt 0)
          )
        )
        (
          EIfThenElse (
            EApp (
              EApp (EPath (MkPath ["Stdlib";">"]))
              (EPath (MkPath ["n"]))
            )
            (EInt 1)
          )
          (
            EApp (EPath (MkPath ["is_odd_naive"]))
            (
              EApp (
                EApp (EPath (MkPath ["Stdlib";"-"]))
                (EPath (MkPath ["n"]))
              )
              (EInt 2)
            )
          )
          (
            EIfThenElse (
              EApp (
                EApp (EPath (MkPath ["Stdlib";"="]))
                (EPath (MkPath ["n"]))
              )
              (EInt 0)
            )
            (EData "false" (EMkTuple[]))
            (EData "true" (EMkTuple[]))
          )
        )
      )
    )]
  )
).
Definition __osiris__reservedsplit_all_sitem12 : rec_binding :=
(
  RecBinding "is_odd_naive"
  (
    AnonFun "__osiris_anonymous_arg"
    __osiris__reservedsplit_all_rec_binding13
  )
).
Definition __osiris__reservedsplit_all_module11 : sitem :=
(
  ILetRec (
    RecBiCons __osiris__reservedsplit_all_sitem12
    RecBiNil
  )
).
Definition __osiris__reservedsplit_all_sitem15 : binding :=
(
  Binding (PVar "is_odd")
  (
    EAnonFun (
      AnonFun "__osiris_anonymous_arg"
      (
        EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
        (
          MkBranches [(
            Branch (PVar "n")
            (
              EApp (
                EApp (EPath (MkPath ["Stdlib";"="]))
                (
                  EApp (
                    EApp (EPath (MkPath ["Stdlib";"mod"]))
                    (EPath (MkPath ["n"]))
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
).
Definition __osiris__reservedsplit_all_module14 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem15
    BiNil
  )
).
Definition __osiris__reservedsplit_all_rec_binding18 : expr :=
(
  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
  (
    MkBranches [(
      Branch (PData "O" (PTuple PNil))
      (EData "true" (EMkTuple[]))
    );(
      Branch (PData "S" (PMkTuple [(PVar "n")]))
      (
        EApp (EPath (MkPath ["Stdlib";"not"]))
        (
          EApp (EPath (MkPath ["is_odd'"]))
          (EPath (MkPath ["n"]))
        )
      )
    )]
  )
).
Definition __osiris__reservedsplit_all_sitem17 : rec_binding :=
(
  RecBinding "is_odd'"
  (
    AnonFun "__osiris_anonymous_arg"
    __osiris__reservedsplit_all_rec_binding18
  )
).
Definition __osiris__reservedsplit_all_module16 : sitem :=
(
  ILetRec (
    RecBiCons __osiris__reservedsplit_all_sitem17
    RecBiNil
  )
).
Definition _Records : mexpr :=
(
  MkStruct
[__osiris__reservedsplit_all_module1;__osiris__reservedsplit_all_module3;__osiris__reservedsplit_all_module5;__osiris__reservedsplit_all_module7;__osiris__reservedsplit_all_module9;__osiris__reservedsplit_all_module11;__osiris__reservedsplit_all_module14;__osiris__reservedsplit_all_module16]
).

(* Done. *)