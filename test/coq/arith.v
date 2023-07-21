From osiris Require Import osiris.



Definition __osiris__reservedsplit_all_rec_binding3 : expr :=
(
  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
  (
    MkBranches [(
      Branch (PVar "x")
      (
        EAnonFun (
          AnonFun "__osiris_anonymous_arg"
          (
            EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
            (
              MkBranches [(
                Branch (PVar "y")
                (
                  EIfThenElse (
                    EApp (
                      EApp (EPath (MkPath ["Stdlib";"="]))
                      (EPath (MkPath ["y"]))
                    )
                    (EInt 0)
                  )
                  (
                    EApp (
                      EApp (EPath (MkPath ["mult"]))
                      (EPath (MkPath ["x"]))
                    )
                    (EInt 1)
                  )
                  (
                    EApp (
                      EApp (EPath (MkPath ["Stdlib";"+"]))
                      (EInt 1)
                    )
                    (
                      EApp (
                        EApp (EPath (MkPath ["add"]))
                        (EPath (MkPath ["x"]))
                      )
                      (
                        EApp (
                          EApp (EPath (MkPath ["Stdlib";"-"]))
                          (EPath (MkPath ["y"]))
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
).
Definition __osiris__reservedsplit_all_sitem2 : rec_binding :=
(
  RecBinding "add"
  (
    AnonFun "__osiris_anonymous_arg"
    __osiris__reservedsplit_all_rec_binding3
  )
).
Definition __osiris__reservedsplit_all_rec_binding5 : expr :=
(
  EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
  (
    MkBranches [(
      Branch (PVar "x")
      (
        EAnonFun (
          AnonFun "__osiris_anonymous_arg"
          (
            EMatch (EPath (MkPath ["__osiris_anonymous_arg"]))
            (
              MkBranches [(
                Branch (PVar "y")
                (
                  EIfThenElse (
                    EApp (
                      EApp (EPath (MkPath ["Stdlib";"="]))
                      (EPath (MkPath ["y"]))
                    )
                    (EInt 0)
                  )
                  (EInt 0)
                  (
                    EIfThenElse (
                      EApp (
                        EApp (EPath (MkPath ["Stdlib";"="]))
                        (EPath (MkPath ["y"]))
                      )
                      (EInt 1)
                    )
                    (EPath (MkPath ["x"]))
                    (
                      EApp (
                        EApp (EPath (MkPath ["add"]))
                        (EPath (MkPath ["x"]))
                      )
                      (
                        EApp (
                          EApp (EPath (MkPath ["mult"]))
                          (EPath (MkPath ["x"]))
                        )
                        (
                          EApp (
                            EApp (EPath (MkPath ["Stdlib";"-"]))
                            (EPath (MkPath ["y"]))
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
).
Definition __osiris__reservedsplit_all_sitem4 : rec_binding :=
(
  RecBinding "mult"
  (
    AnonFun "__osiris_anonymous_arg"
    __osiris__reservedsplit_all_rec_binding5
  )
).
Definition __osiris__reservedsplit_all_module1 : sitem :=
(
  ILetRec (
    RecBiCons __osiris__reservedsplit_all_sitem2
    (
      RecBiCons __osiris__reservedsplit_all_sitem4
      RecBiNil
    )
  )
).
Definition __osiris__reservedsplit_all_sitem7 : binding :=
(
  Binding (PVar "i3")
  (
    EApp (EApp (EPath (MkPath ["add"])) (EInt 1))
    (
      EApp (EApp (EPath (MkPath ["add"])) (EInt 2))
      (EInt 0)
    )
  )
).
Definition __osiris__reservedsplit_all_module6 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem7
    BiNil
  )
).
Definition __osiris__reservedsplit_all_sitem9 : binding :=
(
  Binding (PVar "i17")
  (
    EApp (
      EApp (EPath (MkPath ["add"]))
      (
        EApp (EApp (EPath (MkPath ["mult"])) (EInt 2))
        (EInt 2)
      )
    )
    (
      EApp (EApp (EPath (MkPath ["add"])) (EInt 1))
      (
        EApp (EApp (EPath (MkPath ["mult"])) (EInt 2))
        (
          EApp (EApp (EPath (MkPath ["add"])) (EInt 4))
          (EInt 2)
        )
      )
    )
  )
).
Definition __osiris__reservedsplit_all_module8 : sitem :=
(
  ILet (
    BiCons __osiris__reservedsplit_all_sitem9
    BiNil
  )
).
Definition _Arith : mexpr :=
(
  MkStruct
[__osiris__reservedsplit_all_module1;__osiris__reservedsplit_all_module6;__osiris__reservedsplit_all_module8]
).

(* Done. *)