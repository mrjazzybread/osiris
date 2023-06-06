(* This (handwritten) file provides distinct top-level definitions for each
   function of the source file.

   The point is to experiment on proofs to decide whether it is easier to:
   - write a single proof (of the whole module, defined in
     [records/records_code.v]) ;
   - write one proof for each function body (caller-side reasoning) and to use
     them in the proof of the module ;
   - write one proof by function (callee-side reasoning) and to use them in the
     proof of the module. *)

From osiris Require Import base.
From osiris.lang Require Import lang.
From test.records Require Import records.

Definition r_elt_expr :=
  ERecord (
      FECons "i"
             (EInt 10)
             (FECons "b" (EData "true" (ETuple ENil)) FENil)
    ).

Definition flip_body (r: var) : expr :=
  ERecordUpdate (EPath (PathBase r)) $
                FECons "b"
                (
                  EApp (EPath (PathDot (PathBase "Stdlib") "not"))
                       (ERecordAccess (EPath (PathBase r)) "b")
                )
                FENil
.

Definition flip_function : expr :=
  EAnonFun $
           AnonFun1Pat (PVar "r") (flip_body "r").

Definition lily_expr : expr :=
  EData "::" $
        ETuple $
        ECons (EPath (PathBase "r_elt")) $
        ECons (
          EData "::" $
                ETuple $
                ECons (
                  EApp (EPath (PathBase "flip"))
                       (EPath (PathBase "r_elt"))
                )
                (ECons (EData "[]" (ETuple ENil)) ENil)
        )
        ENil.

Definition r_val_body (r: var) : expr :=
  EMatch (ERecordAccess (EPath (PathBase r)) "b") $
         MkBranches
         [
           Branch (PBool true)
                  (
                    EApp (
                        EApp (EPath (PathDot (PathBase "Stdlib") "-"))
                             (
                               EApp (
                                   EApp (EPath (PathDot (PathBase "Stdlib")
                                                        "*"))
                                        (ERecordAccess (EPath (PathBase r)) "i")
                                 )
                                    (EInt 2)
                             )
                      )
                         (EInt 1)
                  ) ;
           Branch (PBool false)
                  (ERecordAccess (EPath (PathBase r)) "i")
         ].

Definition r_val_function : expr :=
  EAnonFun $
           AnonFun1Pat (PVar "r") $
           r_val_body "r".

Definition sum_body (r1 r2: var) : expr :=
  EApp (
      EApp (EPath (PathDot (PathBase "Stdlib") "+"))
           (
             EApp (EPath (PathBase "r_val"))
                  (EPath (PathBase r1))
           )
    )
       (
         EApp (EPath (PathBase "r_val"))
              (EPath (PathBase r2))
       ).

Definition sum_function : expr :=
  EAnonFun $
           AnonFun1Pat (PVar "r1") $
           EAnonFun $
           AnonFun1Pat (PVar "r2") $
           sum_body "r1" "r2".

Definition opacified_Records : mexpr :=
  MStruct $
          ICons (ILet (Binding1 (PVar "r_elt") r_elt_expr)) $
          ICons (ILet (Binding1 (PVar "flip") flip_function)) $
          ICons (ILet (Binding1 (PVar "lily") lily_expr)) $
          ICons (ILet (Binding1 (PVar "r_val") r_val_function)) $
          ICons (ILet (Binding1 (PVar "sum") sum_function)) $
          ICons (
            ILetRec (
                RecBiCons (
                    RecBinding "is_odd_naive"
                    (
                      AnonFun1Pat (PVar "n")
                      (
                        ESeq (
                          EAssert (
                            EApp (
                              EApp (EPath (PathDot (PathBase "Stdlib") ">="))
                              (EPath (PathBase "n"))
                            )
                            (EInt 0)
                          )
                        )
                        (
                          EIfThenElse (
                            EApp (
                              EApp (EPath (PathDot (PathBase "Stdlib") ">"))
                              (EPath (PathBase "n"))
                            )
                            (EInt 1)
                          )
                          (
                            EApp (EPath (PathBase "is_odd_naive"))
                            (
                              EApp (
                                EApp (EPath (PathDot (PathBase "Stdlib")
"-"))
                                (EPath (PathBase "n"))
                              )
                              (EInt 2)
                            )
                          )
                          (
                            EIfThenElse (
                              EApp (
                                EApp (EPath (PathDot (PathBase "Stdlib")
"="))
                                (EPath (PathBase "n"))
                              )
                              (EInt 0)
                            )
                            (EData "false" (ETuple ENil))
                            (EData "true" (ETuple ENil))
                          )
                        )
                      )
                    )
                  )
                  RecBiNil
                )
              )
              (
                ICons (
                  ILet (
                    BiCons (
                      Binding (PVar "is_odd")
                      (
                        EAnonFun (
                          AnonFun1Pat (PVar "n")
                          (
                            EApp (
                              EApp (EPath (PathDot (PathBase "Stdlib") "="))
                              (
                                EApp (
                                  EApp (EPath (PathDot (PathBase "Stdlib")
"mod"))
                                  (EPath (PathBase "n"))
                                )
                                (EInt 2)
                              )
                            )
                            (EInt 0)
                          )
                        )
                      )
                    )
                    BiNil
                  )
                )
                INil
              )
.
