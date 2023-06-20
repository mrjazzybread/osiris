From osiris Require Import osiris.



Definition __osiris__reservedsplit_all_sitem2 : binding := (
                                                             Binding (PVar
"r_elt")
                                                             (
                                                               ERecord (
                                                                 FECons "i"
                                                                 (EInt 10)
                                                                 (
                                                                   FECons "b"
                                                                   (EConstant
"true")
                                                                   FENil
                                                                 )
                                                               )
                                                             )
                                                           ).
Definition __osiris__reservedsplit_all_module1 : sitem := (
                                                            ILet (
                                                              BiCons
__osiris__reservedsplit_all_sitem2
                                                              BiNil
                                                            )
                                                          ).
Definition __osiris__reservedsplit_all_sitem4 : binding := (
                                                             Binding (PVar
"flip")
                                                             (
                                                               EAnonFun (
                                                                 AnonFun
"__osiris_anonymous_arg"
                                                                 (
                                                                   EMatch (
                                                                     EPath (
                                                                      
PathBase "__osiris_anonymous_arg"
                                                                     )
                                                                   )
                                                                   (
                                                                    
MkBranches [(
                                                                       Branch
(PVar "r")
                                                                       (
                                                                        
ERecordUpdate (
                                                                          
EPath (PathBase "r")
                                                                         )
                                                                         (
                                                                          
FECons "b"
                                                                           (
                                                                            
EApp (
                                                                             
 EPath (
                                                                             
   PathDot (
                                                                             
     PathBase "Stdlib"
                                                                             
   )
                                                                             
   "not"
                                                                             
 )
                                                                            
)
                                                                            
(
                                                                             
 ERecordAccess (
                                                                             
   EPath (
                                                                             
     PathBase "r"
                                                                             
   )
                                                                             
 )
                                                                             
 "b"
                                                                            
)
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
Definition __osiris__reservedsplit_all_module3 : sitem := (
                                                            ILet (
                                                              BiCons
__osiris__reservedsplit_all_sitem4
                                                              BiNil
                                                            )
                                                          ).
Definition __osiris__reservedsplit_all_sitem6 : binding := (
                                                             Binding (PVar
"lily")
                                                             (
                                                               EData "::"
                                                               (
                                                                 EMkTuple [(
                                                                   EPath
(PathBase "r_elt")
                                                                 );(
                                                                   EData "::"
                                                                   (
                                                                     EMkTuple
[(
                                                                       EApp (
                                                                        
EPath (PathBase "flip")
                                                                       )
                                                                       (EPath
(PathBase "r_elt"))
                                                                     );(EData
"[]" (EMkTuple[]))]
                                                                   )
                                                                 )]
                                                               )
                                                             )
                                                           ).
Definition __osiris__reservedsplit_all_module5 : sitem := (
                                                            ILet (
                                                              BiCons
__osiris__reservedsplit_all_sitem6
                                                              BiNil
                                                            )
                                                          ).
Definition __osiris__reservedsplit_all_sitem8 : binding := (
                                                             Binding (PVar
"r_val")
                                                             (
                                                               EAnonFun (
                                                                 AnonFun
"__osiris_anonymous_arg"
                                                                 (
                                                                   EMatch (
                                                                     EPath (
                                                                      
PathBase "__osiris_anonymous_arg"
                                                                     )
                                                                   )
                                                                   (
                                                                    
MkBranches [(
                                                                       Branch
(PVar "r")
                                                                       (
                                                                        
EMatch (
                                                                          
ERecordAccess (
                                                                            
EPath (PathBase "r")
                                                                           )
                                                                          
"b"
                                                                         )
                                                                         (
                                                                          
MkBranches [(
                                                                            
Branch (
                                                                             
 PData "true"
                                                                             
 PUnit
                                                                            
)
                                                                            
(
                                                                             
 EApp (
                                                                             
   EApp (
                                                                             
     EPath (
                                                                             
       PathDot (
                                                                             
         PathBase "Stdlib"
                                                                             
       )
                                                                             
       "-"
                                                                             
     )
                                                                             
   )
                                                                             
   (
                                                                             
     EApp (
                                                                             
       EApp (
                                                                             
         EPath (
                                                                             
           PathDot (
                                                                             
             PathBase "Stdlib"
                                                                             
           )
                                                                             
           "*"
                                                                             
         )
                                                                             
       )
                                                                             
       (
                                                                             
         ERecordAccess (
                                                                             
           EPath (
                                                                             
             PathBase "r"
                                                                             
           )
                                                                             
         )
                                                                             
         "i"
                                                                             
       )
                                                                             
     )
                                                                             
     (EInt 2)
                                                                             
   )
                                                                             
 )
                                                                             
 (EInt 1)
                                                                            
)
                                                                          
);(
                                                                            
Branch (
                                                                             
 PData "false"
                                                                             
 PUnit
                                                                            
)
                                                                            
(
                                                                             
 ERecordAccess (
                                                                             
   EPath (
                                                                             
     PathBase "r"
                                                                             
   )
                                                                             
 )
                                                                             
 "i"
                                                                            
)
                                                                           )]
                                                                         )
                                                                       )
                                                                     )]
                                                                   )
                                                                 )
                                                               )
                                                             )
                                                           ).
Definition __osiris__reservedsplit_all_module7 : sitem := (
                                                            ILet (
                                                              BiCons
__osiris__reservedsplit_all_sitem8
                                                              BiNil
                                                            )
                                                          ).
Definition __osiris__reservedsplit_all_sitem10 : binding := (
                                                              Binding (PVar
"sum")
                                                              (
                                                                EAnonFun (
                                                                  AnonFun
"__osiris_anonymous_arg"
                                                                  (
                                                                    EMatch (
                                                                      EPath (
                                                                       
PathBase "__osiris_anonymous_arg"
                                                                      )
                                                                    )
                                                                    (
                                                                     
MkBranches [(
                                                                       
Branch (PVar "r1")
                                                                        (
                                                                         
EAnonFun (
                                                                           
AnonFun "__osiris_anonymous_arg"
                                                                            (
                                                                             
EMatch (
                                                                             
  EPath (
                                                                             
    PathBase "__osiris_anonymous_arg"
                                                                             
  )
                                                                             
)
                                                                             
(
                                                                             
  MkBranches [(
                                                                             
    Branch (PVar "r2")
                                                                             
    (
                                                                             
      EApp (
                                                                             
        EApp (
                                                                             
          EPath (
                                                                             
            PathDot (
                                                                             
              PathBase "Stdlib"
                                                                             
            )
                                                                             
            "+"
                                                                             
          )
                                                                             
        )
                                                                             
        (
                                                                             
          EApp (
                                                                             
            EPath (
                                                                             
              PathBase "r_val"
                                                                             
            )
                                                                             
          )
                                                                             
          (
                                                                             
            EPath (
                                                                             
              PathBase "r1"
                                                                             
            )
                                                                             
          )
                                                                             
        )
                                                                             
      )
                                                                             
      (
                                                                             
        EApp (
                                                                             
          EPath (
                                                                             
            PathBase "r_val"
                                                                             
          )
                                                                             
        )
                                                                             
        (
                                                                             
          EPath (
                                                                             
            PathBase "r2"
                                                                             
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
                                                            ).
Definition __osiris__reservedsplit_all_module9 : sitem := (
                                                            ILet (
                                                              BiCons
__osiris__reservedsplit_all_sitem10
                                                              BiNil
                                                            )
                                                          ).
Definition __osiris__reservedsplit_all_rec_binding13 : expr := (
                                                                 EMatch (
                                                                   EPath (
                                                                     PathBase
"__osiris_anonymous_arg"
                                                                   )
                                                                 )
                                                                 (
                                                                   MkBranches
[(
                                                                     Branch
(PVar "n")
                                                                     (
                                                                       ESeq (
                                                                        
EAssert (
                                                                          
EApp (
                                                                            
EApp (
                                                                             
 EPath (
                                                                             
   PathDot (
                                                                             
     PathBase "Stdlib"
                                                                             
   )
                                                                             
   ">="
                                                                             
 )
                                                                            
)
                                                                            
(EPath (PathBase "n"))
                                                                           )
                                                                          
(EInt 0)
                                                                         )
                                                                       )
                                                                       (
                                                                        
EIfThenElse (
                                                                          
EApp (
                                                                            
EApp (
                                                                             
 EPath (
                                                                             
   PathDot (
                                                                             
     PathBase "Stdlib"
                                                                             
   )
                                                                             
   ">"
                                                                             
 )
                                                                            
)
                                                                            
(EPath (PathBase "n"))
                                                                           )
                                                                          
(EInt 1)
                                                                         )
                                                                         (
                                                                          
EApp (
                                                                            
EPath (
                                                                             
 PathBase "is_odd_naive"
                                                                            
)
                                                                           )
                                                                           (
                                                                            
EApp (
                                                                             
 EApp (
                                                                             
   EPath (
                                                                             
     PathDot (
                                                                             
       PathBase "Stdlib"
                                                                             
     )
                                                                             
     "-"
                                                                             
   )
                                                                             
 )
                                                                             
 (
                                                                             
   EPath (
                                                                             
     PathBase "n"
                                                                             
   )
                                                                             
 )
                                                                            
)
                                                                            
(EInt 2)
                                                                           )
                                                                         )
                                                                         (
                                                                          
EIfThenElse (
                                                                            
EApp (
                                                                             
 EApp (
                                                                             
   EPath (
                                                                             
     PathDot (
                                                                             
       PathBase "Stdlib"
                                                                             
     )
                                                                             
     "="
                                                                             
   )
                                                                             
 )
                                                                             
 (
                                                                             
   EPath (
                                                                             
     PathBase "n"
                                                                             
   )
                                                                             
 )
                                                                            
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
                                                               ).
Definition __osiris__reservedsplit_all_sitem12 : rec_binding := (
                                                                  RecBinding
"is_odd_naive"
                                                                  (
                                                                    AnonFun
"__osiris_anonymous_arg"
                                                                   
__osiris__reservedsplit_all_rec_binding13
                                                                  )
                                                                ).
Definition __osiris__reservedsplit_all_module11 : sitem := (
                                                             ILetRec (
                                                               RecBiCons
__osiris__reservedsplit_all_sitem12
                                                               RecBiNil
                                                             )
                                                           ).
Definition __osiris__reservedsplit_all_sitem15 : binding := (
                                                              Binding (PVar
"is_odd")
                                                              (
                                                                EAnonFun (
                                                                  AnonFun
"__osiris_anonymous_arg"
                                                                  (
                                                                    EMatch (
                                                                      EPath (
                                                                       
PathBase "__osiris_anonymous_arg"
                                                                      )
                                                                    )
                                                                    (
                                                                     
MkBranches [(
                                                                       
Branch (PVar "n")
                                                                        (
                                                                         
EApp (
                                                                           
EApp (
                                                                             
EPath (
                                                                             
  PathDot (
                                                                             
    PathBase "Stdlib"
                                                                             
  )
                                                                             
  "="
                                                                             
)
                                                                            )
                                                                            (
                                                                             
EApp (
                                                                             
  EApp (
                                                                             
    EPath (
                                                                             
      PathDot (
                                                                             
        PathBase "Stdlib"
                                                                             
      )
                                                                             
      "mod"
                                                                             
    )
                                                                             
  )
                                                                             
  (
                                                                             
    EPath (
                                                                             
      PathBase "n"
                                                                             
    )
                                                                             
  )
                                                                             
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
Definition __osiris__reservedsplit_all_module14 : sitem := (
                                                             ILet (
                                                               BiCons
__osiris__reservedsplit_all_sitem15
                                                               BiNil
                                                             )
                                                           ).
Definition __osiris__reservedsplit_all_rec_binding18 : expr := (
                                                                 EMatch (
                                                                   EPath (
                                                                     PathBase
"__osiris_anonymous_arg"
                                                                   )
                                                                 )
                                                                 (
                                                                   MkBranches
[(
                                                                     Branch
(PData "O" PUnit)
                                                                    
(EConstant "true")
                                                                   );(
                                                                     Branch (
                                                                       PData
"S"
                                                                      
(PMkTuple [(PVar "n")])
                                                                     )
                                                                     (
                                                                       EApp (
                                                                        
EPath (
                                                                          
PathDot (
                                                                            
PathBase "Stdlib"
                                                                           )
                                                                          
"not"
                                                                         )
                                                                       )
                                                                       (
                                                                         EApp
(
                                                                          
EPath (
                                                                            
PathBase "is_odd'"
                                                                           )
                                                                         )
                                                                        
(EPath (PathBase "n"))
                                                                       )
                                                                     )
                                                                   )]
                                                                 )
                                                               ).
Definition __osiris__reservedsplit_all_sitem17 : rec_binding := (
                                                                  RecBinding
"is_odd'"
                                                                  (
                                                                    AnonFun
"__osiris_anonymous_arg"
                                                                   
__osiris__reservedsplit_all_rec_binding18
                                                                  )
                                                                ).
Definition __osiris__reservedsplit_all_module16 : sitem := (
                                                             ILetRec (
                                                               RecBiCons
__osiris__reservedsplit_all_sitem17
                                                               RecBiNil
                                                             )
                                                           ).
Definition Records : mexpr := (
                                MkStruct
[__osiris__reservedsplit_all_module1;__osiris__reservedsplit_all_module3;__osiris__reservedsplit_all_module5;__osiris__reservedsplit_all_module7;__osiris__reservedsplit_all_module9;__osiris__reservedsplit_all_module11;__osiris__reservedsplit_all_module14;__osiris__reservedsplit_all_module16]
                             
).

(* Done. *)