From osiris Require Import osiris.



Definition Incr : mexpr := (
                             MkStruct [(
                               ILet (
                                 BiCons (
                                   Binding (PVar "new_counter")
                                   (
                                     EAnonFun (
                                       AnonFun "__osiris_anonymous_arg"
                                       (
                                         EMatch (EPath (PathBase
"__osiris_anonymous_arg"))
                                         (
                                           MkBranches [(
                                             Branch PUnit
                                             (
                                               ELet (
                                                 BiCons (
                                                   Binding (PVar "c")
                                                   (
                                                     EApp (
                                                       EPath (PathDot
(PathBase "Stdlib") "ref")
                                                     )
                                                     (EInt 0)
                                                   )
                                                 )
                                                 BiNil
                                               )
                                               (
                                                 ELet (
                                                   BiCons (
                                                     Binding (PVar "upd")
                                                     (
                                                       EAnonFun (
                                                         AnonFun
"__osiris_anonymous_arg"
                                                         (
                                                           EMatch (
                                                             EPath (
                                                               PathBase
"__osiris_anonymous_arg"
                                                             )
                                                           )
                                                           (
                                                             MkBranches [(
                                                               Branch (PVar
"i")
                                                               (
                                                                 EApp (
                                                                   EApp (
                                                                     EPath (
                                                                      
PathDot (PathBase "Stdlib")
                                                                       ":="
                                                                     )
                                                                   )
                                                                   (EPath
(PathBase "c"))
                                                                 )
                                                                 (EPath
(PathBase "i"))
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
                                                           AnonFun
"__osiris_anonymous_arg"
                                                           (
                                                             EMatch (
                                                               EPath (
                                                                 PathBase
"__osiris_anonymous_arg"
                                                               )
                                                             )
                                                             (
                                                               MkBranches [(
                                                                 Branch PUnit
                                                                 (
                                                                   EApp (
                                                                     EPath (
                                                                      
PathDot (PathBase "Stdlib")
                                                                       "!"
                                                                     )
                                                                   )
                                                                   (EPath
(PathBase "c"))
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
                                                     EMkTuple [(EPath
(PathBase "get"));(
                                                       EPath (PathBase "upd")
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
                                   Binding PAny
                                   (
                                     ELet (
                                       BiCons (
                                         Binding (PVar "res")
                                         (EApp (EPath (PathBase
"new_counter")) EUnit)
                                       )
                                       BiNil
                                     )
                                     (
                                       ELet (
                                         BiCons (
                                           Binding (PVar "get")
                                           (
                                             EApp (EPath (PathDot (PathBase
"Stdlib") "fst"))
                                             (EPath (PathBase "res"))
                                           )
                                         )
                                         BiNil
                                       )
                                       (
                                         ELet (
                                           BiCons (
                                             Binding (PVar "upd")
                                             (
                                               EApp (EPath (PathDot (PathBase
"Stdlib") "snd"))
                                               (EPath (PathBase "res"))
                                             )
                                           )
                                           BiNil
                                         )
                                         (
                                           ELet (
                                             BiCons (
                                               Binding (PVar "c")
                                               (EApp (EPath (PathBase "get"))
EUnit)
                                             )
                                             BiNil
                                           )
                                           (
                                             EMatch (EApp (EPath (PathBase
"upd")) (EInt 13))
                                             (
                                               MkBranches [(
                                                 Branch PUnit
                                                 (
                                                   ELet (
                                                     BiCons (
                                                       Binding (PVar "res")
                                                       (
                                                         EApp (
                                                           EApp (
                                                             EPath (PathDot
(PathBase "Stdlib") "-")
                                                           )
                                                           (EApp (EPath
(PathBase "get")) EUnit)
                                                         )
                                                         (EPath (PathBase
"c"))
                                                       )
                                                     )
                                                     BiNil
                                                   )
                                                   (EPath (PathBase "res"))
                                                 )
                                               )]
                                             )
                                           )
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
                                   Binding (PVar "_test")
                                   (
                                     ELet (
                                       BiCons (
                                         Binding (PMkTuple [(PVar
"get");(PVar "upd")])
                                         (EApp (EPath (PathBase
"new_counter")) EUnit)
                                       )
                                       BiNil
                                     )
                                     (
                                       ELet (
                                         BiCons (
                                           Binding (PVar "c")
                                           (EApp (EPath (PathBase "get"))
EUnit)
                                         )
                                         BiNil
                                       )
                                       (
                                         EMatch (EApp (EPath (PathBase
"upd")) (EInt 13))
                                         (
                                           MkBranches [(
                                             Branch PUnit
                                             (
                                               ELet (
                                                 BiCons (
                                                   Binding (PVar "res")
                                                   (
                                                     EApp (
                                                       EApp (
                                                         EPath (PathDot
(PathBase "Stdlib") "-")
                                                       )
                                                       (EApp (EPath (PathBase
"get")) EUnit)
                                                     )
                                                     (EPath (PathBase "c"))
                                                   )
                                                 )
                                                 BiNil
                                               )
                                               (EPath (PathBase "res"))
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
                          
).
(* Done. *)