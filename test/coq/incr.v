(* Original file:
let new_counter () =
  let c = ref 0 in let upd i = c := i in let get () = !c in (get, upd)
let _ =
  let res = new_counter () in
  let get = fst res in
  let upd = snd res in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res
let _test =
  let (get, upd) = new_counter () in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res *)

(* Converting a single CMT file for [Incr]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
From osiris Require Import base.
From osiris.lang Require Import lang encode.
From osiris.semantics Require Import sugar notations.

From osiris.libs Require Import Stdlib.


(* Generated code: *)
Definition new_counter :=
  EFun1Var "()" $
  ELet
    (BiCons
      (Binding (PVar "c") (EApp (EMkPath ["Stdlib";"ref"]) (EInt 0))) $
    BiNil) $
  ELet
    (BiCons
      (Binding (PVar "upd") (EFun1Var "i" $
      EApp (EApp (EMkPath ["Stdlib";":="]) (EVar "c")) (EVar "i"))) $
    BiNil) $
  ELet
    (BiCons
      (Binding (PVar "get") (EFun1Var "()" $
      EApp (EMkPath ["Stdlib";"!"]) (EVar "c"))) $
    BiNil) $
  ETuple (ECons (EVar "get") (ECons (EVar "upd") ENil)).


Definition pleasedontclash (*This is not a name. *) :=
   ELet
     (BiCons
       (Binding (PVar "res") (EApp (EVar "new_counter") EUnit)) $
     BiNil) $
   ELet
     (BiCons
       (Binding (PVar "get") (EApp (EMkPath ["Stdlib";"fst"]) (EVar "res")))
$
     BiNil) $
   ELet
     (BiCons
       (Binding (PVar "upd") (EApp (EMkPath ["Stdlib";"snd"]) (EVar "res")))
$
     BiNil) $
   ELet
     (BiCons
       (Binding (PVar "c") (EApp (EVar "get") EUnit)) $
     BiNil) $
   EMatch (EApp (EVar "upd") (EInt 13)) (BrCons (Branch PUnit (ELet
     (BiCons
       (Binding (PVar "res") (EApp (EApp (EMkPath ["Stdlib";"-"]) (EApp (EVar
"get") EUnit)) (EVar "c"))) $
     BiNil) $
   EVar "res")) BrNil).


Definition _test :=
  ELet
    (BiCons
      (Binding (PTuple (PCons (PVar "upd") (PCons (PVar "get") PNil))) (EApp
(EVar "new_counter") EUnit)) $
    BiNil) $
  ELet
    (BiCons
      (Binding (PVar "c") (EApp (EVar "get") EUnit)) $
    BiNil) $
  EMatch (EApp (EVar "upd") (EInt 13)) (BrCons (Branch PUnit (ELet
    (BiCons
      (Binding (PVar "res") (EApp (EApp (EMkPath ["Stdlib";"-"]) (EApp (EVar
"get") EUnit)) (EVar "c"))) $
    BiNil) $
  EVar "res"))
BrNil).


