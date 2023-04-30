(* Original file:
let new_counter () =
  let c = ref 0 in let upd i = c := i in let get () = !c in (get, upd) *)

(* Converting a single CMT file for [Incr]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
Require Import base lang sugar encode.
(* TODO: get the From _ to work From libs *) Require Import Stdlib.


(* Generated code: *)
Definition new_counter :=
  EFun "_" $
    ELet (BiCons
      (Binding (PVar "c")
               (EApp (EMkPath ["Stdlib";"ref"]) (EInt 0)))
      BiNil) $
    ELet (BiCons
      (Binding (PVar "upd")
               (EFun "i"
                     (EApp (EApp (EMkPath ["Stdlib";":="])
                                 (EVar "c"))
                           (EVar "i"))))
      BiNil) $
    ELet (BiCons
      (Binding (PVar "get")
               (EFun "_" (EApp (EMkPath ["Stdlib";"!"]) (EVar "c"))))
      BiNil) $
    (ETuple (ECons (EVar "get") (ECons (EVar "upd") ENil))).

