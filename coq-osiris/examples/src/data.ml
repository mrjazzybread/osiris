(* This file is intended to help us study how various OCaml data types
   are encoded is Osiris. It may be changed or removed in the future. *)

type arity0 =
  | A

type 'a arity1 =
  | A of 'a

type ('a, 'b) arity2 =
  | A of 'a * 'b

let a0 : arity0 =
  A

let a1 : unit arity1 =
  A ()

let b =
  (* This comparison arguably has unspecified behavior in OCaml, because
     it is applied to two values of different types. In our semantics, it
     happens to crash, because the two constructors have the same name but
     have different arities.  *)
  (Obj.magic a0) = a1
