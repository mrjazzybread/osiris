Require int.
Require Import base lang.

(* The sugar in this file can help construct ASTs by hand in Coq. *)

(* It may also be used by the Osiris translator. The definitions that
   the translator relies upon are marked REQUIRED. *)

(* ------------------------------------------------------------------------ *)

(* Paths. *)

Fixpoint MkPathRev (xs : list name) : path :=
  match xs with
  | [] =>
      (* Not supposed to happen. *)
      PathBase "<error in MkPath>"
  | [x] =>
      PathBase x
  | x :: xs =>
      PathDot (MkPathRev xs) x
  end.

Definition MkPath (xs : list name) : path :=
  MkPathRev (rev xs).

(* ------------------------------------------------------------------------ *)

(* Pairs: pattern, expression, value. *)

Definition PPair p1 p2 :=
  (PTuple (PCons p1 (PCons p2 PNil))).

Definition EPair e1 e2 :=
  (ETuple (ECons e1 (ECons e2 ENil))).

Definition VPair v1 v2 :=
  (VTuple (VCons v1 (VCons v2 VNil))).

(* ------------------------------------------------------------------------ *)

(* Options: values. *)

Definition VNone :=
  (VConstant "None").

Definition VSome v :=
  (VData "Some" v).

(* ------------------------------------------------------------------------ *)

(* Lists: patterns, expressions, values. *)

(* TODO would like to use VNil and VCons, but this causes a name clash *)

Definition pNil :=
  (PConstant "[]").

Definition pCons p1 p2 :=
  (PData "::" (PPair p1 p2)).

Definition eNil :=
  (EConstant "[]").

Definition eCons e1 e2 :=
  (EData "::" (EPair e1 e2)).

Definition vNil :=
  (VConstant "[]").

Definition vCons v1 v2 :=
  (VData "::" (VPair v1 v2)).

(* ------------------------------------------------------------------------ *)

(* Expressions. *)

(* [x]. *)

Definition EVar x :=
  (EPath (PathBase x)).

(* [π]. *)

Definition EMkPath xs :=
  (EPath (MkPath xs)).

(* [p = e]. *)

Definition Binding1 (p : pat) (e : expr) : bindings :=
  let binding := Binding p e in
  BiCons binding BiNil.

(* [let p = e1 in e2]. *)

Definition ELet1 (p : pat) (e1 e2 : expr) :=
  ELet (Binding1 p e1) e2.

(* [let x = e1 in e2]. *)

Definition ELet1Var (x : var) (e1 e2 : expr) :=
  ELet1 (PVar x) e1 e2.

(* [rec f x = e1]. *)

Definition RecBinding1 (f x : var) (e1 : expr) : rec_bindings :=
  let rb := RecBinding f (AnonFun x e1) in
  RecBiCons rb RecBiNil.

(* [let rec f x = e1 in e2]. *)

Definition ELetRec1 (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1 f x e1) e2.

(* [fun x -> e]. *)

Definition EFun (x : var) (e : expr) :=
  EAnonFun (AnonFun x e).

(* ------------------------------------------------------------------------ *)

(* Sugar for module expressions. *)

(* [MkStruct items] allows the use of standard list syntax. *)

Fixpoint MkSItems (items : list sitem) : sitems :=
  match items with
  | [] =>
      INil
  | item :: items =>
      ICons item (MkSItems items)
  end.

Definition MkStruct (items : list sitem) : mexpr :=
  MStruct (MkSItems items).

(* [open π]. *)

Definition IOpenMkPath xs :=
  (IOpen (MkPath xs)).

(* [include π]. *)

Definition IIncludeMkPath xs :=
  (IInclude (MPath (MkPath xs))).
