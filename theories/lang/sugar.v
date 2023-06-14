From osiris.lang Require int.
From osiris Require Import base.
From osiris.lang Require Import syntax.

(* The sugar in this file can help construct ASTs by hand in Coq. *)

(* The definitions in this file may be used by the Osiris translator. *)

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

(* Branches. *)

Fixpoint MkBranches (bs : list branch) : branches :=
  match bs with
  | [] =>
      BrNil
  | b :: bs =>
      BrCons b (MkBranches bs)
  end.

Definition Branch1 p e : branches :=
  BrCons (Branch p e) BrNil.

(* ------------------------------------------------------------------------ *)

(* Pairs: pattern, expression, value. *)

Definition PPair p1 p2 :=
  (PTuple (PCons p1 (PCons p2 PNil))).

Definition EPair e1 e2 :=
  (ETuple (ECons e1 (ECons e2 ENil))).

Definition VPair v1 v2 :=
  (VTuple (VCons v1 (VCons v2 VNil))).

(* Tuples of arity 3. *)

Notation VTuple3 v1 v2 v3 :=
  (
    VTuple (
      VCons v1 $
      VCons v2 $
      VCons v3 $
      VNil
    )
  ).

(* Tuples of arity 4. *)

Notation VTuple4 v1 v2 v3 v4 :=
  (
    VTuple (
      VCons v1 $
      VCons v2 $
      VCons v3 $
      VCons v4 $
      VNil
    )
  ).

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

(* [fun x -> e]. *)

Definition AnonFun1Var : var → expr → anonfun :=
  AnonFun.

Definition EFun1Var (x : var) (e : expr) :=
  EAnonFun (AnonFun1Var x e).

(* [function bs] is sugar for [fun x -> match x with bs]. *)

(* The variable [x] must not occur free in [bs]. *)

(* We use a reserved name for [x]. Provided end users do not use such a
   reserved name in their OCaml source code, we can be assured that [x]
   does not occur free in [bs]. *)

Definition AnonFunction (bs : branches) : anonfun :=
  let x := "__osiris_anonymous_arg" in
  AnonFun1Var x $
  EMatch (EVar x) bs.

Definition EFunction (bs : branches) :=
  EAnonFun (AnonFunction bs).

(* [match e with bs]. *)

Definition EMatchMkBranches (e : expr) (bs : list branch) :=
  EMatch e (MkBranches bs).

(* [fun p -> e] is sugar for [fun x -> match x with p -> e]. *)

(* It is the same as [function p -> e]. *)

(* It is a special case of the previous sugar. *)

Definition AnonFun1Pat (p : pat) (e : expr) : anonfun :=
  AnonFunction (MkBranches [Branch p e]).

Definition EFun1Pat (p : pat) (e : expr) :=
  EAnonFun (AnonFun1Pat p e).

(* [fun ps -> e]. *)

(* [fun p1 p2 ... pn -> e] is [fun p1 -> fun p2 -> ... fun pn -> e]. *)

Fixpoint EFunMultiPat (ps : list pat) (e : expr) :=
  match ps with
  | [] =>
      e
  | p :: ps =>
      EFun1Pat p (EFunMultiPat ps e)
  end.

Definition AnonFunMultiPat (p : pat) (ps : list pat) (e : expr) : anonfun :=
  AnonFun1Pat p (EFunMultiPat ps e).

Goal
  ∀ p ps e,
  EFunMultiPat (p :: ps) e =
  EAnonFun (AnonFunMultiPat p ps e).
Proof.
  reflexivity.
Qed.

(* [e0 e1 ... en] is sugar for [((e0 e1) ... en)]. *)

Fixpoint EMultiApp (e0 : expr) (es : list expr) :=
  match es with
  | [] =>
      e0
  | e1 :: es =>
      EMultiApp (EApp e0 e1) es
  end.

(* [rec f x = e1]. *)

Definition RecBinding1Var (f x : var) (e1 : expr) : rec_bindings :=
  let rb := RecBinding f (AnonFun1Var x e1) in
  RecBiCons rb RecBiNil.

(* [rec f 'p = e] *)

Definition RecBinding1Pat f p e :=
  RecBiCons (RecBinding f $ AnonFun1Pat p e) RecBiNil.

(* [rec f = a] *)

Definition RecBinding1 f a :=
  RecBiCons (RecBinding f a) RecBiNil.

(* [let rec f x = e1 in e2]. *)

Definition ELetRec1Var (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1Var f x e1) e2.

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


Definition PMkTuple l :=
  let mk_tpl := fix mk_tpl pl :=
      match pl with
      | nil => PNil
      | cons h pl => PCons h $ mk_tpl pl
      end in
  PTuple (mk_tpl l).

Definition EMkTuple l :=
  let mk_tpl := fix mk_tpl pl :=
      match pl with
      | nil => ENil
      | cons h pl => ECons h $ mk_tpl pl
      end in
  ETuple (mk_tpl l).
