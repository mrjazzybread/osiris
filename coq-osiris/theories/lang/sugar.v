From osiris.lang Require int.
From osiris Require Import base.
From osiris.lang Require Import syntax.

(* The sugar in this file can help construct ASTs by hand in Coq. *)

(* The definitions in this file may be used by the Osiris translator. *)

(* ------------------------------------------------------------------------ *)

(* Decorations. *)

(* A decoration is a string (typically, a snippet extracted out of the
   OCaml source file) that has no semantic meaning. *)

Definition deco {A} (decoration : string) (a : A) :=
  a.

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

(* Branches *)

Definition Branch1 p e : list branch :=
  [Branch p e].

(* ------------------------------------------------------------------------ *)

(* Pairs: pattern, expression, value. *)

Definition PPair p1 p2 :=
  PTuple [p1; p2].

Definition EPair e1 e2 :=
  ETuple [e1; e2].

Definition VPair v1 v2 :=
  VTuple [v1; v2].

(* Tuples of arity 1. *)

(* Used only in the encoding of data constructors; see e.g. [VSome]. *)

Notation VTuple1 v1 :=
  (VTuple [v1]).

(* Tuples of arity 3. *)

Notation VTuple3 v1 v2 v3 :=
  (VTuple [v1; v2; v3]).

(* Tuples of arity 4. *)

Notation VTuple4 v1 v2 v3 v4 :=
  (VTuple [v1; v2; v3; v4]).

(* ------------------------------------------------------------------------ *)

(* Options: values. *)

Definition VNone :=
  (VConstant "None").

Definition VSome v :=
  (VData "Some" (VTuple1 v)).

(* ------------------------------------------------------------------------ *)

(* Lists: patterns, expressions, values. *)

Definition pNil :=
  (PConstant "[]").

Definition pCons p1 p2 :=
  (PData "::" (PPair p1 p2)).

Definition eNil :=
  (EConstant "[]").

Definition eCons e1 e2 :=
  (EData "::" (EPair e1 e2)).

Definition VNil :=
  (VConstant "[]").

Definition VCons v1 v2 :=
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

Definition Binding1 (p : pat) (e : expr) : list binding :=
  [Binding p e].

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

(* The variable [x] must not occur micro in [bs]. *)

(* We use a reserved name for [x]. Provided end users do not use such a
   reserved name in their OCaml source code, we can be assured that [x]
   does not occur micro in [bs]. *)

(* TODO: consider replacing AnonFunction by a Hoare-style reasoning rule
   allowing us to discard the anonymous argument's name *)

Definition AnonFunction (bs : list branch) : anonfun :=
  let x := "__osiris_anonymous_arg" in
  AnonFun1Var x $
  EMatch (EVar x) bs.

Definition EFunction (bs : list branch) :=
  EAnonFun (AnonFunction bs).

(* [fun p -> e] is sugar for [fun x -> match x with p -> e]. *)

(* It is the same as [function p -> e]. *)

(* It is a special case of the previous sugar. *)

Definition AnonFun1Pat (p : pat) (e : expr) : anonfun :=
  AnonFunction [Branch p e].

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

Definition RecBinding1Var (f x : var) (e1 : expr) : list rec_binding :=
  [RecBinding f (AnonFun1Var x e1)].

(* [rec f 'p = e] *)

Definition RecBinding1Pat f p e :=
  [RecBinding f $ AnonFun1Pat p e].

(* [rec f = a] *)

Definition RecBinding1 f a :=
  [RecBinding f a].

(* [let rec f x = e1 in e2]. *)

Definition ELetRec1Var (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1Var f x e1) e2.

(* ------------------------------------------------------------------------ *)

(* Sugar for module expressions. *)

(* [open π]. *)

Definition IOpenMkPath xs :=
  (IOpen (MPath (MkPath xs))).

(* [include π]. *)

Definition IIncludeMkPath xs :=
  (IInclude (MPath (MkPath xs))).
