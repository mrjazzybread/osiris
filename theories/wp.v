Require Import lang free eval spec handle.

(* Instantiate the generic [handle] with the [spec] monad. *)

Definition wp η e φ :=
  run η e φ.

(* An example. *)

Definition ELet p e1 e2 :=
  EMatch e1 (BCons (Branch p e2) BNil).

Definition EUnit :=
  ETuple ENil.

Definition EConstant c :=
  EData c EUnit.

Definition EPair e1 e2 :=
  ETuple (ECons e1 (ECons e2 ENil)).

Definition PPair p1 p2 :=
  PTuple (PCons p1 (PCons p2 PNil)).

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet (PVar "x") (EPair (EConstant "A") (EConstant "B")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Eval cbv in eval EnvNil example.

(* An example of reasoning about straight-line code. *)

Goal wp EnvNil example (λ v, v = VData "A" (VTuple VNil)).
Proof.
  cbv. rewrite handle_fixed_point. cbv. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet (PVar "x") (EPair (EVar "z1") (EVar "z2")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  wp env example2 (λ v, v = v1).
Proof.
  intros. cbv. rewrite handle_fixed_point. cbv. reflexivity.
Qed.
