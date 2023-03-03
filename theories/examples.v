Require Import monads lang free eval spec handle wp soundness handle_spec.

(* TODO move elsewhere *)
(* Syntax. *)

Definition ELet p e1 e2 :=
  EMatch e1 (BCons (Branch p e2) BNil).

Definition EUnit :=
  ETuple ENil.

Definition VUnit :=
  VTuple VNil.

Definition EConstant c :=
  EData c EUnit.

Definition VConstant c :=
  VData c VUnit.

Definition EPair e1 e2 :=
  ETuple (ECons e1 (ECons e2 ENil)).

Definition PPair p1 p2 :=
  PTuple (PCons p1 (PCons p2 PNil)).

Definition VPair v1 v2 :=
  VTuple (VCons v1 (VCons v2 VNil)).

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet (PVar "x") (EPair (EConstant "A") (EConstant "B")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Eval cbv in eval EnvNil example.

(* An example of reasoning about straight-line code. *)

Goal wp EnvNil example (λ v, v = VData "A" (VTuple VNil)).
Proof.
  wp. reflexivity.
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
  intros. wp. reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.


Definition texan {A} (m : free A) (φ : A → Prop) :=
  ∀ (φ' : A → Prop),
  (∀ v, φ v → φ' v) →
  @handle spec _ _ _ _ m ∋ φ'. (* TODO *)

Goal
  ∀ (id : val),
  (∀ v, texan (call id v) (λ v', v' = v)) →
  let env := EnvCons "id" id EnvNil in
  wp env example3 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  intros id Hid.
  wp.
  apply Hid. intros v ?. subst v.
  wp.
  apply Hid. intros v ?. subst v.
  wp.
  reflexivity.
Qed.
