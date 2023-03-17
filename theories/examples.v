Require Import monads lang free eval step safe wp wp_tactics.

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELetVar "x" (EPair (EConstant "A") (EConstant "B")) $
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
  ELetVar "x" (EPair (EVar "z1") (EVar "z2")) $
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
  safe m φ'.

Ltac prove_texan :=
  unfold texan;
  let φ' := fresh "φ'" in
  let finished := fresh "finished" in
  intros φ' finished.

Lemma spec_example3:
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

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is
   the identity function. *)

Definition identity :=
  ERec "self" "x" (EVar "x").

Lemma spec_identity:
  wp EnvNil identity (λ c, ∀ v, texan (call c v) (λ v', v' = v)).
Proof.
  wp. intros c.
  prove_texan.
  wp. eauto.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELetVar "id" identity $
  example3.

Goal
  wp EnvNil example4 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  (* This goes too far! I was expecting to re-use the specs that were proved
     earlier about [example3] and [identity], but the interpreter executes
     the whole program. The next example shows how to avoid this problem. *)
  wp. reflexivity.
Qed.

Ltac wp_use H :=
  eapply safe_covariant; [ eapply H |].

Lemma spec_example4:
  wp EnvNil example4 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  unfold example4.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Abstract away [example3]; its spec suffices. *)
  generalize example3 spec_example3.
  intros example3 Hexample3.
  (* Attack the goal. *)
  wp.
  wp_use Hidentity. simpl. intros id Hid.
  wp_use (Hexample3 _ Hid).
  simpl. eauto.
Qed.
