Require Import base lang free eval step safe wp wp_tactics.
Require Import Setoid Morphisms.

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELetVar "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

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

(* TODO not great *)
Ltac wp_set_postcondition :=
  match goal with |- ?φ ?v =>
    is_evar φ;
    instantiate (1 := λ w, w = v);
    reflexivity
  end.

Lemma Par_Par'_eq {A B C} (a: free A) (b: free B) (ko: A * B -> free C):
  Par a b ko (λ _: (), Next) = Par' a b ko.
Proof. reflexivity. Qed.

Ltac wp_par_simpl :=
  (repeat rewrite Par_Par'_eq);
  (try (rewrite call_ret_ret; try reflexivity)).
Ltac wp_par' := repeat (wp_par_simpl + wp_par).

Lemma spec_example3:
  ∀ (id : val),
  (∀ v, safe (call id v) (λ v', v' = v)) →
  let env := EnvCons "id" id EnvNil in
  wp env example3 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  intros id Hid.
  wp_step.
  wp.
  (* The two components of the pair are evaluated in parallel,
     and each of them is a function application, which is itself
     evaluated in parallel. So we have a tree of nested [Par]. *)
  wp_par_simpl.
  wp_par.
  { apply Hid. }
  { wp. wp_use Hid. wp. wp_set_postcondition. }
  wp_intros. wp.
  reflexivity.
Qed.

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is
   the identity function. *)

Definition identity :=
  ERec "self" "x" (EVar "x").

Lemma spec_identity:
  wp EnvNil identity (λ c, ∀ v, safe (call c v) (λ v', v' = v)).
Proof.
  wp. intros c.
  wp. reflexivity.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELetVar "id" identity $
  example3.

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
  wp_use Hidentity.
  revert a H; intros id Hid. (* TODO wp_intros does not let us pick names *)
  wp_use Hexample3.
  wp_use Hid.
Qed.

(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5:
  wp EnvNil example5 (λ v, v = VFalse).
Proof.
  wp.
  (* Subgoal: prove that [assert true] succeeds. *)
  { reflexivity. }
  (* Remainder: prove that [false] returns [false], as promised. *)
  reflexivity.
Qed.

(* let id = identity in
   (id id) id *)

Definition example4b :=
  ELetVar "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit.

Lemma spec_example4b:
  wp EnvNil example4b (λ v, v = VUnit).
Proof.
  unfold example4b.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  revert a H; intros id Hid. (* TODO wp_intros does not let us pick names *)
  wp.
  (* We are looking at [id id]. *)
  wp_use Hid.
  wp_use Hid.
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELetVar "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  wp EnvNil example4c (λ v, v = VUnit).
Proof.
  unfold example4c.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  revert a H; intros id Hid. (* TODO wp_intros does not let us pick names *)
  wp.
  (* We are looking at [id()]. *)
  wp_use Hid.
  wp_use Hid.
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELetVar "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  wp EnvNil example4d (λ v, v = VUnit).
Proof.
  unfold example4d.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  revert a H; intros id Hid. (* TODO wp_intros does not let us pick names *)
  (* Here, [wp] is unable to make progress because we are looking at two
     function calls in parallel. *)
  wp.

  assert (H: forall v, refinement val (call id v) (ret v)).
  { intros???%invert_safe_result. now wp_use Hid. }

  wp_par'.

  (* Subgoal 1. Application [id ()]. *)
  { wp_use Hid. }


  (* Subgoal 2. [id id <= id] . *)
  { now rewrite H. }

  (* Subgoal 3. [id() <= ()]. *)
  { now rewrite H. }
Qed.
