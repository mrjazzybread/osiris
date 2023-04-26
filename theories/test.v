Require Import base lang free eval step steps.

(* We want to test our semantics, so as to ensure that it seems to be
   consistent with our expectations and with the informal definition
   of the semantics of OCaml.  *)

(* A difficulty is that the semantics is non-deterministic: in particular,
   function applications and tuples are evaluated in parallel. This gives
   rise to an exponential number of reduction paths. We do not wish to
   explore all paths, so we just verify that there exists one path that
   leads to the expected result. For now, this is good enough. Furthermore,
   the proof system already explores all paths, by construction, and can be
   used to prove facts of the form "for every result v, the assertion φ v
   holds". Here, we prove facts of the form "it is possible to reach the
   result v", which are of a different form, hence also valuable. *)

(* -------------------------------------------------------------------------- *)

(* [reduces e v] means that the expression [e] can reduce to the value [v]. *)

Local Notation reduces e v :=
  (∃ n, steps n (eval EnvNil e) (ret v)).

(* [fails e] means that the expression [e] can fail. *)

Local Notation fails e :=
  (∃ n, steps n (eval EnvNil e) fail).

(* -------------------------------------------------------------------------- *)

(* The tactic [step] solves a goal of the form [step e ?e']. *)

(* The construct [EAssert e] is evaluated as a choice between skipping the
   dynamic test and performing the dynamic test (eval.v). Here, we want the
   dynamic tests to be performed, so we choose the right-hand side. This is
   done by using [StepFlip false]. It is brittle, but should do for now. *)

Local Ltac step :=
  first [
    eapply StepEval; [ reflexivity ]
  | eapply StepLoop; [ reflexivity ]
  | eapply (@StepFlip val false)
  | eapply StepParRetRet
  | eapply StepParLeft; [ step ]
  | eapply StepParRight; [ step ]
  ].

(* The tactic [steps] solves a goal of the form [steps ?n e v]. *)

Local Ltac steps :=
  cbn;
  repeat first [
    eapply (StepsZero 0)
  | eapply StepsSucc; [ step | cbn ]
  ].

(* The tactic [reduces] solves a goal of the form [reduces e v]. *)

Local Ltac reduces :=
  intros; eexists; steps.

(* -------------------------------------------------------------------------- *)

(* Tests. *)

Lemma test_assert_false :
  let e := EAssert EFalse in
  fails e.
Proof. reduces. Qed.

Lemma test_assert_true :
  let e := EAssert ETrue in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_seq_assert_true_unit :
  let e := ESeq (EAssert ETrue) EUnit in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_pair :
  let e := EPair ETrue EFalse in
  let v := VPair VTrue VFalse in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_and_access_1 :
  let e := ERecord (FECons "foo" (EInt 0) (FECons "bar" ETrue FENil)) in
  let e := ERecordAccess e "bar" in
  let v := VTrue in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_and_access_2 :
  let e := ERecord (FECons "foo" (EInt 0) (FECons "bar" ETrue FENil)) in
  let e := ERecordAccess e "foo" in
  let v := VInt (int.repr 0) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_call :
  let e :=
    ELet1Var "pair" (
      EFun "x" (EFun "y" (
        EPair (EVar "x") (EVar "y")
    ))) $
    EApp (EApp (EVar "pair") ETrue) EFalse
  in
  let v := VPair VTrue VFalse in
  reduces e v.
Proof. reduces. Qed.

Lemma test_divergent_while_loop :
  let e := EWhile ETrue EUnit in
  ∃ e', steps 10 (eval EnvNil e) e'.
Proof. reduces. Qed.

Lemma test_trivial_while_loop :
  let e := EWhile EFalse EUnit in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_for_loop :
  (* for i = 0 to 1 do () done *)
  let e := EFor "i" (EInt 0) (EInt 1) EUnit in
  let v := VUnit in
  reduces e v.
Proof.
  (* This example is quite artificial, as we must manually force the
     execution of the loop. It is a good sanity check anyway. *)
  reduces.

  (* Iteration 0. *)
  (* Unroll this iteration. *)
  unfold loop.
  (* Simplify the comparison. *)
  rewrite int.lt_repr_repr by int.prove_representable_30. cbn.
  (* Simplify the incrementation. *)
  unfold int.one. rewrite int.add_repr_repr. unfold Z.add. simpl.
  (* Step. *)
  steps.

  (* Iteration 1. *)
  unfold loop.
  rewrite int.lt_repr_repr by int.prove_representable_30. cbn.
  unfold int.one. rewrite int.add_repr_repr. unfold Z.add. simpl.
  steps.

  (* Iteration 2. *)
  unfold loop.
  rewrite int.lt_repr_repr by int.prove_representable_30. cbn.
  steps.

Qed.
