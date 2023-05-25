From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics evalprime. (* TODO *)
From osiris.proofmode Require Import proofmode.

Local Notation ε := EnvNil. (* TODO move *)
Global Opaque call. (* TODO move *)

(* -------------------------------------------------------------------------- *)

(* An example algebraic data type. *)

Inductive data := A | B.

Global Instance encode_data : Encode data := {
  encode := λ data,
  match data with
  | A => VData "A" VUnit
  | B => VData "B" VUnit
  end
}.

(* -------------------------------------------------------------------------- *)

(* let x = A() in let A() = x in () *)

Goal let e :=
  ELet1Var "x" (EConstant "A") $
  ELet1 (PConstant "A") (EVar "x") $
  EUnit
  in simp (eval ε e) (ret (encode tt)).
Proof.
  simp.
  simp_continue.
  (* TODO why is [simp_continue] needed just once and not twice? *)
  (* TODO same question elsewhere *)
Qed.

(* -------------------------------------------------------------------------- *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Goal let e :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1"
  in simp (eval ε e) (ret (encode A)).
Proof.
  simp.
  simp_continue.
Qed.

(* -------------------------------------------------------------------------- *)

(* let x = A() in y *)

Goal let e :=
  ELet1Var "x" (EConstant "A") $ EVar "y"
  in simp (eval ε e) (ret (VConstant "A")).
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  simp.
  simp_continue.
Abort. (* expected *)

(* -------------------------------------------------------------------------- *)

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Goal let e :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1"
  in ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 ε) in
  simp (eval env e) (ret v1).
Proof.
  intros.
  simp.
  simp_continue.
Qed.

(* -------------------------------------------------------------------------- *)

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is the
   identity function. *)

Definition identity :=
  EFun1Var "x" (EVar "x").

Definition spec_id (c : val) : Prop :=
  ∀ v, simp (call c v) (ret v).

Goal
  ∃ c,
  simp (eval ε identity) (ret c) ∧ spec_id c.
Proof.
  eexists.
  split.
  + simp.
  + unfold spec_id. intros. simp_enter.
Qed.

(* -------------------------------------------------------------------------- *)

(* (id (A()), id (A())) *)

Goal
  let idA := EApp (EVar "id") (EConstant "A") in
  let e := EPair idA idA in
  ∀ (id : val),
  spec_id id →
  let env := EnvCons "id" id ε in
  simp (eval env e) (ret (VPair (VConstant "A") (VConstant "A"))).
Proof.
  intros ? ? id Hid ?.
  simp.
  (* The two components of the pair are evaluated in parallel, and
     each of them is a function application, which is itself evaluated
     in parallel. So we have a tree of nested [Par], which fortunately
     is automatically simplified by [simp]. Only one [Par] remains. *)
  eapply prove_simp_par.
  { eapply Hid. }
  { eapply prove_simp_bind.
    { eapply Hid. }
    { simp. }
  }
  simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO *)

(* The tactic [simp_specify x φ] should be used when the term begins with
   [concatenating eval η e δ], that is, when the environment is about to be
   extended with the environment fragment [δ].

   The tactic looks up the variable [x] in the environment fragment [δ]
   so as to find the value [v] of this variable. Then, it produces two
   subgoals:
   - the subgoal [φ v],
     letting the user prove that [v] satisfies the specification [φ];
   - the original goal,
     generalized under the form [∀ v, φ v → ...],
     which means that [v] becomes an opaque value
     about which nothing is known except that [φ v] holds. *)

Ltac simp_specify x φ :=
  lazymatch goal with |- simp (concatenating eval _ _ ?δ) _ =>
    let o := eval cbn in (lookup_name δ x) in
    lazymatch o with ret ?v =>
      let h := fresh in
      assert (φ v) as H; [| revert h; generalize v ]
    end
  end.

(* -------------------------------------------------------------------------- *)

(* let id = identity in
   (id (A()), id (A())) *)

Goal
  let idA := EApp (EVar "id") (EConstant "A") in
  let e :=
    ELet1Var "id" identity $
    EPair idA idA
  in simp (eval ε e) (ret (VPair (VConstant "A") (VConstant "A"))).
Proof.
  simp.
  (* The environment is about to be extended with a binding of the variable
     "id" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  simp_specify "id" spec_id.
  (* Subgoal: prove that the closure satisfies [spec_id]. *)
  { unfold spec_id. intros. simp_enter. }
  (* The variable "id" is now bound to an abstract closure [id]. *)
  intros id Hid.
  simp_continue.
  (* Continue the proof as in the previous example. *)
  eapply prove_simp_par.
  { eapply Hid. }
  { eapply prove_simp_bind.
    { eapply Hid. }
    { simp. }
  }
  simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* let id = identity in
   (id id) () *)

Goal let e :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit
  in simp (eval ε e) ok.
Proof.
  simp.
  (* Deal with the local binding of [id]. *)
  simp_specify "id" spec_id.
  { unfold spec_id. intros. simp_enter. }
  intros id Hid.
  simp_continue.
  (* We are looking at [id id]. *)
  eapply prove_simp_bind.
  { eapply Hid. }
  { eapply Hid. }
Qed.

(* let id = identity in
   id (id ()) *)

(* -------------------------------------------------------------------------- *)

(* let id = identity in
   id (id ()) *)

Goal let e :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit)
  in simp (eval ε e) ok.
Proof.
  simp.
  (* Deal with the local binding of [id]. *)
  simp_specify "id" spec_id.
  { unfold spec_id. intros. simp_enter. }
  intros id Hid.
  simp_continue.
  (* We are looking at the nested applications [id (id())]. *)
  eapply prove_simp_bind.
  { eapply Hid. }
  { eapply Hid. }
Qed.

(* -------------------------------------------------------------------------- *)

(* let id = identity in
   (id id) (id ()) *)

Goal let e :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit)
  in simp (eval ε e) ok.
Proof.
  simp.
  (* Deal with the local binding of [id]. *)
  simp_specify "id" spec_id.
  { unfold spec_id. intros. simp_enter. }
  intros id Hid.
  simp_continue.

  (* Here, [simp] is unable to make progress because we are looking at two
     function calls in parallel. *)
  eapply prove_simp_par; [| | cbn ].
  (* id id *)
  { eapply Hid. }
  (* id () *)
  { eapply Hid. }

  eapply Hid.
Qed.

(* -------------------------------------------------------------------------- *)

(* An example that involves an assertion. *)

Goal let e :=
  ESeq (EAssert ETrue) EFalse
  in simp (eval ε e) (ret VFalse).
Proof.
  simp.
  eapply prove_simp_bind.
  (* Subgoal: prove that [assert true] succeeds. *)
  { simp. }
  (* Remainder: prove that [false] returns [false], as promised. *)
  { simp. }
Qed.
