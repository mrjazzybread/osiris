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
  intros. simp.
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
  intros. simp_continue.
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
  intros. simp_continue.
Qed.

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
  intros. simp_continue.
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
  intros. simp_continue.
Qed.

(* -------------------------------------------------------------------------- *)

(* An example that involves an assertion. *)

Goal let e :=
  ESeq (EAssert ETrue) EFalse
  in simp (eval ε e) (ret VFalse).
Proof.
  simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* A recursive function that walks a list. *)

(* let rec walk xs =
     match xs with
     | [] -> ()
     | x :: xs -> walk xs *)

Definition walk : rec_bindings :=
  RecBinding1 "walk" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil EUnit;
    Branch (pCons (PVar "x") (PVar "xs"))
           (EApp (EVar "walk") (EVar "xs"))
    ].

Definition spec_walk (walk : val) :=
  ∀ (bs : list bool),
  simp (call walk (encode bs)) ok.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := eCons ETrue (eCons EFalse eNil) in
  simp (eval ε (walk_example e)) ok.
Proof.
  (* The code is pure and terminating and can be fully evaluated,
     if we accept to step into each call to [walk]. *)
  intros.
  simp.
  simp_continue.
  simp_enter. simp_continue.
  simp_enter. simp_continue.
  simp_enter.
Qed.

(* The following example illustrates how to reason about a local function.
   When the environment is about to be extended with a binding of the
   variable "walk" to a closure, we prove a specification for this closure,
   then we make this closure opaque. *)

Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := EnvCons "xs" (encode bs) ε in
  simp (eval η (walk_example (EVar "xs"))) ok.
Proof.
  intros. simp.
  (* The environment is about to be extended with a binding of the variable
     "walk" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  simp_specify "walk" spec_walk.
  (* Subgoal: prove that the closure satisfies [spec_walk]. *)
  { (* The environment [η] is irrelevant, since the code is in fact closed.
       Abstract it away. *)
    generalize η. clear bs η. intros η.
    unfold spec_walk.
    (* Prove the spec by induction on the list [bs]. *)
    induction bs as [| b bs ]; simp_enter.
    (* The [nil] branch has been automatically solved. *)
    (* This is the [cons] branch. *)
    simp_continue.
  }
  (* The variable "walk" is now bound to an abstract closure [walk]. *)
  intros walk Hwalk. simp_continue.
Qed.
