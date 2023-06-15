From osiris Require Import osiris.

Local Notation ε := EnvNil. (* TODO move *)

(* -------------------------------------------------------------------------- *)

(* A test involving [as_bool]. *)

Goal
  simp (as_bool (ret #true)) (ret true).
Proof.
  simp.
Qed.

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

Lemma solve_encode_A :
  VData "A" VUnit = #A.
Proof. reflexivity. Qed.

Lemma solve_encode_B :
  VData "B" VUnit = #B.
Proof. reflexivity. Qed.

Local Hint Resolve solve_encode_A solve_encode_B : encode.

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
  RecBinding1Var "walk" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil EUnit;
    Branch (pCons (PVar "x") (PVar "xs"))
           (EApp (EVar "walk") (EVar "xs"))
    ].

Definition spec_walk (walk : val) :=
  ∀ X `(_ : Encode X) (xs : list X),
  simp (call walk (encode xs)) ok.

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
  forall `{Encode X} (xs : list X),
  let η := EnvCons "xs" (encode xs) ε in
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
    generalize η. clear xs η. intros η.
    unfold spec_walk.
    (* Prove the spec by induction on the list [bs]. *)
    induction xs as [| x xs ]; simp_enter.
    (* The [nil] branch has been automatically solved. *)
    (* This is the [cons] branch. *)
    simp_continue.
  }
  (* The variable "walk" is now bound to an abstract closure [walk]. *)
  intros walk Hwalk. simp_continue.
Qed.

(* ------------------------------------------------------------------------- *)

(* A recursive function that computes the length of a list. *)

(* let rec length xs =
     match xs with
     | [] -> 0
     | x :: xs -> 1 + length xs *)

Definition length : rec_bindings :=
  RecBinding1Var "length" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil (EInt 0);
    Branch (pCons (PVar "x") (PVar "xs"))
           (EIntAdd (EInt 1) (EApp (EVar "length") (EVar "xs")))
    ].

Definition spec_length (length : val) :=
  ∀ X `(_ : Encode X) (xs : list X),
  simp (call length (encode xs)) (ret (encode (List.length xs))).

Goal
  ∀ η,
  spec_length (VCloRec η length "length").
Proof.
  unfold spec_length.
  induction xs as [| x xs ]; simp_enter.
  (* The [nil] branch has been automatically solved. *)
  (* This is the [cons] branch. *)
  simp_continue.
Qed.

(* ------------------------------------------------------------------------- *)

(* Now let us try to specify that [length] returns a nonnegative integer
   value. *)

Definition weak_spec_length (length : val) :=
  ∀ X `(_ : Encode X) (xs : list X),
  ∃ (n : Z),
  simp (call length (encode xs)) (ret (encode n)) ∧ (0 ≤ n)%Z.

Goal
  ∀ η,
  weak_spec_length (VCloRec η length "length").
Proof.
  unfold weak_spec_length.
  induction xs as [| x xs ].
  { eexists; split.
    + simp_enter. simp_continue.
    + lia. }
  { (* The proof goes through, but it is necessary to destruct the
       induction hypothesis and name the result of the recursive
       call *before* we reach the point where this call takes place.
       This is unpleasant. *)
    destruct IHxs as (n & ? & ?).
    eexists; split.
    + simp_enter. simp_continue.
    + lia. }
Qed.

(* ------------------------------------------------------------------------- *)

Definition weak_spec_length' (length : val) :=
  ∀ X `(_ : Encode X) (xs : list X),
  SIMP (call length (encode xs)) (λ n : Z, 0 ≤ n)%Z.

Goal
  ∀ η,
  weak_spec_length' (VCloRec η length "length").
Proof.
  unfold weak_spec_length'.
  induction xs as [| x xs ]; SIMP_enter; SIMP_continue.
  { lia. }
  { intros n ?. SIMP1. lia. }
Qed.
