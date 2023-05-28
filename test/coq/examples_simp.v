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
  simp_continue. simp_ret.
Qed.

(* ------------------------------------------------------------------------- *)

(* Now let us try to specify that [length] returns a nonnegative integer
   value. *)

Global Opaque int.signed int.repr int.add int.mul. (* TODO *)

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
    + simp_enter. simp_continue. simp_ret.
    + lia. }
Qed.

(* ------------------------------------------------------------------------- *)

(* TODO *)

Definition SIMP `{Encode X} (m : free val) (φ : X → Prop) :=
  ∃ x, simp m (ret (encode x)) ∧ φ x.

Lemma SIMP_det `{Encode X} m (φ : X → Prop) v x :
  simp m (ret v) →
  v = encode x →
  φ x →
  SIMP m φ.
Proof.
  unfold SIMP. intros. subst. eauto.
Qed.

Ltac SIMP_det :=
  eapply SIMP_det; [ simp | eauto | eauto ].

Lemma SIMP_ret `{Encode X} (φ : X → Prop) v x :
  v = encode x →
  φ x →
  SIMP (ret v) φ.
Proof.
  eauto using SIMP_det with simp.
Qed.

Lemma SIMP_simp `{Encode X} m m' φ :
  simp m m' →
  SIMP m' φ →
  SIMP m φ.
Proof.
  unfold SIMP.
  intros ? (x & ? & ?).
  eauto with simp.
Qed.

Lemma SIMP_bind X Y (_ : Encode X) (_ : Encode Y)
   m f (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f (encode x)) ψ) →
  SIMP (bind m f) ψ.
  (* This is [@bind val val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_bind.
Qed.

Ltac encode :=
  eauto.

Ltac SIMP_ret :=
  eapply SIMP_ret; [ encode |].

Ltac SIMP_simp :=
  eapply SIMP_simp; [ simp_really |].

Ltac SIMP_bind :=
  eapply @SIMP_bind.

Ltac SIMP :=
  try SIMP_simp;
  repeat rewrite bind_bind;
  first [
    SIMP_ret
  | SIMP_bind; [ solve [ SIMP ] | SIMP ]
  | idtac
  ].

Ltac SIMP_enter :=
  with_strategy transparent [call] unfold call; SIMP.

Ltac SIMP_continue :=
  cbn;
  lazymatch goal with |- SIMP (concatenating _ _ _ _) _ =>
    unfold concatenating; (* TODO restrict to head occurrence *)
    SIMP
  | _ =>
    fail "[SIMP_continue] expects a goal of the form [simp (concatenating ...) _]"
  end.

Opaque SIMP.

(* ------------------------------------------------------------------------- *)

Definition weak_spec_length' (length : val) :=
  ∀ X `(_ : Encode X) (xs : list X),
  SIMP (call length (encode xs)) (λ n : Z, 0 ≤ n)%Z.

Goal
  ∀ η,
  weak_spec_length' (VCloRec η length "length").
Proof.
  unfold weak_spec_length'.
  induction xs as [| x xs ].
  { SIMP_enter. SIMP_continue. lia. }
  { SIMP_enter. SIMP_continue.
    (* TODO We must explicitly give the type of the left-hand side of
            the sequence, otherwise Coq automatically makes an incorrect
            choice. Painful! *)
    eapply (@SIMP_bind Z).
    + rewrite encode_list_is_encode. eauto.
    + cbn. intros n ?. SIMP_ret. equality. lia. }
Qed.
