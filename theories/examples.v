Require Import base lang free eval step safe wp wp_tactics encode.

(* let x = A() in y *)

Goal
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  wp EnvNil e (λ v, v = VConstant "A").
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  wp.
Abort. (* expected *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

(* An example of reasoning about straight-line code. *)

Goal wp EnvNil example (λ v, v = VData "A" (VTuple VNil)).
Proof.
  wp.
  wp_continue. wp_continue.
  reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  wp env example2 (λ v, v = v1).
Proof.
  intros. wp.
  wp_continue.
  wp_continue.
  reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

(* TODO not great *)
Ltac wp_set_postcondition :=
  match goal with |- ?φ ?v =>
    is_evar φ;
    instantiate (1 := λ w, w = v);
    reflexivity
  end.

Lemma spec_example3:
  ∀ (id : val),
  (∀ v, safe (call id v) (λ v', v' = v)) →
  let env := EnvCons "id" id EnvNil in
  wp env example3 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  intros id Hid.
  wp.
  (* The two components of the pair are evaluated in parallel,
     and each of them is a function application, which is itself
     evaluated in parallel. So we have a tree of nested [Par]. *)
  wp_par.
  { wp_use Hid. }
  { wp_use Hid.
    wp. wp_set_postcondition. }
  { wp_intros.
    wp. reflexivity. }
Qed.

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is
   the identity function. *)

Definition identity :=
  EFun "x" (EVar "x").

Definition spec_id (c : val) :=
  ∀ v, safe (call c v) (λ v', v' = v).

Goal
  wp EnvNil identity spec_id.
Proof.
  wp. intros c. wp_call. reflexivity.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
  example3.

Lemma spec_example4:
  wp EnvNil example4 (λ v, v = VPair (VConstant "A") (VConstant "A")).
Proof.
  unfold example4.
  wp.
  (* The environment is about to be extended with a binding of the variable
     "id" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  wp_specify "id" spec_id.
  (* Subgoal: prove that [fun x -> x] satisfies [spec_id]. *)
  { unfold spec_id. intros v. wp_call. reflexivity. }
  (* The variable "id" is now bound to an abstract closure [id]. *)
  intros id Hid.
  (* Abstract away [example3]; its spec suffices. *)
  generalize example3 spec_example3.
  intros example3 Hexample3.
  (* Attack the goal. *)
  wp_continue.
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
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit.

Lemma spec_example4b:
  wp EnvNil example4b (λ v, v = VUnit).
Proof.
  unfold example4b. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. intros v. wp_call. reflexivity. }
  intros id Hid. wp_continue.
  (* We are looking at [id id]. *)
  wp_use Hid.
  wp_use Hid.
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  wp EnvNil example4c (λ v, v = VUnit).
Proof.
  unfold example4c. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. intros v. wp_call. reflexivity. }
  intros id Hid. wp_continue.
  (* We are looking at [id()]. *)
  wp_use Hid.
  (* We are again looking at [id()]. *)
  wp_use Hid.
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  wp EnvNil example4d (λ v, v = VUnit).
Proof.
  unfold example4d. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. intros v. wp_call. reflexivity. }
  intros id Hid. wp_continue.
  (* Here, [wp] is unable to make progress because we are looking at two
     function calls in parallel. *)
  wp_par.

  (* id id *)
  { wp_use Hid. }

  (* id () *)
  { wp_use Hid. }

  wp_intros.
  wp_use Hid.
Qed.

(* let rec diverge x = diverge x in diverge() *)

Definition divergence :=
  ELetRec1 "diverge" "x" (EApp (EVar "diverge") (EVar "x")) $
  EApp (EVar "diverge") EUnit.

Lemma spec_divergence:
  wp EnvNil divergence (λ _, False).
Proof.
  (* The tactic [wp_step] can be applied as many times as one wishes,
     since this term does not terminate, but the goal can never be
     reached in this way. *)
  do 100 wp_step.
Abort. (* TODO once we have Löb induction, prove this goal *)

(* -------------------------------------------------------------------------- *)

(* A recursive function that walks a list. *)

(* let rec walk xs =
     match xs with
     | [] -> ()
     | x :: xs -> walk xs *)

Definition walk : rec_bindings :=
  RecBinding1 "walk" "xs" (
    EMatch (EVar "xs") (
      BrCons (Branch pNil EUnit) $
      BrCons (Branch (pCons (PVar "x") (PVar "xs"))
                     (EApp (EVar "walk") (EVar "xs"))
             ) $
      BrNil
    )
  ).

Definition spec_walk (walk : val) :=
  ∀ (bs : list bool),
  safe (call walk (encode_list bs)) (λ v, v = VUnit).

(* This is a subgoal that appears in the proof of
   [spec_walk_example_abstract] below. *)
Goal
  ∀ η,
  spec_walk (VCloRec η walk "walk").
Proof.
  unfold spec_walk.
  induction bs as [| b bs ]; wp_call; wp_continue.
  { reflexivity. }
  { wp_use IHbs. }
Qed.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  wp EnvNil (walk_example e) (λ v, v = encode ()).
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  wp.
  wp_continue.
  wp_call. wp_continue.
  wp_call. wp_continue.
  wp_call. wp_continue.
  reflexivity.
Qed.

(* The following example illustrates how to reason about a local function.
   When the environment is about to be extended with a binding of the
   variable "walk" to a closure, we prove a specification for this closure,
   then we make this closure opaque. *)

Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := EnvCons "xs" (encode bs) EnvNil in
  wp η (walk_example (EVar "xs")) (λ v, v = encode ()).
Proof.
  intros. wp.
  (* The environment is about to be extended with a binding of the variable
     "walk" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  wp_specify "walk" spec_walk.
  (* Subgoal: prove that the closure satisfies [spec_walk]. *)
  { (* The environment [η] is irrelevant, since the code is in fact closed.
       Abstract it away. *)
    generalize η. clear bs η. intros η.
    unfold spec_walk.
    (* Prove the spec by induction on the list [bs]. *)
    induction bs as [| b bs ]; wp_call; wp_continue.
    { reflexivity. }
    { wp_use IHbs. }
  }
  (* The variable "walk" is now bound to an abstract closure [walk]. *)
  intros walk Hwalk. wp_continue.
  (* The remains to exploit the hypothesis [Hwalk]. *)
  wp_use Hwalk.
Qed.

(* -------------------------------------------------------------------------- *)

(* A recursive function that computes the length of a list. *)

(* let rec length xs =
     match xs with
     | [] -> 0
     | x :: xs -> 1 + length xs *)

Definition length : rec_bindings :=
  RecBinding1 "length" "xs" (
    EMatch (EVar "xs") (
      BrCons (Branch pNil (EInt 0)) $
      BrCons (Branch (pCons (PVar "x") (PVar "xs"))
                     (EIntAdd (EInt 1) (EApp (EVar "length") (EVar "xs")))
             ) $
      BrNil
    )
  ).

Definition spec_length (length : val) :=
  ∀ A (eA : Encode A) (xs : list A),
  safe
    (call length (encode_list xs))
    (λ v, v = encode (List.length xs)).

Goal
  ∀ η,
  spec_length (VCloRec η length "length").
Proof.
  unfold spec_length.
  induction xs as [| x xs ]; wp_call; wp_continue.
  { reflexivity. }
  { wp_use IHxs. wp.
    rewrite Nat2Z.inj_succ.
    rewrite int.add_repr_repr.
    do 2 f_equal. lia. }
Qed.
