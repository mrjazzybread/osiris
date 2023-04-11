Require Import base lang free eval step safe safe_tactics encode.

(* let x = A() in y *)

Goal
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  is_safe EnvNil e (λ v, v = VConstant "A").
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

Goal is_safe EnvNil example (λ v, v = VData "A" (VTuple VNil)).
Proof.
  wp. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  is_safe env example2 (λ v, v = v1).
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

Lemma spec_example3:
  ∀ (id : val),
  (∀ v, safe (call id v) (λ v', v' = v)) →
  let env := EnvCons "id" id EnvNil in
  is_safe env example3 (λ v, v = VPair (VConstant "A") (VConstant "A")).
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

Lemma spec_identity:
  is_safe EnvNil identity (λ c, ∀ v, safe (call c v) (λ v', v' = v)).
Proof.
  wp. intros c. wp_call. reflexivity.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
  example3.

Lemma spec_example4:
  is_safe EnvNil example4 (λ v, v = VPair (VConstant "A") (VConstant "A")).
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
  is_safe EnvNil example5 (λ v, v = VFalse).
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
  is_safe EnvNil example4b (λ v, v = VUnit).
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
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  is_safe EnvNil example4c (λ v, v = VUnit).
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
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  is_safe EnvNil example4d (λ v, v = VUnit).
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
  is_safe EnvNil divergence (λ _, False).
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

Lemma spec_walk :
  ∀ (bs : list bool) η,
  safe (call (VCloRec η walk "walk") (encode_list bs)) (λ v, v = VUnit).
Proof.
  (* The environment that is captured by the closure does not matter,
     since the code is in fact closed. So, we must in fact universally
     quantify over this environment. *)
  (* TODO It would be desirable to avoid writing [VCloRec η walk "walk"]
     explicitly, as the structure of this value is an internal detail of
     the semantics. Instead we would like to refer this value as "the
     value produced by evaluating the recursive bindings [walk]". *)
  induction bs as [| b bs ]; intro η; wp_call.
  { reflexivity. }
  { wp_use IHbs. }
Qed.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  is_safe EnvNil (walk_example e) (λ v, v = encode ()).
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  wp. do 3 wp_call. reflexivity.
Qed.

Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := EnvCons "xs" (encode bs) EnvNil in
  is_safe η (walk_example (EVar "xs")) (λ v, v = encode ()).
Proof.
  intros. wp. wp_use spec_walk.
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

Lemma spec_length :
  ∀ `{Encode A} (xs : list A) η,
  safe
    (call (VCloRec η length "length") (encode_list xs))
    (λ v, v = encode (List.length xs)).
Proof.
  induction xs as [| x xs ]; intro η; wp_call.
  { reflexivity. }
  { wp_use IHxs. wp.
    rewrite Nat2Z.inj_succ.
    rewrite int.add_repr_repr.
    do 2 f_equal. lia. }
Qed.
