From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

Require Import base lang sugar free eval step wp wp_tactics encode notations.


Context `{!osirisGS_gen hlc Σ}.




(* ---------------------------------------------------------------------------*)
(* Examples. *)


(* let x = A() in y *)

Goal forall s E,
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  ⊢ WP (eval EnvNil e) @ s; E {{ λ v, ⌜v = VConstant "A"⌝ }}.
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  intros. subst e. simpl.
  iApply wp_par_ret_ret.
  cbn.
Abort. (* expected *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)
Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
    ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
    EVar "x1".


(* An example of reasoning about straight-line code. *)

Goal
  ⊢ WP (eval EnvNil example) {{ λ v, ⌜v = VData "A" (VTuple VNil)⌝ }}.
Proof.
  by wp.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
    ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
    EVar "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  ⊢ WP (eval env example2) {{ λ v, ⌜v = v1⌝ }}.
Proof.
  iIntros. by wp.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

(* TODO. *)
Lemma spec_example3 s E:
  ∀ (id : val),
  ⊢ □ (∀ v, WP (call id v) @ s; E {{λ v', ⌜ v' = v⌝ }} ) -∗
  let env := EnvCons "id" id EnvNil in
  WP (eval env example3) @ s; E
                                {{λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  iIntros (id) "#Hid".
  wp.
  (* The two components of the pair are evaluated in parallel, and each of them
   * is a function application, which is itself evaluated in parallel. So we
   * have a tree of nested [Par]. *)
  wp_par.
  { iApply "Hid". }
  { iApply wp_covariant.
    - iApply "Hid".
    - iIntros (v->).
      wp. by wp_set_postcondition. }
  iNext.
  iIntros (??) "->->".
  by wp.
Qed.


(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is the
 * identity function. *)

Definition identity :=
  EFun1Var "x" (EVar "x").

Lemma spec_identity s E:
  ⊢ □ WP (eval EnvNil identity) @ s; E
                                       {{λ c, □ ∀ v, WP (call c v) @ s; E {{ λ v', ⌜v' = v⌝ }} }}.
Proof.
  iModIntro.
  wp.
  iModIntro. iIntros.
  by wp_call.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
    example3.

Lemma spec_example4 s E:
  ⊢ WP (eval EnvNil example4) @ s; E
                                     {{λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  unfold example4.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Abstract away [example3]; its spec suffices. *)
  generalize example3 spec_example3.
  intros example3 Hexample3.
  (* Attack the goal. *)
  iStartProof.
  wp.
  wp_use Hidentity.
  iIntros (id) "#Hid". wp.
  by wp_use Hexample3.
Qed.

(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5 s E:
  ⊢ WP (eval EnvNil example5) @ s; E {{ λ v, ⌜v = VFalse⌝ }}.
Proof.
  wp.
  iIntros ([|]).
  (* Subgoal: prove that [assert true] succeeds. *)
  { by wp. }
  (* Remainder: prove that [false] returns [false], as promised. *)
  by wp.
Qed.

(* let id = identity in
   (id id) id *)

Definition example4b :=
  ELet1Var "id" identity $
    let id := EVar "id" in
    EApp (EApp id id) EUnit.

Lemma spec_example4b s E:
  ⊢ WP (eval EnvNil example4b) @ s; E {{λ v, ⌜v = VUnit⌝ }}.
Proof.
  unfold example4b.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  iIntros (id) "#Hid".
  wp.
  (* We are looking at [id id]. *)
  wp_use "Hid".
  iIntros(?->).
  wp_use "Hid".
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELet1Var "id" identity $
    let id := EVar "id" in
    EApp id (EApp id EUnit).

Lemma spec_example4c s E:
  ⊢ WP (eval EnvNil example4c) @ s; E {{λ v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4c.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  iIntros (id) "#Hid".
  wp.
  (* We are looking at [id()]. *)
  wp_use "Hid".
  iIntros(?->).
  wp_use "Hid".
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELet1Var "id" identity $
    let id := EVar "id" in
    EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d s E:
  ⊢ WP (eval EnvNil example4d) @ s; E {{λ v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4d.
  (* Abstract away the [identity] function; its spec suffices. *)
  generalize identity spec_identity.
  intros identity Hidentity.
  (* Attack the goal. *)
  wp.
  (* Exploit the spec of the expression [identity]. *)
  wp_use Hidentity.
  iIntros (id) "#Hid".

  wp_par.

  (* id id *)
  { wp_use "Hid". }

  (* id () *)
  { wp_use "Hid". }

  iIntros (??->->).
  wp_use "Hid".
Qed.

(* let rec diverge x = diverge x in diverge() *)

Definition divergence :=
  ELetRec1 "diverge" "x" (EApp (EVar "diverge") (EVar "x")) $
    EApp (EVar "diverge") EUnit.

Lemma spec_divergence:
  ⊢ WP (eval EnvNil divergence) {{λ _, ⌜False⌝}}.
Proof.
  (* The tactic [wp_call] can be applied as many times as one wishes,
     since this term does not terminate, but the goal can never be
     reached in this way.
     TODO: reduce the gap between the tactics in [safe_*] and those in [wp_*] in
     order to use [wp_step] below. *)
  wp.
  Time do 100 wp_call.

Abort. (* TODO now that we have Löb induction, prove this goal *)

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

Lemma spec_walk s E:
  ∀ (bs : list bool) η,
  ⊢ WP (call (VCloRec η walk "walk") (encode_list bs)) @s; E
                                                             {{λ v, ⌜v = VUnit⌝}}.
Proof.
  (* The environment that is captured by the closure does not matter,
     since the code is in fact closed. So, we must in fact universally
     quantify over this environment. *)
  (* TODO It would be desirable to avoid writing [VCloRec η walk "walk"]
     explicitly, as the structure of this value is an internal detail of
     the semantics. Instead we would like to refer this value as "the
     value produced by evaluating the recursive bindings [walk]". *)
  induction bs as [| b bs ]; intro η; wp_call.
  { iPureIntro. reflexivity. }
  { wp_use IHbs. }
Qed.

Definition walk_example e :=
  ELetRec walk $
    EApp (EVar "walk") e.

(* TODO: resolve evar-related issues.

   Lemma spec_walk_example_concrete s E:
   let e := (eCons ETrue (eCons EFalse eNil)) in
   ⊢ WP (eval EnvNil (walk_example e)) @ s; E {{λ v, ⌜v = encode ()⌝}}.
   Proof.
     (* The code is pure and terminating and can be fully evaluated. *)
   wp. do 3 wp_call. reflexivity.
   Qed.

   Lemma spec_walk_example_abstract s E:
   forall (bs : list bool),
   let η := EnvCons "xs" (encode bs) EnvNil in
   ⊢ WP (eval η (walk_example (EVar "xs"))) @ s; E {{ λ v, ⌜v = encode ()⌝ }}.
   Proof.
   intros. wp. wp_use spec_walk.
   Qed. *)

(* ------------------------------------------------------------------------- *)

(* A recursive function that computes the length of a list. *)

(* let rec length xs =
    match xs with
    | [] -> 0
    | x :: xs -> 1 + length xs *)

Definition length : rec_bindings :=
  RecBinding1 "length" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil (EInt 0);
    Branch (pCons (PVar "x") (PVar "xs"))
           (EIntAdd (EInt 1) (EApp (EVar "length") (EVar "xs")))
  ].

Lemma spec_length s E :
  ∀ `{Encode A} (xs : list A) η,
  ⊢ WP
      (call (VCloRec η length "length") (encode_list xs))
      @ s; E
             {{ λ v, ⌜v = encode (List.length xs)⌝ }}.
Proof.
  induction xs as [| x xs ]; intro η; wp_call.
  { iPureIntro. reflexivity. }
  { wp_use IHxs.
    rewrite Nat2Z.inj_succ.
    iIntros(?->).
    wp.
    iPureIntro.
    rewrite int.add_repr_repr.
    do 2 f_equal. lia. }
Qed.

(* let l = ref "A" in
   l := "B";
   !l
 *)
Definition ref_store_load: expr :=
  ELet1Var "l" (ERef (EConstant "A")) $
  ELet1Var "_" (EStore (EVar "l") (EConstant "B")) $
  ELoad (EVar "l").

Goal forall s E,
  ⊢ WP (eval EnvNil ref_store_load)@s; E {{ λ v, ⌜ v = VConstant "B" ⌝ }}.
Proof.
  unfold ref_store_load.
  iIntros(??).
  wp.
  wp_ref ℓ "[Hℓ _]".
  wp_store "Hℓ".
  wp_load "Hℓ".
  iPureIntro. reflexivity.
Qed.
