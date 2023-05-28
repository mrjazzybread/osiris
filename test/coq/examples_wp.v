From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics tactics notations.


Context `{!osirisGS_gen hlc Σ}.



(* ---------------------------------------------------------------------------*)
(* Examples. *)


(* let x = A() in y *)

Goal
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  ⊢ WP (eval EnvNil e) {{ λ v, ⌜v = VConstant "A"⌝ }}.
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  iIntros.
  wp.
  wp_continue.
Abort. (* expected *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

(* An example of reasoning about straight-line code. *)

Goal ⊢ WP (eval EnvNil example) {{ λ v, ⌜v = VData "A" (VTuple VNil)⌝ }}.
Proof.
  wp.
  wp_continue. wp_continue.
  iPureIntro. reflexivity.
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
  iIntros. wp.
  wp_continue.
  wp_continue.
  iPureIntro. reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

Lemma spec_example3:
  ∀ (id : val),
  ⊢ □ (∀ v, WP (call id v) {{ λ v', ⌜ v' = v⌝ }} ) -∗
  let env := EnvCons "id" id EnvNil in
  WP (eval env example3) {{ λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  iIntros (id) "#Hid".
  wp.
  (* The two components of the pair are evaluated in parallel, and each of them
     is a function application, which is itself evaluated in parallel. So we
     have a tree of nested [Par]. *)
  wp_par.
  { wp_use "Hid". }
  { wp_use "Hid".
    iIntros (v->).
    wp. wp_set_postcondition.
    iPureIntro. reflexivity. }
  { iIntros (??) "->->".
    wp. iPureIntro. reflexivity. }
Qed.

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is the
   identity function. *)

Definition identity :=
  EFun1Var "x" (EVar "x").

Definition spec_id (c: val) : iProp Σ :=
  □ ∀ v, WP call c v {{ λ v', ⌜ v' = v ⌝ }}.

Goal
  ⊢ WP (eval EnvNil identity) {{ spec_id }}.
Proof.
  wp. iModIntro. iIntros.
  wp_call. iPureIntro. reflexivity.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
  example3.

Lemma spec_example4:
  ⊢ WP (eval EnvNil example4)
    {{λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  unfold example4.
  wp.
  (* The environment is about to be extended with a binding of the variable
     "id" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  wp_specify "id" spec_id.
  (* Subgoal: prove that [fun x -> x] satisfies [spec_id]. *)
  { unfold spec_id. iModIntro. iIntros (v). wp_call.
    iPureIntro. reflexivity. }
  (* The variable "id" is now bound to an abstract closure [id]. *)
  iIntros (id) "Hid".

  (* Abstract away [example3]; its spec suffices. *)
  generalize example3 spec_example3.
  intros example3 Hexample3.
  (* Attack the goal. *)
  iStartProof.
  wp_continue.
  wp_use Hexample3.
  wp_use "Hid".
Qed.

(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5:
  ⊢ WP (eval EnvNil example5) {{ λ v, ⌜v = VFalse⌝ }}.
Proof.
  wp.
  iIntros ([|]).
  (* Subgoal: prove that [assert true] succeeds. *)
  { by wp. }
  (* Remainder: prove that [false] returns [false], as promised. *)
  by wp.
Qed.

(* let id = identity in
   (id id) () *)

Definition example4b :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit.

Lemma spec_example4b:
  ⊢ WP eval EnvNil example4b {{λ v, ⌜v = VUnit⌝ }}.
Proof.
  unfold example4b. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. iIntros (v).
    iModIntro. wp_call.
    iPureIntro. reflexivity. }
  iIntros (id) "#Hid". wp_continue.
  (* We are looking at [id id]. *)
  wp_use "Hid". iIntros(?->).
  wp_use "Hid".
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  ⊢ WP eval EnvNil example4c {{λ v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4c. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. iIntros (v).
    iModIntro. wp_call.
    iPureIntro. reflexivity. }
  iIntros (id) "#Hid". wp_continue.
  (* We are looking at [id()]. *)
  wp_use "Hid". iIntros(?->).
  (* We are again looking at [id()]. *)
  wp_use "Hid".
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  ⊢ WP eval EnvNil example4d {{λ v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4d. wp.
  (* Deal with the local binding of [id]. *)
  wp_specify "id" spec_id.
  { unfold spec_id. iIntros (v).
    iModIntro. wp_call.
    iPureIntro; reflexivity. }
  iIntros (id) "#Hid". wp_continue.
  (* Here, [wp] is unable to make progress because we are looking at two
     function calls in parallel. *)
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
  ELetRec1Var "diverge" "x" (EApp (EVar "diverge") (EVar "x")) $
  EApp (EVar "diverge") EUnit.

Lemma spec_divergence:
  ⊢ WP eval EnvNil divergence {{ λ _, ⌜False⌝ }}.
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
  RecBinding1Var "walk" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil EUnit;
    Branch (pCons (PVar "x") (PVar "xs"))
           (EApp (EVar "walk") (EVar "xs"))
    ].

Definition spec_walk (walk : val): iProp Σ :=
  ∀ (bs : list bool),
  WP call walk (encode_list bs) {{ λ v, ⌜v = VUnit⌝ }}.
  (* TODO should always use [encode], not [encode_list] *)

(* This is a subgoal that appears in the proof of
   [spec_walk_example_abstract] below. *)
Goal
  ∀ η,
  ⊢ spec_walk (VCloRec η walk "walk").
Proof.
  unfold spec_walk.
  iIntros (η bs).
  iInduction bs as [| b bs ] "IHbs"; wp_call; wp_continue.
  { iPureIntro. reflexivity. }
  { wp_use "IHbs". }
Qed.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  ⊢ WP eval EnvNil (walk_example e) {{ λ v, ⌜v = encode tt⌝ }}.
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  iIntros.
  wp.
  wp_continue.
  wp_call. wp_continue.
  wp_call. wp_continue.
  wp_call. wp_continue.
  iPureIntro. reflexivity.
Qed.

(* The following example illustrates how to reason about a local function.
   When the environment is about to be extended with a binding of the
   variable "walk" to a closure, we prove a specification for this closure,
   then we make this closure opaque. *)
Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := EnvCons "xs" (encode bs) EnvNil in
  ⊢ WP (eval η (walk_example (EVar "xs"))) {{ λ v, ⌜v = encode tt⌝ }}.
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
    iIntros(bs).
    iInduction bs as [| b bs ] "IHbs"; wp_call; wp_continue.
    { iPureIntro. reflexivity. }
    { wp_use "IHbs". }
  }
  (* The variable "walk" is now bound to an abstract closure [walk]. *)
  iIntros (walk) "Hwalk". wp_continue.
  (* The remains to exploit the hypothesis [Hwalk]. *)
  wp_use "Hwalk".
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
  ∀ A (eA : Encode A) (xs : list A),
  ⊢ WP call length (encode_list xs)
       {{ λ v, ⌜v = encode (List.length xs)⌝ }}.

Goal
  ∀ η,
  spec_length (VCloRec η length "length").
Proof.
  unfold spec_length. intros η ?? xs.
  iInduction (xs) as [| x xs ] "IHxs"; wp_call; wp_continue.
  { iPureIntro. reflexivity. }
  { wp_use "IHxs". wp. iIntros(?->).
    rewrite Nat2Z.inj_succ. wp. iPureIntro.
    rewrite int.add_repr_repr.
    do 2 f_equal. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

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
  wp_alloc l "[Hl _]". wp_continue.
  wp_store "Hl". wp_continue.
  wp_load "Hl".
  iPureIntro. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* On verifying modules. *)

(* [simple_module] defines stand alone module expression.
   There are no side-effects to deal with. *)
Definition simple_module: mexpr :=
  MkStruct
    [
      ILet (Binding1 (PVar "f")
                     identity);
      ILet (Binding1 (PVar "g") $
                     EVar "f");
      ILet (Binding1 (PVar "h") $
                     EApp (EVar "f") (EVar "g"))
    ].

Definition simple_module_spec: val → iProp Σ :=
  module_spec $
  [
    ("f", spec_id) ;
    ("h", spec_id)
  ]
.


Goal
  ⊢ WP eval_mexpr EnvNil simple_module {{ simple_module_spec }}.
Proof.
  wp.

  (* [f] is about to be added to the environment *)
  wp_specify "f" spec_id.
  { iIntros(v). iModIntro.
    wp_call. iPureIntro. reflexivity. }
  iIntros (id) "#Hid". wp_continue.

  (* [g] is about to be added to the environment *)
  wp_specify "g" spec_id.
  { iIntros(v). iModIntro.
    wp_use "Hid". }
  iIntros (id') "#Hid'". wp_continue.

  (* We can use the spec of [f] at the function call (of the body of [h]). *)
  wp_use "Hid". iIntros (?->). wp.
  wp_continue.

  (* Proving the trivial post condition using the aforementioned specs. *)
  wp_module_spec.
Qed.

From osiris.libs Require Import Stdlib.

Goal
  ⊢ WP call Stdlib__add #3 {{ λ v,
       WP call v #3 {{ λ res, ⌜res = #6⌝ }} }}.
Proof.
  wp. iPureIntro. reflexivity.
Qed.
