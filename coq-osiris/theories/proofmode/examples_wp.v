From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
Local Transparent eval.

Context `{!osirisGS Σ}.

(* ---------------------------------------------------------------------------*)
(* Examples. *)

(* let x = A() in y *)

Goal
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  ⊢ WP eval [] e @ NotStuck; ⊤ {{ RET v, ⌜v = VConstant "A"⌝ }}.
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

Goal ⊢ WP (eval [] example) {{ RET v, ⌜v = VConstant "A"⌝ }}.
Proof.
  wp. do 2 wp_continue.
  iPureIntro. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := [("z1", v1); ("z2", v2)] in
  ⊢ WP (eval env example2) {{ RET v, ⌜v = v1⌝ }}.
Proof.
  iIntros. wp.
  do 2 wp_continue.
  iPureIntro. reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

Lemma spec_example3:
  ∀ (id : val),
  ⊢ □ (∀ v, WP (call id v) {{ RET v', ⌜ v' = v⌝ }} ) -∗
  let env := [("id", id)] in
  WP (eval env example3) {{ RET v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  iIntros (id) "#Hid".
  wp.
  wp_par.
  3,4: try wp_absurd.
  { wp_use "Hid". }
  { wp_bind. wp_use "Hid".
    (* Coq throws an anomaly if we don't invoke a [subst] here and call
        [wp_set_postcondition]. *)
    wp_pure_postcondition; subst.
    cbn. wp. wp_set_postcondition. }
  { cbn. iIntros (??) "%H %H'"; inversion H'; subst.
    wp; by iPureIntro. }
Qed.

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is the
   identity function. *)

Definition identity :=
  EFun1Var "x" (EVar "x").

Definition spec_id (c: val) : iProp Σ :=
  □ ∀ v, WP call c v {{ RET v', ⌜ v' = v ⌝ }}.

Goal
  ⊢ WP (eval [] identity) {{ RET v, spec_id v }}.
Proof.
  wp. iModIntro. iIntros. wp. equality.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
  example3.

Lemma spec_example4:
  ⊢ WP (eval [] example4)
    {{ RET v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  unfold example4.
  wp. wp_bind.
  (* The environment is about to be extended with a binding of the variable
     "id" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  oSpecify "id" spec_id vid "#Hid".
  (* Subgoal: prove that [fun x -> x] satisfies [spec_id]. *)
  { unfold spec_id. iModIntro. iIntros (v). wp. equality. }
  (* The variable "id" is now bound to an abstract closure [id]. *)

  (* Abstract away [example3]; its spec suffices. *)
  (* TODO this is broken; [example3] has been unfolded/simplified already
  generalize example3 spec_example3.
  intros example3 Hexample3.
  (* Attack the goal. *)
  wp_continue.
  iApply wp_simp; [ simp_really |]. (* TODO [wp] should do this *)
  wp_use Hexample3.
  wp_use "Hid". *)
Abort.

(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5:
  ⊢ WP (eval [] example5) {{ RET v, ⌜v = VFalse⌝ }}.
Proof.
  (* TODO make [choose] opaque somewhere else *)
  (* TODO and prove a [wp] rule for [eval (EAssert _)]
          so we do not need to descend to the level of [choose] *)
  Opaque choose.
  wp.
  (* Applying [wp_bind] (unary) followed with [wp_choose_ok]
     duplicates the proof of the continuation. We must use
     [wp_bind_binary] to introduce a cut and avoid duplication. *)
  iApply wp_bind_binary.
  + iApply (wp_choose_ok _ (True)%I).
    - auto.
    - iModIntro. iIntros "_". wp. auto.
  + iIntros (??). unfold lift_ipure. destruct v.
    - wp. equality.
    - iPureIntro; apply e.
Qed.

(* let id = identity in
   (id id) () *)

Definition example4b :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit.

Lemma spec_example4b:
  ⊢ WP eval [] example4b {{ RET v, ⌜v = VUnit⌝ }}.
Proof.
  unfold example4b. wp. wp_bind.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  (* We are looking at [id id]. *)
  wp_bind. wp_use "Hid".
  wp_pure_postcondition; subst.
  wp_use "Hid".
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  ⊢ WP eval [] example4c {{ RET v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4c. wp. wp_bind.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  (* We are looking at [id()]. *)
  wp_bind. wp_use "Hid".
  wp_pure_postcondition.
  (* We are again looking at [id()]. *)
  wp_use "Hid".
  wp_pure_postcondition; subst; done.
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  ⊢ WP eval [] example4d {{ RET v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4d. wp. wp_bind.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  (* Here, [wp] is unable to make progress because we are looking at two
     function calls in parallel. *)
  wp_par; try wp_absurd.

  (* id id *)
  { wp_use "Hid". }

  (* id () *)
  { wp_use "Hid". }

  wp_pure_postcondition. subst.
  wp_bind.

  wp_use "Hid".
Qed.

(* let rec diverge x = diverge x in diverge() *)

Definition divergence :=
  ELetRec1Var "diverge" "x" (EApp (EVar "diverge") (EVar "x")) $
  EApp (EVar "diverge") EUnit.

Lemma spec_divergence:
  ⊢ WP eval [] divergence {{ λ _, ⌜False⌝ }}.
Proof.
Abort. (* TODO now that we have Löb induction, prove this goal *)

(* -------------------------------------------------------------------------- *)

(* A recursive function that walks a list. *)

(* let rec walk xs =
     match xs with
     | [] -> ()
     | x :: xs -> walk xs *)

Definition walk : list rec_binding :=
  RecBinding1Var "walk" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil EUnit;
    Branch (pCons (PVar "x") (PVar "xs"))
           (EApp (EVar "walk") (EVar "xs"))
    ].

Definition spec_walk (walk : val): iProp Σ :=
  □ ∀ (bs : list bool),
  WP call walk (encode_list bs) {{ RET v, ⌜v = VUnit⌝ }}.
  (* TODO should always use [encode], not [encode_list] *)

(* This is a subgoal that appears in the proof of
   [spec_walk_example_abstract] below. *)
Goal
  ∀ η,
  ⊢ spec_walk (VCloRec η walk "walk").
Proof.
  unfold spec_walk.
  iIntros (η) "!>%bs".
  iInduction bs as [| b bs ] "IHbs";
  wp_enter_and_abstract; iIntros (walk); wp.
  { equality. }
  { wp_use "IHbs". }
Qed.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  ⊢ WP eval [] (walk_example e) {{ RET v, ⌜v = encode tt⌝ }}.
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  iIntros. wp. wp_continue. equality.
Qed.

(* The following example illustrates how to reason about a local function.
   When the environment is about to be extended with a binding of the
   variable "walk" to a closure, we prove a specification for this closure,
   then we make this closure opaque. *)
Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := [("xs", (encode bs))] in
  ⊢ WP (eval η (walk_example (EVar "xs"))) {{ RET v, ⌜v = encode tt⌝ }}.
Proof.
  intros. wp. wp_bind.
  (* The environment is about to be extended with a binding of the variable
     "walk" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  oSpecify "walk" spec_walk vid "#Hwalk".
  (* Subgoal: prove that the closure satisfies [spec_walk]. *)
  { (* The environment [η] is irrelevant, since the code is in fact closed.
       Abstract it away. *)
    generalize η. clear bs η. intros η.
    unfold spec_walk.
    (* Prove the spec by induction on the list [bs]. *)
    iIntros "!>"(bs).
    iInduction bs as [| b bs ] "IHbs";
    wp_enter_and_abstract; iIntros (walk); wp.
    { equality. }
    { wp_use "IHbs". }
  }
  (* The variable "walk" is now bound to an abstract closure [walk]. *)
  (* The remains to exploit the hypothesis [Hwalk]. *)
  wp_use "Hwalk".
Qed.

(* ------------------------------------------------------------------------- *)

(* A recursive function that computes the length of a list. *)

(* let rec length xs =
     match xs with
     | [] -> 0
     | x :: xs -> 1 + length xs *)

Definition length : list rec_binding :=
  RecBinding1Var "length" "xs" $
  EMatchMkBranches (EVar "xs") [
    Branch pNil (EInt 0);
    Branch (pCons (PVar "x") (PVar "xs"))
           (EIntAdd (EInt 1) (EApp (EVar "length") (EVar "xs")))
    ].

Definition spec_length (length : val) :=
  ∀ A (eA : Encode A) (xs : list A),
  ⊢ WP call length (encode_list xs)
       {{ RET v, ⌜v = encode (List.length xs)⌝ }}.

Goal
  ∀ η,
  spec_length (VCloRec η length "length").
Proof.
  unfold spec_length. intros η ?? xs.
  iInduction (xs) as [| x xs ] "IHxs";
  wp_enter_and_abstract; iIntros (length);
  wp.
  { equality. }
  { iApply wp_bind_binary; first by wp_use "IHxs".
    wp_pure_postcondition; subst; cbn. wp.
    cbn. iPureIntro.
    rewrite add_repr_repr. equality. }
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

Goal ⊢ WP (eval [] ref_store_load) {{ RET v, ⌜ v = VConstant "B" ⌝ }}.
Proof.
  unfold ref_store_load.
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
  ⊢ WP eval_mexpr [] simple_module {{ RET v, simple_module_spec v }}.
Proof.
  wp. wp_bind.

  (* [f] is about to be added to the environment *)
  oSpecify "f" spec_id vf "#Hid".
  { iIntros(v). iModIntro. wp. equality. }

  wp_bind.

  (* [g] is about to be added to the environment *)
  oSpecify "g" spec_id vg "#Hid'".
  { iIntros(v). iModIntro.
    wp_use "Hid". }

  (* We can use the spec of [f] at the function call (of the body of [h]). *)
  wp_bind. wp_use "Hid". wp_pure_postcondition; subst; cbn.
  wp_bind. wp_concat. wp.

  (* Proving the trivial post condition using the aforementioned specs. *)
  wp_module_spec.
Qed.

(* -------------------------------------------------------------------------- *)

(* Test : specify the body of a function instead of the function itself. *)

From osiris.proofmode Require Import proofmode.

(* ( (x * z) + (y * t) ) + v*)
Definition test_innerbody x y z t v  : expr :=
  EIntAdd
    (EIntAdd (EIntMul (EVar x) (EVar z)) (EIntMul (EVar y) (EVar t)))
    (EVar v).
Opaque test_innerbody.

Definition test_body : expr :=
  EAnonFun $ AnonFun "x" $
           EAnonFun $ AnonFun "y" $
           EAnonFun $ AnonFun "z" $
           EAnonFun $ AnonFun "t" $
           EAnonFun $ AnonFun "v" $
           test_innerbody "x" "y" "z" "t" "v".


Lemma test_body_simp (i j k l m : Z) :
  ∀ (η: env) x y z t v,
    lookup_name η x = ret #i →
    lookup_name η y = ret #j →
    lookup_name η z = ret #k →
    lookup_name η t = ret #l →
    lookup_name η v = ret #m →
    simp (eval η (test_innerbody x y z t v))
         (ret #( ((i * k) + (j * l) ) + m)%Z).
Proof.
  intros η x y z t v Hx Hy Hz Ht Hv.
  force_unfold_at_1 test_innerbody.
  simp.
Qed.

Local Hint Resolve test_body_simp : simp_specs.

Definition add_uc : expr :=
  ELet (Binding1 (PVar "x") (EInt 1)) $
  EApp
    (EApp
       (EApp
          (EApp
             (EApp test_body (EVar "x"))
             (EInt 2))
          (EInt 3))
       (EInt 4))
    (EInt 5).

Lemma add_test (i j: Z) :
  ⊢ WP eval [("bloup", #0%Z)] add_uc {{ RET v, ⌜ v = #16 ⌝ }}.
Proof.
  wp. wp_continue. equality.
Qed.
