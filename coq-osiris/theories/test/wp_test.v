From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.proofmode Require Import ewp_tactics.

Context `{!osirisGS Σ} `{protocol_wf Σ}.

Local Transparent eval eval_mexpr eval_sitem eval_sitems
  eval_bindings evals eval_pat eval_cpat encode.

(* ---------------------------------------------------------------------------*)
(* Examples. *)

(* let x = A() in y *)

Goal
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  ⊢ WP eval [] e @ NotStuck; ⊤ {{ RET v, ⌜v = VConstant "A"⌝ }}.
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  iIntros.
Abort. (* expected *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

(* An example of reasoning about straight-line code. *)

Goal ⊢ EWP (eval [] example) {{ RET v, ⌜v = VConstant "A"⌝ }}.
Proof.
  do 3 Simp. Ret. iPureIntro. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := [("z1", v1); ("z2", v2)] in
  ⊢ EWP (eval env example2) {{ RET v, ⌜v = v1⌝ }}.
Proof.
  iIntros.
  do 3 Simp. Ret. cbn.
  iPureIntro. reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

Ltac Apply H :=
  lazymatch goal with
  | |- environments.envs_entails _ (ewp_def _ _ _ (lift_ret_spec _)) =>
      let v := fresh "v" in
      let Hv := fresh "Hv" in
      iApply ewp_mono; [ iApply H | ]; iIntros ([v | ?]) "HΦ"; [ | done];
      try iDestruct "HΦ" as %HΦ
  | _ => iApply ewp_mono; [ iApply H | ]; iDestruct H as ([v _]) "HΦ"
  end.

Lemma spec_example3:
  ∀ (id : val),
  ⊢ □ (∀ v, EWP (call id v) {{ RET v', ⌜ v' = v⌝ }} ) -∗
  let env := [("id", id)] in
  EWP (eval env example3) {{ RET v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  iIntros (id) "#Hid".
  Simp. Par.
  { Bind.
    Apply "Hid"; subst; cbn.
    (* FIXME *)
    Unshelve.
    2 : exact (fun x => ⌜x = [VConstant "A"]⌝)%I.
    cbn. iPureIntro; done. }

  (* Exceptional continuations are not taken. *)
  { cbn; iIntros (??); done. }
  { cbn; iIntros (??); done. }

  { cbn. iIntros (????); subst.
    Ret; cbn. by iPureIntro. }
Qed.

(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is the
   identity function. *)

Definition identity :=
  EFun1Var "x" (EVar "x").

Definition spec_id (c: val) : iProp Σ :=
  □ ∀ v, EWP call c v {{ RET v', ⌜ v' = v ⌝ }}.

Goal
  ⊢ EWP (eval [] identity) {{ RET v, spec_id v }}.
Proof.
  Simp. Ret. cbn. iModIntro. iIntros (?).
  Simp. Ret. done.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
    example3.

Lemma spec_example4:
  ⊢ EWP (eval [] example4)
    {{ RET v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  unfold example4.
  Simp.
  iApply spec_example3. (* TODO: Reintroduce [oSpecify]? *)
  iModIntro. iIntros (?). Simp; by Ret.
Qed.


(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5:
  ⊢ EWP (eval [] example5) {{ RET v, ⌜v = VFalse⌝ }}.
Proof.
  (* TODO make [choose] opaque somewhere else *)
  (* TODO and prove a [wp] rule for [eval (EAssert _)]
          so we do not need to descend to the level of [choose] *)
  Simp. Ret. done.
Qed.

(* let id = identity in
   (id id) () *)

Definition example4b :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp (EApp id id) EUnit.

Lemma spec_example4b:
  ⊢ EWP eval [] example4b {{ RET v, ⌜v = VUnit⌝ }}.
Proof.
  unfold example4b.
  Simp. Simp. Ret. done.
Qed.

(* let id = identity in
   id (id ()) *)

Definition example4c :=
  ELet1Var "id" identity $
  let id := EVar "id" in
  EApp id (EApp id EUnit).

Lemma spec_example4c:
  ⊢ EWP eval [] example4c {{ RET v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4c.

  Simp. Simp. Ret. done.
Qed.

(* let id = identity in
   (id id) (id ()) *)

Definition example4d :=
  ELet1Var "id" identity $
    let id := EVar "id" in
    EApp (EApp id id) (EApp id EUnit).

Lemma spec_example4d:
  ⊢ EWP eval [] example4d {{ RET v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4d.

  Simp. Simp. Ret. done.
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
  EMatch (EVar "xs") [
    Branch (CVal pNil) EUnit;
    Branch (CVal (pCons (PVar "x") (PVar "xs")))
           (EApp (EVar "walk") (EVar "xs"))
    ].

Definition spec_walk (walk : val): iProp Σ :=
  □ ∀ (bs : list bool),
  EWP call walk (encode_list bs) {{ RET v, ⌜v = VUnit⌝ }}.
  (* TODO should always use [encode], not [encode_list] *)

(* This is a subgoal that appears in the proof of
   [spec_walk_example_abstract] below. *)
Goal
  ∀ η,
  ⊢ spec_walk (VCloRec η walk "walk").
Proof.
  unfold spec_walk.
  iIntros (η) "!>%bs".
  iInduction bs as [| b bs ] "IHbs".
  { Simp; by Ret. }
  { cbn. (* TODO *)
Admitted.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  ⊢ EWP eval [] (walk_example e) {{ RET v, ⌜v = (encode.encode tt : val)⌝ }}.
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  iIntros. do 2 Simp. by Ret.
Qed.

(* ------------------------------------------------------------------------- *)

(* A recursive function that computes the length of a list. *)

(* let rec length xs =
     match xs with
     | [] -> 0
     | x :: xs -> 1 + length xs *)

Definition length : list rec_binding :=
  RecBinding1Var "length" "xs" $
  EMatch (EVar "xs") [
    Branch (CVal pNil) (EInt 0);
    Branch (CVal (pCons (PVar "x") (PVar "xs")))
           (EIntAdd (EInt 1) (EApp (EVar "length") (EVar "xs")))
    ].

Definition spec_length (length : val) :=
  ∀ A (eA : Encode A) (xs : list A),
  ⊢ EWP call length (encode_list xs)
       {{ RET v, ⌜v = encode.encode (List.length xs)⌝ }}.

Goal
  ∀ η,
  spec_length (VCloRec η length "length").
Proof.
  unfold spec_length. intros η ?? xs.
Admitted.


(* -------------------------------------------------------------------------- *)

(* On verifying modules. *)

(* [simple_module] defines stand alone module expression.
   There are no side-effects to deal with. *)
Definition simple_module: mexpr :=
  MStruct
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
