From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.

Context `{!osirisGS Σ}.

Local Transparent eval_mexpr eval_bindings evals extend encode.

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
Abort. (* expected *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

(* An example of reasoning about straight-line code. *)

Goal ⊢ WP (eval [] example) {{ RET v, ⌜v = VConstant "A"⌝ }}.
Proof.
  wp. wp. wp.
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
  iIntros. wp. wp. wp.
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
  { wp_use "Hid". }
  { wp_bind. wp_use "Hid". iIntros (r) "Hr". iClear (id) "Hid".
    (* TODO fp: I cannot read the goal. The "uparrow" notation
            makes it incomprehensible. *)
    (* TODO fp: we should be able to reason without destructing [r] *)
    destruct r as [v|e]; simpl.
    + iDestruct "Hr" as %H. subst v.
      (* TODO [wp_set_postcondition] does not work here *)
      iApply wp_ret. unfold ipure.
      wp_set_postcondition.
    + iExact "Hr".
  }
  { wp_absurd. }
  { wp_absurd. }
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
  wp.
  (* The environment is about to be extended with a binding of the variable
     "id" to a certain closure. Now is the time to prove a specification
     for this closure; then, we can make this closure opaque. *)
  oSpecify "id" spec_id id "#Hid".
  (* Subgoal: prove that [fun x -> x] satisfies [spec_id]. *)
  { unfold spec_id. iModIntro. iIntros (v). wp. equality. }
  (* The variable "id" is now bound to an abstract closure [id]. *)
  iApply spec_example3.
  wp_use "Hid".
Qed.

(* An example that involves an assertion. *)

Definition example5 :=
  ESeq (EAssert ETrue) EFalse.

Lemma spec_example5:
  ⊢ WP (eval [] example5) {{ RET v, ⌜v = VFalse⌝ }}.
Proof.
  (* TODO make [choose] opaque somewhere else *)
  (* TODO and prove a [wp] rule for [eval (EAssert _)]
          so we do not need to descend to the level of [choose] *)
  by wp.
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
  unfold example4b.
  wp.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  (* We are looking at [id id]. *)
  wp. wp_bind. wp_use "Hid".
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
  unfold example4c. wp.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  (* We are looking at [id()]. *)
  wp. wp_bind. wp_use "Hid".
  wp_pure_postcondition.
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
  ⊢ WP eval [] example4d {{ RET v, ⌜v = VUnit⌝}}.
Proof.
  unfold example4d. wp.
  (* Deal with the local binding of [id]. *)
  oSpecify "id" spec_id vid "#Hid".
  { unfold spec_id. iIntros (v).
    iModIntro. wp. equality. }
  wp.
  (* Here, [wp] is no longer able to make progress because we are looking at two
     function calls in parallel. *)

  wp_par; try wp_absurd.

  (* id id *)
  { wp_use "Hid". }

  (* id () *)
  { wp_use "Hid". }

  wp_pure_postcondition.

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
  EMatch (EVar "xs") [
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
  { cbn. wp. equality. }
  { wp_use "IHbs". wp_pure_postcondition.
    wp. equality. }
Qed.

Definition walk_example e :=
  ELetRec walk $
  EApp (EVar "walk") e.

Lemma spec_walk_example_concrete :
  let e := (eCons ETrue (eCons EFalse eNil)) in
  ⊢ WP eval [] (walk_example e) {{ RET v, ⌜v = encode tt⌝ }}.
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  iIntros. wp. wp. equality.
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
  { cbn. wp. equality. }
  { iApply wp_bind_binary; first by wp_use "IHxs".
    wp_pure_postcondition; subst; cbn. wp.
    cbn. wp. iPureIntro.
    rewrite add_repr_repr. equality. }
Qed.

(* -------------------------------------------------------------------------- *)

(* let l = ref "A" in
   l := "B";
   !l
 *)



Local Ltac wp_progress :=
  first [
      lazymatch goal with
      | |- environments.envs_entails _ $ wp _ _ (eval _ ?e) _ =>
          rewrite eval_eval'; try progress wp_cbn
      end
    | wp_cbn (* TODO: better control the reduction strategy. *)
    | progress wp_simp
    | cbn beta delta -[app]
    ].


Definition ref_store_load: expr :=
  ELet1Var "l" (ERef (EConstant "A")) $
  ELet1Var "_" (EStore (EVar "l") (EConstant "B")) $
  ELoad (EVar "l").

Goal ⊢ WP (eval [] ref_store_load) {{ RET v, ⌜ v = VConstant "B" ⌝ }}.
Proof.
  wp.
  wp_alloc l "[Hl _]".
  wp_store "Hl".
  wp_load "Hl".
  iPureIntro. reflexivity.
Qed.

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


Local Ltac wp_setup :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails ?Δ $ wp _ _ _ _ =>
      let Δ :=
        eval cbn in (environments.env_to_list
                       (environments.env_intuitionistic Δ)) in
      let rec lookforme l :=
        lazymatch constr:(l) with
        | [] => idtac
        | (satisfies_spec ?Λ0 ?v) :: ?t =>
            let Λ := eval hnf in Λ0 in
            lazymatch constr:(Λ) with
            | SpecModule Auto ?l ?P =>
                lazymatch goal with
                | _ : pure_spec Λ0 v |- _ => idtac
                | _ =>
                    iPoseProof ((satisfies_pure_spec Λ v) with "[$]")
                    as "%";
                    change Λ with Λ0 in *
                end
            | _ => idtac
            end ; lookforme t
        | _ :: ?t => lookforme t
        end in
      lookforme Δ
  end
.


(* Goal *)
(*   ⊢ WP eval_mexpr [] simple_module {{ RET v, simple_module_spec v }}. *)
(* Proof. *)
(*   wp. *)
(*   (* [f] is about to be added to the environment *) *)
(*   oSpecify "f" spec_id vf "#Hid". *)
(*   { iIntros(v). iModIntro. wp. equality. } *)

(*   wp_bind. *)

(*   (* [g] is about to be added to the environment *) *)
(*   oSpecify "g" spec_id vg "#Hid'". *)
(*   { iIntros(v). iModIntro. *)
(*     wp_use "Hid". } *)

(*   (* We can use the spec of [f] at the function call (of the body of [h]). *) *)
(*   wp_bind. wp_use "Hid". wp_pure_postcondition; subst; cbn. *)
(*   wp_bind. wp_concat. wp. *)

(*   (* Proving the trivial post condition using the aforementioned specs. *) *)
(*   wp_module_spec. *)
(* Qed. *)

(* -------------------------------------------------------------------------- *)

(* Test : specify the body of a function instead of the function itself. *)

(* ( (x * z) + (y * t) ) + v*)
Definition test_innerbody x y z t v  : expr :=
  ((EVar x) * (EVar z) + (EVar y) * (EVar t) + (EVar v))%expr.
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
  wp. wp. equality.
Qed.
