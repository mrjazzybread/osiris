Require Import base lang free eval step wp encode.

From iris.proofmode Require Import base proofmode classes.

From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

Require Import wp.
Context `{!osirisGS_gen hlc Σ}.


(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

(* TODO:
 * - instead of using [cbn], try to only reduce what should be reduced (not continutations, ...).
 * - eliminate later modalities if required.
 *   It can *at least* be done when the goal is automatically provable after 
 *   [repeat iNext].
 * - move the tactics and tactics-related elements to a new file [theories/wp_tactics.v]
 *)

Definition our__id {A}: A → A := λ i, i.
Lemma our__id_is_id {A} (i: A) :
  i = our__id i.
Proof. reflexivity. Qed.
Global Opaque our__id.

Ltac wp_step :=
  lazymatch goal with
  | |- environments.envs_entails _
        (wp _ _ (ret _) _) => iApply wp_ret
  | |- environments.envs_entails _
        (wp _ _ (bind _ _) _) => iApply wp_bind
  | |- environments.envs_entails _
        (wp _ _ (Par (ret _) (ret _) _ _) _) => iApply wp_par_ret_ret
  | |- environments.envs_entails _
        (wp _ _ (Par _ (ret _) ?k ?ko) _) =>
      remember k; remember ko;
      iApply wp_par_ret_right
  | |- environments.envs_entails _
        (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      remember k; remember ko;
      iApply wp_par_ret_left
  | |- environments.envs_entails _ (bi_later _) => iNext
  | |- environments.envs_entails _
        (wp _ _ (try (ret _) _ _) _) => iApply wp_try_ret
  | |- environments.envs_entails _
        (wp _ _ (eval.lookup _ _) _) => simpl (eval.lookup _ _)
  | H: ?k = _ |- environments.envs_entails _
        (wp _ _ (?k _) _) =>
      rewrite H; clear H k
  end.

Ltac wp :=
  cbn;
  repeat wp_step.

Ltac wp_par :=
  iApply wp_par; [wp | wp | ].

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ].

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  ];
  simpl.

Global Opaque call.
Ltac wp_call :=
  with_strategy transparent [call] unfold call at 1; wp.


(* TODO not great *)
Ltac wp_set_postcondition :=
  match goal with
    |- @environments.envs_entails _ _
        (?ϕ ?v) =>
      is_evar ϕ;
      instantiate (1 := (λ w, ⌜w = v⌝)%I)
  end.

(* ----------------------------------------------------------------------*)
(* Examples. *)


(* let x = A() in y *)

Goal forall s E,
  let e := ELet1Var "x" (EConstant "A") $ EVar "y" in
  ⊢ WP (eval EnvNil e) @ s; E {{ λ v, ⌜v = VConstant "A"⌝ }}.
Proof.
  (* This goal is false: the variable [y] is unbound. *)
  intros. subst e. simpl.
  iApply wp_par_ret_ret.
  simpl.
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
  iStartProof.
  Time cbn.
  Time wp.
  iApply wp_try_ret.
  iApply wp_ret.
  iPureIntro. reflexivity.
Time Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet1Var "x" (EPair (EVar "z1") (EVar "z2")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

(* 
Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  ⊢ WP (eval env example2) {{ λ v, ⌜v = v1⌝ }}.
Proof.
  intros. wp.
  iPureIntro. reflexivity.
Qed.

(* (id (A()), id (A())) *)

Definition example3 :=
  let idA := EApp (EVar "id") (EConstant "A") in
  EPair idA idA.

(* TODO. *)
Lemma spec_example3:
  ∀ (id : val),
  ⊢ □ (∀ v, WP (call id v) {{λ v', ⌜ v' = v⌝ }} ) -∗
  let env := EnvCons "id" id EnvNil in
  WP (eval env example3) {{λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
Proof.
  iIntros (id) "#Hid".
  wp.
  (* The two components of the pair are evaluated in parallel,
     and each of them is a function application, which is itself
     evaluated in parallel. So we have a tree of nested [Par]. *)
  wp_par.
  { iApply "Hid". }
  { iApply wp_covariant.
    - iApply "Hid".
    - iIntros (v->).
      do 3 iNext. wp. by wp_set_postcondition. }
  iNext.
  iIntros (??) "->->".
  wp. iPureIntro. reflexivity.
Qed.


(* The identity function. *)

(* [identity] is an expression which returns a closure whose behavior is
   the identity function. *)

Definition identity :=
  EFun "x" (EVar "x").

Lemma spec_identity s E:
  ⊢ □ WP (eval EnvNil identity) @ s; E {{λ c, ∀ v, WP (call c v) @ s; E {{ λ v', ⌜v' = v⌝ }} }}.
Proof.
  iModIntro.
  wp. iIntros.
  by wp_call.
Qed.

(* let id = identity in
   (id (A()), id (A())) *)

Definition example4 :=
  ELet1Var "id" identity $
  example3.

Lemma spec_example4 s E:
  ⊢ WP (eval EnvNil example4) @ s; E {{λ v, ⌜v = VPair (VConstant "A") (VConstant "A")⌝ }}.
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
  iPoseProof (Hidentity s E) as "#Hid".
  wp_par.
  - wp_use "Hid".
  - wp.
    iNext. wp_set_postcondition.
    iPureIntro. reflexivity.
  - iNext.
    iIntros (v1 v2) "H->". wp.
Admitted.

(*
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
  wp EnvNil example4c (λ v, v = VUnit).
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
  wp EnvNil example4d (λ v, v = VUnit).
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
  wp EnvNil (walk_example e) (λ v, v = encode ()).
Proof.
  (* The code is pure and terminating and can be fully evaluated. *)
  wp. do 3 wp_call. reflexivity.
Qed.

Lemma spec_walk_example_abstract :
  forall (bs : list bool),
  let η := EnvCons "xs" (encode bs) EnvNil in
  wp η (walk_example (EVar "xs")) (λ v, v = encode ()).
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

*) *)
