From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import wp.
From osiris.program_logic Require Import judgements pattern_rules pure.expr_rules.
From osiris.program_logic Require Import pure_rules.
From osiris.program_logic Require Import pure.toplevel_rules.

From Stdlib Require Import Wellfounded.Inverse_Image.
From Equations Require Import Equations.

(* -------------------------------------------------------------------------- *)

(* [is_lambda_of_depth e arg_τ] asserts that [e] is a series of nested
   [EAnonFun _] of depth ≥ to the length of [arg_τ]. *)

Fixpoint is_lambda_of_depth (e : expr) (τ : types) : Prop :=
  exists x e',
    e = EAnonFun (AnonFun x e') ∧
      match τ with
      | Tbase _ => True
      | Tcons _ τ' =>
          is_lambda_of_depth e' τ'
      end.

Lemma unfold_is_lambda_of_depth e τ :
  is_lambda_of_depth e τ =
  exists x e', e = EAnonFun (AnonFun x e') ∧
                 match τ with
                 | Tbase _ => True
                 | Tcons _ τ' =>
                     is_lambda_of_depth e' τ'
                 end.
Proof. destruct τ; tauto. Qed.

(* [is_VCloRec_of_depth v arg_τ] asserts that the value [v] is
   a (non-mutually) recursive function with
   a number of arguments ≥ to the number of types in [arg_τ]. *)

Definition is_VCloRec_of_depth v τ :=
  exists η f x e,
    v = VCloRec η [ RecBinding f (AnonFun x e) ] f ∧
      match τ with
      | Tbase _ =>
          (* The base case is true since there is always
             at least one binding, namely [x]. *)
          True
      | Tcons _ τ' =>
          is_lambda_of_depth e τ'
      end.

Definition is_VClo_of_depth v τ :=
  exists η x e,
    v = VClo η (AnonFun x e) ∧
      match τ with
      | Tbase _ => True
      | Tcons _ τ' =>
          is_lambda_of_depth e τ'
      end.

(* -------------------------------------------------------------------------- *)

(* To reason about curried n-ary function, and give them natural specifications
   (i.e. specifications over the function when fully applied)
   We introduce the predicate [Spec arg_τ c P]. *)

(* [Spec arg_τ c P] should be read as "[c] is a function value, with
   arguments described by [arg_τ], and with specification [P]." *)

(* [Spec] matches on the list of argument types [arg_τ], producing a series of
   nested calls, where the base case asserts [P] over the full call. *)

Equations Spec (τ : types)
  (c : val) (P : τ -#> microvx -> Prop) : Prop :=
| Tbase X, c, P :=
    ∀ (x : X), P x (call c #x)
| Tcons X τ', c, P :=
    ∀ (x : X), pure_wp (call c #x) (λ c, Spec τ' c (P x)) ⊥.

(* As a sanity check, we can check on simple examples that we get
   the expected premise when we want to show that
   a function satisfies some specification [P]. *)

Local Lemma pure_eval_anon_unary `{Encode X}
  (P : τ[X] -#> microvx -> Prop) η (x : var) e ζ
  :
  (∀ (v : X), P v (please_eval ((x, #v) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun x e))) (λ c, Spec τ[X] c P) ζ.
Proof.
  intros HP; simpl_eval; eapply pure_ret; encode.
Qed.

Local Lemma pure_eval_anon_binary `{Encode X, Encode Y}
  (P : τ[X; Y] -#> microvx -> Prop) η (x y : var) e ζ
  :
  (∀ (vx : X) (vy : Y), P vx vy (please_eval ((y, #vy) :: (x, #vx) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun x (EAnonFun (AnonFun y e))))) (λ c, Spec τ[X; Y] c P) ζ.
Proof.
  intros HP.
  simpl_eval; eapply pure_ret; [ encode | ].
  rewrite Spec_equation_2; intros vx; simpl; eapply pure_wp_Eval; simpl_eval; eapply pure_wp_ret.
  rewrite Spec_equation_1; intros vy; apply HP.
Qed.

(* [Spec] is monotonic over specification predicates. *)

Lemma Spec_mono (τ : types) (P P' : τ -#> microvx -> Prop) c :
  Spec τ c P ->
  (∀# args, ∀ m, (P args) m -> (P' args) m) ->
  Spec τ c P'.
Proof.
  revert c.
  induction τ as [ | X HX arg_τ IH ]; intros c HP Hmono.
  { simp Spec in HP |-*. intros x.
    apply Hmono. apply HP. }
  simp Spec in HP |-*; intros x.
  eapply pure_wp_mono_ret; [ apply HP | ].
  intros c' HSpec'.
  apply IH with (P := P x); [ apply HSpec' | ].
  rewrite tforall_unroll in Hmono. apply Hmono.
Qed.

(* Under a [Spec], a [VCloRec] [c] is equivalent to a [VClo] where [c]
   is in the captured environment. *)

Lemma Spec_equiv (τ : types) η f x e (P : τ -#> microvx -> Prop) :
  let f_value := VCloRec η [RecBinding f (AnonFun x e)] f in
  Spec τ f_value P =
  Spec τ (VClo ((f, f_value) :: η) (AnonFun x e)) P.
Proof.
  destruct τ; simpl; simp Spec;
    simpl; rewrite String.eqb_refl; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [aSpec] is a restatement of [Spec], but with all of the
   arguments quantified before the nested calls. *)

(* [aSpec] is used when we want to do induction over all arguments at
   once. The user is NOT exposed to it, we only use it in our
   intermediary lemma [prove_aSpec_rec]. *)

Equations aSpec (τ : types)
  (c : val) (P : τ -#> microvx -> Prop) (args : τ) : Prop :=
| Tbase X, c, P, x :=
    P x (call c #x);
| Tcons X τ', c, P, (x, args') :=
    pure_wp (call c #x) (λ c', aSpec τ' c' (P x) args') ⊥.

Arguments aSpec {τ} c P args.

Lemma unfold_aSpec `{Encode X}
  {τ : types}
  c
  (P : (Tcons X τ) -#> microvx -> Prop)
  (args : τ)
  x :
  aSpec c P (x, args) =
    pure_wp (call c #x) (λ c', (aSpec c' (P x)) args) ⊥.
Proof.
  simp aSpec. reflexivity.
Qed.

Lemma aSpec_mono (τ : types) (P P' : τ -#> microvx -> Prop) c args :
  aSpec c P args ->
  (∀ m, (P args) m -> (P' args) m) ->
  aSpec c P' args.
Proof.
  revert c.
  induction τ as [ | X HX τ IH ]; intros c HP Hmono.
  { simp aSpec in HP |-*.
    apply Hmono. apply HP. }
  destruct args as [x args].
  simp aSpec in HP |-*.
  eapply pure_wp_mono_ret; [ apply HP | ].
  intros c' HSpec'.
  apply IH with (P := P x); [ apply HSpec' | ].
  apply Hmono.
Qed.

Lemma aSpec_equiv (τ : types) η f x e (P : τ -#> _) args :
  let f_value := VCloRec η [RecBinding f (AnonFun x e)] f in
  aSpec f_value P args =
  aSpec (VClo ((f, f_value) :: η) (AnonFun x e)) P args.
Proof.
  destruct τ; [ | destruct args ]; simpl;
    simp aSpec;
    simpl; rewrite String.eqb_refl; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(*  We want to show the following equivalence:
    [Spec c P <-> ∀ args, aSpec c P args]. *)

(* This equivalence holds as long as one of the following two conditions holds:
   - the type of arguments is inhabited
   - the closure represents a function of arity equal to
     the number of parameters *)

(* The direction [Spec] -> [aSpec] is true without any condition. *)

Lemma Spec_aSpec (τ : types) (c : val) (P : τ -#> microvx -> Prop) :
  Spec τ c P ->
  (∀ args, aSpec c P args).
Proof.
  revert c.
  induction τ as [ | X HX arg_τ IH ].
  { intros c HSpec.
    simp Spec in HSpec; apply HSpec. }
  intros c HSpec args.

  destruct args; simpl. rewrite unfold_aSpec.

  eapply pure_wp_mono_ret; [ simp Spec in HSpec; apply HSpec | ].
  intros c' HSpec'.
  apply IH. apply HSpec'.
Qed.

(* The direction [aSpec] -> [Spec] necessitates one of the conditions.
   We elect to enforce that the closure is of an appropriate depth.
   This is because the alternative uses the lemma [pure_wp_intersection]. *)

(* We proceed by induction over the list of types. During the induction
   step, we want the statement to hold over the generated intermediate
   closure.

   Because this closure will be a [VClo], we need to use the [Spec]
   equivalences between [VClo] and [VCloRec] to generalise our goal
   before we can start the induction.

   This gives rise to the intermediate lemma [aSpec_Spec_VClo],
   which we use in the proof of [aSpec_Spec]. *)

Lemma aSpec_Spec_VClo (τ : types) (c : val) (P : τ -#> microvx -> Prop) :
  is_VClo_of_depth c τ ->
  (∀ args, (aSpec c P) args) ->
  Spec τ c P.
Proof.
  generalize dependent c.
  induction τ as [ X HX | X HX τ' IH ];
    intros c is_VClo HSpec; simp Spec; intros vx.
  (* Base case: [aSpec] and [Spec] unfold to the same thing. *)
  { specialize (HSpec vx); apply HSpec. }
  (* Inductive case: step through the call in [Spec] and the call
     in [aSpec] thanks to the knowledge that [c] is a closure. *)
  inversion is_VClo as (η & x & e & -> & Hlambda).
  rewrite unfold_is_lambda_of_depth in Hlambda.
  destruct Hlambda as (y & e' & -> & Hlambda).
  simpl; eapply pure_wp_Eval; simpl_eval. eapply pure_wp_ret.
  apply IH.
  - (* Goal: The next intermediate closure is of depth [τ']. *)
    repeat eexists. apply Hlambda.
  - (* Goal: The closure satisfies [aSpec]. *)
    intros args.
    (* Step through the [call] in HSpec. *)
    rewrite forall_unroll in HSpec; specialize (HSpec vx args);
      simpl in HSpec.
    rewrite unfold_aSpec in HSpec.
    simpl in HSpec. eapply invert_pure_wp_eval in HSpec.
    unfold eval in HSpec; rewrite seal_eq in HSpec; simpl in HSpec.
    eapply invert_pure_wp_ret in HSpec.
    apply HSpec.
Qed.

Lemma aSpec_Spec (τ : types) (c : val) (P : τ -#> microvx -> Prop):
  is_VCloRec_of_depth c τ ->
  (∀ args, (aSpec c P) args) ->
  Spec τ c P.
Proof.
  intros (η & f & x & e & -> & Hlambda) HaSpec'.
  set (v := VClo
              ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η)
              (AnonFun x e)).
  (* Restate our hypotheses in terms of [VClo]. *)
  assert (is_VClo_of_depth v τ).
  { unfold is_VClo_of_depth. repeat eexists. apply Hlambda. }
    assert (∀ args : τ, aSpec v P args) as HaSpec.
  { intros args; subst v; rewrite <- aSpec_equiv; apply HaSpec'. }
  (* Restate our goal in terms of [VClo]. *)
  rewrite Spec_equiv.
  (* Apply the auxiliary lemma, and use our restated hypotheses. *)
  apply aSpec_Spec_VClo; auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define [predicate_over_function_body τ P η e], which fetches the
   function body from a series of nested [EAnonFun] in [e], at a depth
   equal to the number of arguments specified by [τ], and asserts [P]
   over the evaluation of that function body. *)

(* In particular, [predicate_over_function_body] can be used to prove
   a goal of the form [Spec τ c P]. *)

Equations predicate_over_function_body
  (τ : types)
  (P : τ -#> microvx -> Prop)
  (η : env)
  (e : expr)
  : Prop :=
| Tbase X, P, η, EAnonFun (AnonFun arg e) :=
    ∀ (x : X), P x (please_eval ((arg, #x) :: η) e)
| Tcons X arg_τ', P, η, (EAnonFun (AnonFun arg e)) :=
    ∀ (x : X), predicate_over_function_body arg_τ' (P x) ((arg, #x) :: η) e
(* If the expression isn't an [EAnonFun] we produce an unprovable proposition. *)
| _, _, _, _ := False.

(* We always want to unfold [predicate_over_function_body] until only a
   statement of the form [∀ x, P x (eval η e)] remains. *)
Arguments predicate_over_function_body !τ /.
Transparent predicate_over_function_body.
Strategy transparent [ predicate_over_function_body ].

(* The following proof proceeds by induction over the depth of a lambda. *)
Fixpoint AnonFun_depth e : nat :=
  match e with
  | EAnonFun (AnonFun _ e) => 1 + AnonFun_depth e
  | _ => 0
  end.
Local Lemma afun_wf :
  well_founded (λ e1 e2, AnonFun_depth e1 < AnonFun_depth e2)%nat.
Proof.
  eapply wf_inverse_image. apply Nat.lt_wf_0.
Qed.

Local Lemma prove_Spec (τ : types) η x e (P : τ -#> microvx -> Prop) :
  predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) ->
  @Spec τ (VClo η (AnonFun x e)) P.
Proof.
  generalize dependent x; revert η; generalize dependent τ.
  (* We do induction on the depth of the number or arguments that the function takes.*)
  induction e as [e IH] using (well_founded_induction afun_wf).
  intros arg_τ P η arg HP.
  destruct arg_τ.
  (* Case: the tuple has size 1. *)
  { apply HP. }
  simp Spec; intros x.
  (* Case: the tuple has size [≥ 2]. *)
  (* Because the tuple has size greater than 1, we must have that the
     function body [e] is equal to [EAnonFun a] for some [a]. *)
  simpl in HP; specialize (HP x); simpl.
  destruct e; try (destruct arg_τ; contradiction);
    destruct a as [arg2 e2].
  (* Goal: [ P (x, args) (call_tele (ret (VClo η ..)) (x, args)) ]. *)
  specialize (IH e2); simpl in IH.
  (* We reduce [call_tele] and its internal evaluations. *)
  eapply pure_wp_Eval.
  simpl; simpl_eval; simpl. apply pure_wp_ret.
  (* Apply the induction hypothesis. *)
  apply IH; [ lia | apply HP ].
Qed.

(* The reasoning rule for an n-ary non-recursive function. *)

Lemma pure_eval_anon
  (τ : types)
  (P : τ -#> microvx -> Prop)
  η
  (x : var)
  e
  ζ :
  predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) ->
  pure (eval η (EAnonFun (AnonFun x e))) (λ c, Spec τ c P) ζ.
Proof.
  intros HP.
  simpl_eval; apply pure_wp_ret.
  unfold returns; eexists; split; [ reflexivity | ].
  by apply prove_Spec.
Qed.

(* -------------------------------------------------------------------------- *)

(* We can also use [Spec] to specify and reason about recursive functions.
   [prove_aSpec_rec τ R c P] gives an induction principle for [Spec] by
   well-foundedness over the arguments. *)

Lemma prove_aSpec_rec
  (τ : types)
  (R : τ -> τ -> Prop) c
  (P : τ -#> microvx -> Prop) :
  is_VCloRec_of_depth c τ ->
  well_founded R ->
  (∀# (args : τ),
    (∀# sargs, R sargs args -> aSpec c P sargs) ->
    aSpec c P args)->
  @Spec τ c P.
Proof.
  intros is_VCloRec Hwf HP.
  apply aSpec_Spec; eauto.
  intros args.

  induction args as [args IHR] using (well_founded_induction Hwf); clear Hwf.

  rewrite tforall_equiv in HP; specialize (HP args); apply HP.
  apply tforall_equiv; apply IHR.
Qed.

(* If [c] is a lambda of depth [arg_τ], then
   [∀ args, Q args -> aSpec c P args] is equivalent to
   [Spec c (λ args, Q args -> P args)] *)

Lemma guarded_aSpec_Spec c (τ : types)
  (Q : τ -> Prop) (P : τ -#> microvx -> Prop) :
  is_VCloRec_of_depth c τ ->
  (∀# args, Q args -> aSpec c P args) ->
  Spec τ c (λ# args m, Q args -> P args m).
Proof.
  intros (η & f & x & e & -> & He) HaSpec.
  (* The nature of the proof involves a growing environment [η]. We
     need to generalise over this environment for the induction to go
     through.

     We could step through the first [VCloRec] manually to reach the
     underlying [VClo]s, but we have an equivalence between [VCloRec]
     and [VClo] under [Spec] which is cleaner. *)
  rewrite Spec_equiv.
  assert
    (∀# args,
      Q args ->
      aSpec
        (VClo
           ((f, (VCloRec η [ RecBinding f (AnonFun x e)] f)) :: η)
           (AnonFun x e))
        P
        args) as HSpec; [ | clear HaSpec ].
  { apply tforall_equiv; intros sargs HR.
    rewrite <- aSpec_equiv.
    rewrite tforall_equiv in HaSpec; by apply HaSpec. }
  generalize dependent ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η).

  (* Proceed by induction over the argument type. *)
  generalize dependent e; revert x.
  induction τ as [ X H | X H arg_τ IH ]; intros x e He η0 HSpec.

  (* Base case: the argument is unary. *)
  { simp Spec; intros vx HR.
    specialize (HSpec vx HR). apply HSpec. }

  (* Inductive case: the argument has a head [vx] of type [X]. *)
  simp Spec; intros vx; simpl.

  (* Invert [He] to conclude that [e] is an [EAnonFun], then step
     through its (trivial) evaluation. *)
  rewrite unfold_is_lambda_of_depth in He.
  destruct He as (y & e' & -> & He').
  eapply pure_wp_Eval.
  simpl_eval; apply pure_wp_ret.

  (* Apply the induction hypothesis. *)
  apply IH; [ | clear IH He' ]. { apply He'. }

  apply tforall_equiv; intros sargs HR.
  rewrite tforall_unroll in HSpec; specialize (HSpec vx).
  rewrite tforall_equiv in HSpec; specialize (HSpec sargs HR).
  (* Subgoal (morally): show [aSpec (VClo e') (P vx) args] using
     [aSpec (VClo (EAnonFun x e')) P (vx args)]. *)
  simpl in HSpec; rewrite unfold_aSpec in HSpec; simpl in HSpec.
  eapply invert_pure_wp_eval in HSpec.
  unfold eval in HSpec; rewrite seal_eq in HSpec; simpl in HSpec.
  by apply invert_pure_wp_ret in HSpec.
Qed.

(* -------------------------------------------------------------------------- *)

(* We would like to provide a [prove_aSpec_rec]-like reasoning rule to
   the user. But there are two ergonomic improvements we can make:
   (1) We can hide the use of [aSpec].
   (2) We can unfold the goal so that we step into the function's body. *)

(* [predicate_over_function_body_with_hyp] is a restatement of
   [predicate_over_function_body] that is parameterised by a hypothesis
   that can depend on the arguments. *)

Equations predicate_over_function_body_with_hyp
  (τ : types)
  (P : τ -#> microvx -> Prop)
  (H : τ -> Prop)
  (η : env) (e : expr)
  : Prop :=
| Tbase X, P, H, η, (EAnonFun (AnonFun arg e)) :=
    ∀ (x : X),
      H x ->
      P x (please_eval ((arg, #x) :: η) e)
| Tcons X τ', P, H, η, (EAnonFun (AnonFun arg e)) :=
    ∀ (x : X),
      let η_x := (arg, #x) :: η in
      let H_x := λ args, H (x, args) in
      predicate_over_function_body_with_hyp τ' (P x) H_x η_x e
| _, _, _, _, _ := False.

Transparent predicate_over_function_body_with_hyp.
Strategy transparent [ predicate_over_function_body_with_hyp ].

(* [unfolded_spec_with_rec_assumption] generates a [Prop] of the form
   [Spec c (R x y -> P x) -> P y c], and is used to prove a goal of
   the form [Spec c P]. *)

(* We introduce this auxiliary definition in order to decouple the type
   over which we will perform proofs by induction [τ] and the "original"
   type [τ_og] that is used in the generated induction hypothesis. *)

Definition unfolded_spec_with_rec_assumption_aux (τ τ_og : types) η f x e
  (R : τ_og -> τ -> Prop)
  (P : τ -#> microvx -> Prop)
  (Pog : τ_og -#> microvx -> Prop) :=
  (∀ c, predicate_over_function_body_with_hyp τ
          P
          (λ args, @Spec τ_og c (λ# sargs m,
                                     R sargs args ->
                                     Pog sargs m))
          ((f, c) :: η)
          (EAnonFun (AnonFun x e))).

Arguments unfolded_spec_with_rec_assumption_aux τ /.
Transparent unfolded_spec_with_rec_assumption_aux.
Strategy transparent [ unfolded_spec_with_rec_assumption_aux ].

Definition unfolded_spec_with_rec_assumption (τ : types) η f x e
  (R : τ -> τ -> Prop)
  (P : τ -#> microvx -> Prop) :=
  unfolded_spec_with_rec_assumption_aux τ τ η f x e R P P.

Arguments unfolded_spec_with_rec_assumption τ /.
Transparent unfolded_spec_with_rec_assumption.
Strategy transparent [ unfolded_spec_with_rec_assumption ].

(* We show that the proposition generated by
   [unfolded_spec_with_rec_assumption] implies the recursive premise
   we get by well-founded induction over the arguments. *)

Lemma by_unfold_spec (τ : types) η f x e R P :
  let c := VCloRec η [RecBinding f (AnonFun x e)] f in
  is_VCloRec_of_depth c τ ->
  unfolded_spec_with_rec_assumption τ η f x e R P ->
  (∀# args,
    (∀# sargs, R sargs args -> aSpec c P sargs) ->
    aSpec c P args).
Proof.
  intros c isVCloRec HP; subst c.
  apply tforall_equiv; intros args IHargs.
  unfold unfolded_spec_with_rec_assumption in HP.
  (* Generalize [τ] where it doesn't participate in the recursion.
     This is exactly where [τ_og] appears in the definition of
     [unfolded_spec_with_rec_assumption_aux[. *)
  remember P as Pog in HP at 2, IHargs; clear HeqPog.
  remember τ as τ_og in R at 1, Pog, HP at 2, IHargs, isVCloRec;
    clear Heqτ_og.

  (* Generalize the [VCloRec] used in the recursive call. *)
  rewrite aSpec_equiv.
  revert IHargs isVCloRec.
  generalize (VCloRec η [RecBinding f (AnonFun x e)] f); intros c.
  (* Generalize all instances of [(f, c) :: η]. *)
  specialize (HP c); revert HP.
  generalize ((f, c) :: η); intros η0.

  intros HP IHargs Hclo.

  (* Generalize the statement for the induction. Notably, generalize
     over the head type of the telescope. *)
  revert x e η0 HP Hclo.
  induction τ as [ X HX | X HX τ IH]; intros x e η0 Hbp Hclo.

  (* Base case: there is only one parameter. *)
  { simp aSpec. apply Hbp.
    apply guarded_aSpec_Spec; [ apply Hclo | apply IHargs ]. }

  (* Induction step: the list of parameters has a head of type [X]. *)
  destruct args as [vx args].

  simpl in Hbp; specialize (Hbp vx).

  (* We know that [e = EAnonFun (AnonFun y e')] by inversion on Hbp. *)
  destruct e;
    ((destruct τ; contradiction)
     || destruct a as [y e']).

  (* Specialize the induction hypothesis. *)
  specialize (IH (λ ttog tt,
                  R ttog (vx, tt))).
  specialize (IH (P vx) args).
  specialize (IH IHargs).
  specialize (IH y e' ((x, #vx) :: η0)).
  (* We now step forward by evaluating [pure (eval .. (EAnonFun y e')) (λ c', ..)]. *)
  simp aSpec. eapply pure_wp_Eval.
  simpl; simpl_eval; simpl.
  apply pure_wp_ret.

  apply IH; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma lambda_depth_to_vclorec (τ : types) η f x e :
  is_lambda_of_depth (EAnonFun (AnonFun x e)) τ ->
  is_VCloRec_of_depth (VCloRec η [RecBinding f (AnonFun x e)] f) τ.
Proof.
  intros Hlambda; rewrite unfold_is_lambda_of_depth in Hlambda.
  destruct Hlambda as (? & ? & Heq & Hlambda').
  inversion Heq; subst.
  repeat eexists; assumption.
Qed.

(* [pure_eval_letrec] is the user-facing lemma for reasoning about an
   n-ary letrec. Its statement makes use of [unfold_spec] to generate
   an appropriate lemma for every arity. *)

(** For example, if we have [ τ := τ[list Z; Nat] ],
    [pure_eval_letrec] becomes equal to

    Lemma pure_eval_letrec (P : list Z -> Nat -> microvx -> Prop)
    (R : (list Z * Nat) -> (list Z * Nat) -> Prop)
    η f x e e2 φ ζ :
    wf R ->
    (∀ c (l : list Z) (n : Nat),
       Spec c (λ l' n' m, R (l', n') (l, n) -> P l' n' m) ->
       P l n (eval ((y, n) :: (x, l) :: (f, c) :: η) e)) ->
    (∀ c, Spec c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
    pure (eval η (ELetRec [RecBinding f (AnonFun x (EAnonFun (AnonFun y e)))] e2)) φ ζ.
*)

Lemma pure_eval_letrec `{Encode X} (τ : types)
  (P : τ -#> microvx -> Prop)
  (R : τ -> τ -> Prop) η f (x : var) e
  e2 (φ : X -> Prop) ζ :
  is_lambda_of_depth (EAnonFun (AnonFun x e)) τ ->
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  well_founded R ->
  (* Show the specification [P] holds over a call to any arguments,
     under the assumption that [P] holds to a call over any
     smaller arguments. *)
  unfolded_spec_with_rec_assumption τ η f x e R P ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec τ c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros isLambda Hwf Hmkspec He2.
  eapply lambda_depth_to_vclorec in isLambda.
  simpl_eval. eapply He2.
  eapply prove_aSpec_rec; eauto.
  apply by_unfold_spec; eauto.
Qed.

(* Restatement of the lemma for module-level let-recs. *)

Lemma struct_letrec (τ : types)
  (R : τ -> τ -> Prop)
  η δ f (x : var) e (P : τ -#> microvx -> Prop) φ :
  is_lambda_of_depth (EAnonFun (AnonFun x e)) τ ->
  well_founded R ->
  unfolded_spec_with_rec_assumption τ η f x e R P ->
  (∀ c, Spec τ c P -> φ ((f, c) :: η, (f, c) :: δ)) ->
  struct_item (η, δ) (ILetRec [RecBinding f (AnonFun x e)]) φ.
Proof.
  intros isLambda Hwf Hmkspec He2.
  eapply lambda_depth_to_vclorec in isLambda.
  unfold struct_item. simpl_eval_sitem.
  eapply pure_ret.
  2: { eapply He2. eapply prove_aSpec_rec; eauto. apply by_unfold_spec; eauto. }
  simpl. reflexivity.
Qed.

Lemma structs_letrec (τ : types)
  (R : τ -> τ -> Prop)
  η δ f (x : var) e (P : τ -#> microvx -> Prop) sitems φ :
  is_lambda_of_depth (EAnonFun (AnonFun x e)) τ ->
  well_founded R ->
  unfolded_spec_with_rec_assumption τ η f x e R P ->
  (∀ c, Spec τ c P -> struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
  struct_items (η, δ) (ILetRec [RecBinding f (AnonFun x e)] :: sitems) φ.
Proof.
  intros isLambda Hwf Hmkspec He2.
  eapply lambda_depth_to_vclorec in isLambda.
  unfold struct_items. simpl_eval_sitems.
  eapply He2.
  eapply prove_aSpec_rec; eauto.
  apply by_unfold_spec; eauto.
Qed.

(* [pure_eval_anonfun_nonrec] is to be used when a letrec expression
   defines a non-recursive function.  *)

Lemma pure_eval_letrec_nonrec `{Encode X} (τ : types)
  (P : τ -#> microvx -> Prop) η f x e e2 (φ : X -> Prop) ζ :
  (* Show the specification [P] holds over a call to any argument. *)
  (∀ v, predicate_over_function_body τ P ((f, v) :: η) (EAnonFun (AnonFun x e))) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec τ c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros Hmkspec He2. simpl_eval.
  apply He2.
  rewrite Spec_equiv. apply prove_Spec. apply Hmkspec.
Qed.

(* -------------------------------------------------------------------------- *)

(* [pure_EApp_partial] is a lemma for partial application. *)

Lemma pure_EApp_partial `{Encode X} (τ: types) η e e1 ζ
  (φ1 : X -> Prop) (P : Tcons X τ -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec (Tcons X τ) c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η (EApp e e1)) (λ c, ∃ v1, φ1 v1 ∧ Spec τ c (P v1)) ζ.
Proof.
  intros.
  eapply pure_eval_app; eauto.
  intros c v1 Hc Hv1.
  eapply pure_wp_mono. simpl in Hc. simp Spec in Hc.
  - intros c' Hc'. unfold returns; eexists; split; [ reflexivity | ].
    eauto.
  - intros ? [].
Qed.

(* This alternative formulation may look heaver, but it easier to use
   for an n-ary partial application. *)

Lemma pure_EApp_partial_alt `{Encode X} (τ : types) η e e1 ζ
  (φ1 : X -> Prop) (P : Tcons X τ -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec (Tcons X τ) c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η (EApp e e1))
    (λ c,
      Spec τ c (λ# (tt : τ) m,
                  ∃ (x : X), φ1 x ∧
                      (tapp (P x) tt) m))
    ζ.
Proof.
  intros.
  eapply pure_eval_app; eauto.
  intros c v1 Hc Hv1.
  simpl in Hc.
  eapply pure_wp_mono. simp Spec in Hc.
  - intros c' Hc'. unfold returns; eexists; split; [ reflexivity | ].
    eapply Spec_mono; [ apply Hc' | ].
    rewrite tforall_equiv; intros args m HP.
    rewrite tapp_bind.
    exists v1. split; [ apply Hv1 | apply HP ].
  - intros ? [].
Qed.

(* The following lemmas illustrate that we can reach our desired
   reasoning rule using chained applications of [pure_EApp_partial] or
   [pure_EApp_partial_alt]. *)

(* Although we still are missing a single lemma for n-ary applications,
   this demonstrates that a user could repeatedly use the partial
   application lemmas to prove an n-ary application. *)

Local Lemma pure_EApp_prop2 `{Encode A, Encode B, Encode C} η e e1 e2 (Ψ : C -> Prop) ζ
  (φ1 : A -> Prop) (φ2 : B -> Prop) (P : τ[A; B] -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec τ[A;B] c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η e2) φ2 ζ ->
  (∀ v1 v2, φ1 v1 -> φ2 v2 -> ∀ m, P v1 v2 m -> pure m Ψ ζ) ->
  pure (eval η (EApp (EApp e e1) e2)) Ψ ζ.
Proof.
  intros He He1 He2 Hmono.
  eapply pure_eval_app; eauto.
  eapply pure_EApp_partial; eauto. simpl.
  intros c v2 (v1 & HP & Hv1) Hv2.
  eapply Hmono; eauto. simp Spec in Hv1.
Qed.

Local Lemma pure_EApp_prop3 `{Encode A, Encode B, Encode C, Encode D} η e e1 e2 e3 (Ψ : D -> Prop) ζ
  (φ1 : A -> Prop) (φ2 : B -> Prop) (φ3 : C -> Prop) (P : τ[A; B; C] -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec τ[A;B;C] c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η e2) φ2 ζ ->
  pure (eval η e3) φ3 ζ ->
  (∀ v1 v2 v3, φ1 v1 -> φ2 v2 -> φ3 v3 -> ∀ m, P v1 v2 v3 m -> pure m Ψ ζ) ->
  pure (eval η (EApp (EApp (EApp e e1) e2) e3)) Ψ ζ.
Proof.
  intros He He1 He2 He3 Hmono.
  eapply pure_eval_app; eauto.
  (* Here either could also use [pure_EApp_partial]. *)
  eapply pure_EApp_partial_alt; eauto.
  eapply pure_EApp_partial_alt; eauto.
  intros c v3 HSpec Hv3; simpl in HSpec.
  simp Spec in HSpec.
  destruct (HSpec v3) as (v2 & Hv2 & (v1 & Hv1 & HP)).
  eapply Hmono; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* We provide a gallina function [pure_EApp_prop], which computes a
   proposition from an argument type, which generalises
   [pure_EApp_prop2] to n-ary applications. *)

(* Given a list of expressions [es := [e_1; ..; e_n]], [app_exprs e es] builds the term
   [EApp (EApp (EApp e e_n) ..) e_1]. *)

Fixpoint app_exprs e (es : list expr) :=
  match es with
  | [] => e
  | e' :: es =>
      EApp (app_exprs e es) e'
  end.

Section pure_EApp_prop_aux_def.

  (* We use sectioning here to avoid having to write out the following
     arguments, which are static from the point of view of the
     auxiliary function.*)

  Context (η : env) (ζ : exn -> Prop).
  Context (expr_base : expr) (goal_prop : expr -> Prop).

  Equations accumulate_argument_premises_and_build_consequence_hyp
    (τ : types) (es : list expr) (conseq_acc : τ -#> Prop -> Prop) :
    Prop :=
  | Tbase X, es, conseq_acc :=
      ∀ (e : expr) (φ : X -> Prop),
        pure (eval η e) φ ζ ->
        (* [Hconseq] is the consequence premise that we have built over
           all parameters and their postconditions. *)
        let Hconseq := ∀ (x : X), conseq_acc x (φ x) in
        (* [nested_eapp] is the nested application of the function
           [expr_base] to the paremeters [exprs]. *)
        let nested_eapp := app_exprs expr_base (e :: es) in
        Hconseq -> goal_prop (nested_eapp)
  | Tcons X τ', es, conseq_acc :=
      (* Quantify over the expression of a new argument and its postcondition. *)
      ∀ (e : expr) (φ : X -> Prop),
        pure (eval η e) φ ζ ->
        (* Add the hypothesis that evaluating [e] produces a value
            over which [φ] holds to our list of hypotheses. *)
        let conseq_acc :=
          (λ# (tt : τ') (B : Prop),
              ∀ (x : X),
                φ x ->
                (tapp (conseq_acc x) tt) B)
        in
        accumulate_argument_premises_and_build_consequence_hyp
          τ' (e :: es) conseq_acc.

  Arguments accumulate_argument_premises_and_build_consequence_hyp !τ /.
  Transparent accumulate_argument_premises_and_build_consequence_hyp.
  Strategy transparent [ accumulate_argument_premises_and_build_consequence_hyp ].

  (* The lemmas generated by [pure_EApp_prop] are monotonic in the
     consequence hypothesis. *)

  Local Lemma pure_EApp_mono (τ : types) es (Hmon' Hmon : τ -#> Prop -> Prop) :
  accumulate_argument_premises_and_build_consequence_hyp τ es Hmon' ->
  (∀ args (P : Prop), Hmon args P -> Hmon' args P) ->
  accumulate_argument_premises_and_build_consequence_hyp τ es Hmon.
  Proof.
    revert es.
    induction τ as [ X HX | X HX τ IH ];
      intros es HEApp' Hmono; simpl; intros ex φx Hex.
    { intros Hx.
      eapply HEApp'.
      - apply Hex.
      - intros x; apply Hmono; apply Hx. }

    eapply IH; [ apply HEApp'; apply Hex | ].
    intros args P; rewrite !tapp_bind.
    intros Hx x Hφ.
    rewrite forall_unroll in Hmono.
    apply Hmono. apply Hx. apply Hφ.
  Qed.

End pure_EApp_prop_aux_def.

(* Ensures that evaluating an expression `e` under `η` results in a value `c`
   that satisfies a specification `P`, and ultimately, that `pure m Ψ ζ` holds
   for the final result.
*)

Definition pure_EApp_prop `{Encode A} (τ : types) : Prop :=
  ∀ (η : env) (e : expr) (Ψ : A -> Prop)
  (ζ : exn -> Prop) (P : τ -#> microvx -> Prop),
  pure (eval η e) (λ c, Spec τ c P) ζ ->
  accumulate_argument_premises_and_build_consequence_hyp
    η ζ e
    (* The goal we want to prove: *) (λ e, pure (eval η e) Ψ ζ)
    (* The list of types of the parameters: *) τ
    (* The list of expressions we build: *) []
    (* The consequence hypothesis we build up: *)
    (λ# (tt : τ) (B : Prop),
         B -> ∀ m, (tapp P tt) m -> pure m Ψ ζ).

(* We always want [pure_EApp_prop] to unfold, the user should only be
   exposed to the generated lemma. *)
Arguments pure_EApp_prop {_ _} !τ /.
Transparent pure_EApp_prop.
Strategy transparent [ pure_EApp_prop ].

(* Auxiliary lemma used in the following proof of [pure_EApp]. *)

Local Lemma pure_EApp_prop_induction_step
  (τ : types)
  (η : env)
  e
  (ζ : exn -> Prop) (g : expr -> Prop) :
  ∀ (Hconseq : τ -#> Prop -> Prop) (es : list expr) (ei : expr),
    app_exprs (EApp e ei) es = app_exprs e (es ++ [ei]) ->
    accumulate_argument_premises_and_build_consequence_hyp
      η ζ
      (EApp e ei)
      g τ
      es
      Hconseq ->
    accumulate_argument_premises_and_build_consequence_hyp
      η ζ
      e
      g τ
      (es ++ [ei])
      Hconseq.
Proof.
  induction τ as [ X HX | X HX τ IH ];
    intros Hconseq es ei HeqEApp Happlied.
  (* Base case. *)
  { simpl in *; rewrite <- HeqEApp; apply Happlied. }
  (* Inductive case. *)
  intros ex φx Hx; cbn zeta.
  specialize (IH (λ# (tt : τ) (B : Prop),
                  ∀ x : X,
                    φx x →
                    tapp Hconseq (x, tt) B)).
  specialize (IH (ex :: es) ei).
  apply IH; [ simpl; f_equal; apply HeqEApp | ].
  apply Happlied. apply Hx.
Qed.

(* [pure_EApp] is the user-facing lemma for reasoning about the
   application of n-ary function.
   It uses the [pure_EApp_prop] gallina function to generate an
   appropriate lemma before applying it.

   The generated lemma is an n-ary equivalent of [pure_EApp_prop2],
   where [n] is dictated by the list of types [τ].

   Thus, a user must provide this list of types, and is expected to
   use a tactic of the form [apply (pure_EApp τ[ A1; A2; .. ; An ])]. *)

Lemma pure_EApp `{Encode A} (τ : types) :
  @pure_EApp_prop A _ τ.
Proof.
  unfold pure_EApp_prop.
  intros η e Ψ ζ P.

  (* We proceed by induction on [τ]. *)
  revert e.
  induction τ as [ X HX | X HX τ IH];
    intros e HSpec ex φx Hx; cbn zeta.

  { (* Base case. *)
    intros Hmono; simpl in *.
    eapply pure_eval_app; eauto.
    intros c x Hc Hφx.
    eapply Hmono; [ apply Hφx | ].
    simpl in Hc; simp Spec in Hc; apply Hc. }

  (* Inductive case: we use [pure_EApp_induction_step]. *)
  change [ex] with ([] ++ [ex]).
  apply pure_EApp_prop_induction_step; [ reflexivity | ].

  (* Specialize the induction hypothesis with some specification
     [P' : τ -#> microvx -> Prop] such that
     [pure (eval η (EApp e ex)) (λ c, Spec c P')] and
     [∀ args B, B ->
     (∀ x, φ x -> B -> ∀ m, (P x) args m -> pure m Ψ ζ) ->
     B ->
     ∀ m, P' args m -> pure m Ψ ζ]. *)
  set (P' := (λ# (tt : τ) m,
                      ∃ x,
                        φx x ∧
                        tapp P (x, tt) m)).
  specialize (IH P').
  specialize (IH (EApp e ex)).

  (* Use the induction hypothesis. *)
  eapply pure_EApp_mono; [ eapply IH | ].

  { (* Subgoal: the application satisfies our specification P' *)
    eapply pure_eval_app; eauto.
    intros c x Hc Hφx.
    eapply pure_wp_mono. simpl in Hc; simp Spec in Hc; apply Hc.
    - intros c' HSpec'; cbn beta in HSpec'.
      eexists; split; [ reflexivity | ].
      eapply Spec_mono; [ apply HSpec' | ].
      apply tforall_equiv; intros args m HP.
      subst P'; rewrite tapp_bind.
      exists x; split; [ apply Hφx | apply HP ].
    - intros ? []. }

  (* Subgoal: the specification P' implies the specification P *)
  subst P'; intros args B; rewrite !tapp_bind; simpl; intros Hmon HB.
  intros m (x & Hφx & HP).
  specialize (Hmon x Hφx).
  simpl in Hmon; rewrite tapp_bind in Hmon.
  eapply Hmon; eauto.
Defined.
