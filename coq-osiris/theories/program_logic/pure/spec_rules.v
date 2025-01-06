From osiris Require Import base lang semantics.

From osiris.program_logic.pure Require Import
  judgements pure_rules pattern_rules call_rules.

(* -------------------------------------------------------------------------- *)

(* TODO Comment *)

Local Definition acall η a v :=
  let 'AnonFun x e := a in
  eval ((x, v) :: η) e.

Lemma pure_acall_equiv `{Encode A} η a v φ ζ :
  pure (A := A) (eval.acall η a v) φ ζ <->
  pure (acall η a v) φ ζ.
Proof.
  destruct a; split;
    [ apply invert_pure_wp_eval | apply pure_CEval_inject2 ].
Qed.

Local Definition call f x :=
   match f with
  | VClo η a => acall η a x
  | VCloRec η rbs g =>
      let δ := eval_rec_bindings η rbs in
      let η0 := δ ++ η in
      'a ← lookup_rec_bindings rbs g;
      acall η0 a x
  | _ => type_mismatch "closure expected"
  end.

(* TODO Move *)
Corollary pure_wp_bind_mono {A B E} (m : micro A E) (f g : A -> micro B E) φ ζ :
  (∀ a, pure_wp (f a) φ ζ -> pure_wp (g a) φ ζ) ->
  pure_wp (bind m f) φ ζ -> pure_wp (bind m g) φ ζ.
Proof.
  intros Hmono Hf. apply invert_pure_wp_bind in Hf.
  eapply pure_wp_bind, pure_wp_mono; eauto.
Qed.

Lemma pure_call_equiv `{Encode A} f v φ ζ :
  pure (A := A) (eval.call f v) φ ζ <->
  pure (call f v) φ ζ.
Proof.
  destruct f; try done; [ apply pure_acall_equiv | ].
  split; apply pure_wp_bind_mono; intros; simpl; by apply pure_acall_equiv.
Qed.

(* -------------------------------------------------------------------------- *)

(* As an example, we define [Spec'] as a way to specify unary functions. *)

(* [call_spec] is the type of specifications over function calls. It
  depends on two arguments: the argument of the function call, and the
  computation resulting from calling the function on that argument. *)

Local Definition call_spec {A : Type} := A -> microvx -> Prop.

(* [Spec c P] states that given a closure [c], the specification [P]
  holds for any call of [c] on an argument. *)

Local Definition Spec `{Encode X} (c : val) (P : call_spec) :=
  ∀ (x : X), P x (call c #x).

(* Consider for example the specification of a function [sort]:
  [ Spec sort (λ l m, pure m (λ l', Sorted l' ∧ l' ≡ l) ⊥) ] *)

(* Example of a reasoning rule, for the creation of a [Spec c P]. *)

Local Lemma pure_eval_anon `{Encode X} (P : call_spec) η (xvar : var) e ζ :
  (∀ (x : X),
      P x (eval ((xvar, #x) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun xvar e))) (λ c, Spec c P) ζ.
Proof. intros; simpl_eval; by eapply pure_ret; eauto. Qed.

(* [pure_eval_letrec] allows us to prove that the body [e] of a letrec
  expression satisfies a specification given by [P].

  In a first subgoal, we prove that any function call satisfies [P],
  under the assumption that calls to smaller arguments (according to
  [R]) are well-behaved.
  In the second subgoal, we prove [e2] while abstracting over [e]. *)

Local Lemma pure_eval_letrec `{Encode X, Encode Y}
  (P : call_spec) (R : X -> X -> Prop) η f (x : var) e
  e2 (φ : Y -> Prop) ζ
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  {WF_x : WellFoundedRel _ R} :
  (* Show the specification [P] holds over a call to any argument
    [arg], under the assumption that [P] holds to a call over any
    argument [yval] smaller than [arg]. *)
  (∀ c (arg : X),
      Spec c (λ yval m, R yval arg -> P yval m) ->
      P arg (eval ((x, #arg) :: (f, c) :: η) e)) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros Hmkspec He2. simpl_eval. eapply He2.
  unfold Spec. intros v.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  simpl; rewrite String.eqb_refl; simpl.
  eapply Hmkspec. intros y. intros HR. by apply IH.
Qed.

(* -------------------------------------------------------------------------- *)

From Equations Require Import Equations.

(* We want to be able to reason on n-ary functions. We thus generalize
   [Spec'] to take a list of arguments described by an [arg_type]. *)

(* [Spec] matches on the list of argument types [arg_τ], producing a
   series of nested calls, where the base case is identical to the
   definition of [Spec']. *)

(* [Spec arg_τ c P] should be read as "[c] is a function value, with
   arguments described by [arg_τ], and with specification [P]." *)

Equations Spec (arg_τ : arg_type)
  (c : val) (P : arg_τ -#> microvx -> Prop) : Prop :=
| Arg1 X, c, P :=
    ∀ (x : X), P x (call c #x)
| ArgS X TT, c, P :=
    ∀ (x : X), pure_wp (call c #x) (λ c, Spec TT c (P x)) ⊥.

Arguments Spec {arg_τ} c P.

(* We can check on a simple example that [Spec] generalizes [Spec']. *)

Local Lemma pure_eval_anon_single `{Encode X} (P : tele[X] -#> microvx -> Prop) η (x : var) e ζ :
  (∀ (v : X), P v (eval ((x, #v) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun x e))) (λ c, Spec c P) ζ.
Proof.
  intros HP; simpl_eval; eapply pure_ret; encode.
Qed.

(* [Spec_mono] states that [Spec] is monotonic over specifications. *)

Lemma Spec_mono (arg_τ : arg_type) (P P' : arg_τ -#> microvx -> Prop) c :
  Spec c P ->
  (∀# args, ∀ m, (P args) m -> (P' args) m) ->
  Spec c P'.
Proof.
  revert c.
  induction arg_τ as [ | X HX arg_τ IH ]; intros c HP Hmono.
  { simp Spec in HP |-*. intros x.
    apply Hmono. apply HP. }
  simp Spec in HP |-*; intros x.
  eapply pure_wp_mono_ret; [ apply HP | ].
  intros c' HSpec'.
  apply IH with (P := P x); [ apply HSpec' | ].
  rewrite spec_once in Hmono. apply Hmono.
Qed.

Definition eq_partial_arg_app {arg_τ1 arg_τ2 arg_τ A} :
  arg_τ = arg_cat arg_τ1 arg_τ2 ->
  (arg_τ -#> A) ->
  (arg_τ1) ->
  (arg_τ2 -#> A).
Proof.
  intros -> P args.
  induction arg_τ1 as [ X | X ? arg_τ1 IH ].
  - auto.
  - destruct args. apply IH; auto.
Defined.

Lemma decompose_Spec (arg_τ1 arg_τ2 arg_τ : arg_type) (c : val) P
  (Heqargs : arg_τ = arg_cat arg_τ1 arg_τ2) :
  @Spec arg_τ c P ->
  @Spec arg_τ1 c
    (arg_bind (λ args m,
         let P' := eq_partial_arg_app Heqargs P args in
         pure_wp m (λ c, @Spec arg_τ2 c P') ⊥)).
Proof.
  subst.
  revert c; induction arg_τ1 as [ X | X ? arg_τ1 IH ]; intros c.
  { simpl. simp Spec. }
  simpl; simp Spec.
  intros Hwp x.
  eapply pure_wp_mono_ret; eauto.
  intros c' HSpec'.
  apply IH; apply HSpec'.
Qed.

(** [aSpec] is a restatement of [Spec], but with all of the
    arguments quantified before the nested calls.

    We then have the following equivalence:
    [Spec c P <-> ∀ args, aSpec c P args]. *)

Equations aSpec_aux (arg_τ : arg_type) (c : val)
  (P : arg_τ -#> microvx -> Prop) (args : arg_τ)
  : Prop :=
| Arg1 X, c, P, x :=
    P x (call c #x);
| ArgS X args_τ', c, P, {| arg_head := x; arg_tail := args'; |} :=
    pure_wp (call c #x)
      (λ c', aSpec_aux args_τ' c' (P x) args') ⊥
.

Definition aSpec {args_τ : arg_type} (c : val)
  (P : args_τ -#> microvx -> Prop) : args_τ -#> Prop :=
  arg_bind (aSpec_aux args_τ c P).

Ltac args_app_bind :=
  repeat match goal with
    | |- context[(arg_app (arg_bind _))] =>
        rewrite args_app_bind
    | |- context[(fun _ => arg_app (arg_bind _) _)] =>
        repeat f_equal;
        (* LATER: Fix this *)
        apply functional_extensionality; intros;
        by rewrite args_app_bind
  end.

Lemma unfold_aSpec `{Encode X} {arg_τ : arg_type} c (P : (ArgS X arg_τ) -#> microvx -> Prop) (args : arg_τ) x :
  arg_app (aSpec c P x) args =
    pure_wp (call c #x) (λ c', (aSpec c' (P x)) args) ⊥.
Proof.
  unfold aSpec; cbn.
  args_app_bind; simp aSpec_aux; args_app_bind.
Qed.

Ltac aSpec_simpl := unfold aSpec; simpl; simp aSpec_aux.
Tactic Notation "aSpec_simpl" "in" hyp(H) :=
  unfold aSpec in H; simpl in H; simp aSpec_aux in H.

Ltac Spec_hyp_normalize :=
  args_app_bind;
  match goal with
    | [ H : arg_to_type (ArgS _ _) |- _] => destruct H
    | [ H : arg_cons _ _ |- _] => destruct H
    | [ H : context[ arg_app (aSpec _ _) _] |- _] =>
        unfold aSpec in H; simpl in H;
        rewrite args_app_bind in H
    | [ H : context[ arg_app (aSpec _ _ _ _) _] |- _] =>
        unfold aSpec in H; simpl in H;
        rewrite args_app_bind in H
    | [ H : aSpec _ _ _ |- _] =>
        aSpec_simpl in H
    | [ H : aSpec_aux _ _ _ _ _ |- _] =>
        aSpec_simpl in H
  end.

Ltac Spec_auto :=
  repeat Spec_hyp_normalize ; try aSpec_simpl;
  rewrite ?args_app_bind.

Lemma Spec_aSpec (arg_τ : arg_type) (c : val) (P : arg_τ -#> microvx -> Prop) :
  Spec c P ->
  (∀ args, aSpec c P args).
Proof.
  revert c.
  induction arg_τ as [ | X HX arg_τ IH ].
  { intros c HSpec. aSpec_simpl.
    simp Spec in HSpec; apply HSpec. }
  intros c HSpec args.

  destruct args; simpl. rewrite unfold_aSpec.

  eapply pure_wp_mono_ret; [ simp Spec in HSpec; apply HSpec | ].
  intros c' HSpec'.
  apply IH. apply HSpec'.
Qed.

Lemma aSpec_Spec (arg_τ : arg_type) (c : val) (P : arg_τ -#> microvx -> Prop)
  `{Inhabited arg_τ}:
  (∀ args, (aSpec c P) args) ->
  Spec c P.
Proof.
  revert c.
  induction arg_τ as [ | X HX arg_τ IH ];
    intros c HSpec; simp Spec; intros x.
  { specialize (HSpec x); apply HSpec. }

  rewrite spec_once_tele in HSpec; specialize (HSpec x).
  assert (Inhabited arg_τ).
  { inversion H; inv inhabitant; constructor; eauto. }
  eapply pure_wp_mono_ret; last first.
  { intros c' HSpec'. apply IH; eauto.
    apply HSpec'. }
  eapply pure_wp_intersection.
  intros args.
  specialize (HSpec args).
  simpl in HSpec.
  rewrite unfold_aSpec in HSpec.
  apply HSpec.
Qed.

Lemma aSpec_mono (arg_τ : arg_type) (P P' : arg_τ -#> microvx -> Prop) c args :
  aSpec c P args ->
  (∀ m, (P args) m -> (P' args) m) ->
  aSpec c P' args.
Proof.
  unfold aSpec; rewrite !args_app_bind.
  revert c.
  induction arg_τ as [ | X HX arg_τ IH ]; intros c HP Hmono.
  { simp aSpec_aux in HP |-*.
    apply Hmono. apply HP. }
  destruct args as [x args].
  simp aSpec_aux in HP |-*.
  eapply pure_wp_mono_ret; [ apply HP | ].
  intros c' HSpec'.
  apply IH with (P := P x); [ apply HSpec' | ].
  apply Hmono.
Qed.

(* -------------------------------------------------------------------------- *)

(* We want to generalize this reasoning rule over arbitrary telescopes.
   We could give a lemma that simply requires the user to prove [Spec c P],
   but this would expose the nested calls created by [call_tele]. *)

(* Instead, we define [build_prop], which fetches the function body
   from a series of nested [EAnonFun], at a depth equal to the number
   of arguments specified by the telescope.  *)

Equations build_prop (arg_τ : arg_type) (η : env) (e : expr) (P : arg_τ -#> microvx -> Prop) : Prop :=
| Arg1 X, η, EAnonFun (AnonFun arg e), P :=
    ∀ (x : X), P x (eval ((arg, #x) :: η) e)
| ArgS X arg_τ', η, (EAnonFun (AnonFun arg e)), P :=
    ∀ (x : X), build_prop arg_τ' ((arg, #x) :: η) e (P x)
(* If the expression isn't an [EAnonFun] we produce an unprovable proposition. *)
| _, _, _, _ := False.

Transparent build_prop.

Fixpoint AnonFun_depth e : nat :=
  match e with
  | EAnonFun (AnonFun _ e) => 1 + AnonFun_depth e
  | _ => 0
  end.

Local Lemma afun_wf :
  wf (λ e1 e2, AnonFun_depth e1 < AnonFun_depth e2)%nat.
Proof.
  eapply wf_inverse_image. apply Nat.lt_wf_0.
Qed.

Local Lemma prove_Spec (arg_τ : arg_type) η x e (P : arg_τ -#> microvx -> Prop) :
  build_prop arg_τ η (EAnonFun (AnonFun x e)) P ->
  @Spec arg_τ (VClo η (AnonFun x e)) P.
Proof.
  revert dependent x; revert η; revert dependent arg_τ.
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
  simpl; simpl_eval; simpl. apply pure_wp_ret.
  (* Apply the induction hypothesis. *)
  apply IH; [ lia | apply HP ].
Qed.

(* The reasoning rule for an n-ary non-recursive function. *)

Lemma pure_eval_anon (arg_τ : arg_type) (P : arg_τ -#> microvx -> Prop) η (x : var) e ζ :
  build_prop arg_τ η (EAnonFun (AnonFun x e)) P ->
  pure (eval η (EAnonFun (AnonFun x e))) (λ c, Spec c P) ζ.
Proof.
  intros HP.
  simpl_eval; apply pure_wp_ret.
  unfold returns; eexists; split; [ reflexivity | ].
  by apply prove_Spec.
Qed.

(* -------------------------------------------------------------------------- *)

(* [call_tele] is a function that takes a closure [c] and arguments
   described by a telescope [arg_τ], and returns the computation obtained
   by successively calling [c] on the arguments. *)

Fixpoint call_tele {arg_τ : arg_type} (m : microvx) : arg_τ -#> microvx :=
  match arg_τ with
  | Arg1 X => λ (x : X), bind m (λ c, call c #x)
  | @ArgS X H arg_τ' =>
      λ (x : X), @call_tele arg_τ' (bind m (λ c, call c #x))
  end.

(* [prove_Spec_rec] gives an induction principle for [Spec] by
   well-foundedness over the argument type. *)

Lemma prove_Spec_rec
  (arg_τ : arg_type)
  {Inh_arg_τ: Inhabited arg_τ}
  (R : arg_τ -> arg_τ -> Prop) c
  (P : arg_τ -#> microvx -> Prop) :
  wf R ->
  (∀# (args : arg_τ),
    (∀# sargs, R sargs args -> aSpec c P sargs) ->
    aSpec c P args)->
  @Spec arg_τ c P.
Proof.
  intros Hwf HP.
  apply aSpec_Spec; eauto.
  intros args.

  induction args as [args IHR] using (well_founded_induction Hwf); clear Hwf.

  rewrite forallArgs_forall in HP. specialize (HP args).
  apply HP.
  apply forallArgs_forall; apply IHR.
Qed.

(* We would like to provide a [prove_Spec_rec]-like reasoning rule to
   the user. We can then improve the user experience by stepping
   through the nested calls that result from the unfolding of
   [aSpec c P args].

   This is done by [unfold_spec], which syntactically fetches the body
   of the function [c]. *)

Section unfold_spec_aux_def.

  Context (og_arg_τ : arg_type).
  Context (Pog : og_arg_τ -#> microvx -> Prop).
  Context (c : val).

  Equations unfold_spec_aux (arg_τ : arg_type)
    (η : env) (e : expr)
    (P : arg_τ -#> microvx -> Prop) (R : og_arg_τ -> arg_τ -> Prop)
    : Prop :=
  | Arg1 X, η, (EAnonFun (AnonFun arg e)), P, R :=
      ∀ (x : X),
        Spec c (arg_bind(λ sargs m,
                    R sargs x ->
                    Pog sargs m)) ->
        P x (eval ((arg, #x) :: η) e)
  | ArgS X arg_τ', η, (EAnonFun (AnonFun arg e)), P, R :=
      ∀ (x : X),
        let η := (arg, #x) :: η in
        let P := P x in
        let R := (λ (sargs : og_arg_τ) (args : arg_τ'),
                   R sargs {| arg_head := x; arg_tail := args |})
        in
        unfold_spec_aux arg_τ' η e P R
  | _, _, _, _, _ := False.

End unfold_spec_aux_def.

Strategy transparent [ unfold_spec_aux ].

Definition unfold_spec (arg_τ : arg_type) η f x e
  (R : arg_τ -> arg_τ -> Prop)
  (P : arg_τ -#> microvx -> Prop) :=
  (∀ c, unfold_spec_aux arg_τ P c arg_τ ((f, c) :: η) (EAnonFun (AnonFun x e)) P R).

Arguments unfold_spec arg_τ /.
Strategy transparent [ unfold_spec ].

Lemma aSpec_equiv (arg_τ : arg_type) η f x e (P : arg_τ -#> _) args :
  aSpec (VCloRec η [RecBinding f (AnonFun x e)] f) P args =
  aSpec (VClo ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η) (AnonFun x e)) P args.
Proof with Spec_auto.
  destruct arg_τ...
  { cbv; simp aSpec_aux.
    simpl; rewrite String.eqb_refl; simpl. reflexivity. }
  cbn...
  simpl; rewrite String.eqb_refl; simpl. reflexivity.
Qed.

Lemma Spec_equiv (arg_τ : arg_type) η f x e (P : arg_τ -#> _) :
  Spec (VCloRec η [RecBinding f (AnonFun x e)] f) P =
    Spec (VClo ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η) (AnonFun x e)) P.
Proof with Spec_auto.
  destruct arg_τ.
  { cbv; simp Spec.
    simpl; rewrite String.eqb_refl; reflexivity. }
  simp Spec; simpl; rewrite String.eqb_refl; reflexivity.
Qed.

Definition is_VCloRec v e :=
  ∃ η f x, v = VCloRec η [ RecBinding f (AnonFun x e) ] f.

Fixpoint is_lambda_of_depth e (arg_τ : arg_type) : Prop :=
  match arg_τ with
  | Arg1 _ =>
      exists x ebody,
      e = EAnonFun (AnonFun x ebody)
  | ArgS _ arg_τ' =>
      exists x e',
      e = EAnonFun (AnonFun x e') ∧ is_lambda_of_depth e' arg_τ'
  end.

Definition is_VCloRec_of_depth v arg_τ :=
  exists η f x e,
    v = VCloRec η [ RecBinding f (AnonFun x e) ] f ∧
      match arg_τ with
      | Arg1 _ => True
      | ArgS _ arg_τ' =>
          is_lambda_of_depth e arg_τ'
      end.

Lemma guarded_Spec_equiv (arg_τ arg_τ_og : arg_type) c
  (R : arg_τ_og -> arg_τ -> Prop) (P : arg_τ_og -#> microvx -> Prop) (args : arg_τ) :
  is_VCloRec_of_depth c arg_τ_og ->
  Spec c (arg_bind(λ sargs m,
              R sargs args ->
              P sargs m)) <->
  (∀# sargs, R sargs args -> aSpec c P sargs).
Proof.
  intros Hclo.
  split; [ clear Hclo | ].
  { revert c.
    induction arg_τ_og as [ X H | X H arg_τ_og IH ]; intros c.
    - unfold aSpec; simp Spec.
      intros Hcall x HR.
      rewrite args_app_bind.
      simp aSpec_aux. apply Hcall. apply HR.
    - intros HSpec.
      rewrite spec_once; intros sx.
      simp Spec in HSpec; specialize (HSpec sx).

      apply forallArgs_forall; intros sargs HR.
      unfold aSpec; rewrite args_app_bind; simp aSpec_aux.
      eapply pure_wp_mono_ret; [ apply HSpec | ].
      intros c' HSpec'.
      specialize (IH (λ t1 t2, R (ArgCons sx t1) t2)).
      specialize (IH (P sx)).
      specialize (IH c').
      specialize (IH HSpec').
      rewrite forallArgs_forall in IH; specialize (IH sargs HR).
      unfold aSpec in IH; rewrite args_app_bind in IH.
      apply IH. }

  intros HaSpec.

  destruct Hclo as (η & f & x & e & -> & He).
  assert (∀# sargs, R sargs args -> aSpec (VClo ((f, (VCloRec η [ RecBinding f (AnonFun x e)] f)) :: η) (AnonFun x e)) P sargs) as HSpec.
  { apply forallArgs_forall; intros sargs HR.
    rewrite forallArgs_forall in HaSpec; specialize (HaSpec sargs HR).
    rewrite <- aSpec_equiv. apply HaSpec. }
  clear HaSpec.
  rewrite Spec_equiv.

  generalize dependent ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η).
  revert dependent e.
  revert x.
  induction arg_τ_og as [ X H | X H arg_τ_og IH ]; intros x e He η0 HSpec.
  { simp Spec; intros vx HR.
    specialize (HSpec vx HR).
    unfold aSpec in HSpec; rewrite args_app_bind in HSpec.
    apply HSpec. }

  simp Spec; intros sx. simpl.

  destruct arg_τ_og.
  { inversion He as (y & e' & ->).
    simpl_eval. apply pure_wp_ret.
    simp Spec; intros vy HR.
    specialize (HSpec sx vy HR). simpl in HSpec.
    unfold aSpec in HSpec.
    cbv in HSpec. simp aSpec_aux in HSpec.
    simpl in HSpec.
    unfold eval in HSpec; rewrite seal_eq in HSpec; simpl in HSpec.
    apply invert_pure_wp_ret in HSpec.
    apply HSpec. }

  inversion He as (y & e' & -> & He').
  simpl_eval. apply pure_wp_ret.

  specialize (IH (λ t1 t2, R (ArgCons sx t1) t2)).
  specialize (IH (P sx)).
  specialize (IH y e' He').
  specialize (IH ((x, #sx) :: η0)).
  apply IH.

  rewrite spec_once in HSpec; specialize (HSpec sx).
  apply forallArgs_forall; intros sargs HR.
  rewrite forallArgs_forall in HSpec; specialize (HSpec sargs HR).
  unfold aSpec in HSpec. rewrite args_app_bind in HSpec.
  simp aSpec_aux in HSpec.
  simpl in HSpec.
  unfold eval in HSpec; rewrite seal_eq in HSpec; simpl in HSpec.
  apply invert_pure_wp_ret in HSpec.
  unfold aSpec; rewrite args_app_bind.
  apply HSpec.
Qed.

Lemma invert_unfold_spec (arg_τ : arg_type) (args : arg_τ) η f x e R P :
  unfold_spec arg_τ η f x e R P ->
  is_VCloRec_of_depth (VCloRec η [RecBinding f (AnonFun x e)] f) arg_τ.
Proof.
  intros Huspec.
  specialize (Huspec (VCloRec η [RecBinding f (AnonFun x e)] f)).
  remember P as Pog in Huspec at 1; clear HeqPog.
  remember arg_τ as TTog in R at 1, Pog, Huspec at 1; clear HeqTTog.

  eexists _, _, _, _; split; [ reflexivity | ].
  destruct arg_τ as [ | X HX arg_τ ]; [ done | ].
  destruct args as [vx args]. revert Huspec.
  generalize ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η); intros η0.
  generalize (VCloRec η [RecBinding f (AnonFun x e)] f) as v; intros v Huspec.

  revert dependent e. revert dependent X. revert x η0.
  induction arg_τ as [ Y HY | Y HY arg_τ' IH ]; intros x η0 X HX vx R P e Huspec.
  { destruct e; try (specialize (Huspec vx); contradiction).
    destruct a as [y e'].
    eexists _, _; reflexivity. }

  destruct e; try (specialize (Huspec vx); contradiction); destruct a as [y e'].
  destruct args as [vy args].
  specialize (IH args y ((x, #vx) :: η0) Y HY vy).
  specialize (IH (λ t1 t2, R t1 (ArgCons vx t2)) (P vx)).
  specialize (IH e').
  eexists _, _; split; [ reflexivity | ].
  apply IH.
  simpl in Huspec. specialize (Huspec vx).
  intros vyy.
  simpl. specialize (Huspec vyy).
  apply Huspec.
Qed.

Lemma by_unfold_spec (arg_τ : arg_type) η f x e R P :
  let c := VCloRec η [RecBinding f (AnonFun x e)] f in
  @unfold_spec arg_τ η f x e R P ->
  (∀# args,
    (∀# sargs, R sargs args -> aSpec c P sargs) ->
    aSpec c P args).
Proof with Spec_auto.
  unfold unfold_spec; intros HP.
  apply forallArgs_forall; intros args IHargs.
  pose proof (invert_unfold_spec arg_τ args η f x e R P HP) as Hclo.
  specialize (HP (VCloRec η [RecBinding f (AnonFun x e)] f)).

  (* Generalize all instances of [(f, c) :: η]. *)
  rewrite aSpec_equiv.
  revert HP.
  generalize ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η); intros η0.
  (* Generalize the [VCloRec] used in the recursive call. *)
  revert IHargs Hclo.
  generalize (VCloRec η [RecBinding f (AnonFun x e)] f); intros v.

  (* Generalize (TeleS X TT) where it doesn't participate in the
     recursion. This is exactly where [TTog] appears in the definition
     of [build_prop_rec_aux]. *)
  intros IHargs Hclo HP.

  remember P as Pog in HP at 1, IHargs; clear HeqPog.
  remember arg_τ as TTog in R at 1, Pog, HP at 1, IHargs, Hclo; clear HeqTTog.

  (* Generalize the statement for the induction. Notably, generalize
     over the head type of the telescope. *)
  revert x e η0 HP Hclo.
  induction arg_τ as [ X HX | X HX arg_τ IH]; intros x e η0 Hbp Hclo.

  (* Base case: the telescope is empty. *)
  { cbv... apply Hbp.
    apply <- (guarded_Spec_equiv (tele[X]) TTog _ R Pog args Hclo).

    apply IHargs. }

  (* Induction step: the telescope has some head type [Y]. *)
  destruct args as [vx args].
  simpl in Hbp. specialize (Hbp vx).

  (* We know that [e = EAnonFun (AnonFun y e')] by inversion on Hbp. *)
  destruct e;
    ((destruct arg_τ; contradiction)
     || destruct a as [y e']).

  (* Specialize the induction hypothesis before destructing args. *)
  specialize (IH (λ ttog tt,
                  R ttog {| arg_head := vx; arg_tail := tt |})).
  specialize (IH (P vx) args).
  specialize (IH IHargs).
  specialize (IH y e' ((x, #vx) :: η0)).
  (* We now step forward by evaluating [pure (eval .. (EAnonFun y e')) (λ c', ..)]. *)
  simpl... simp aSpec_aux.
  simpl; simpl_eval; simpl.
  apply pure_wp_ret.

  apply IH. apply Hbp.
  apply Hclo.
Qed.

(* -------------------------------------------------------------------------- *)

(* [pure_eval_letrec] is the user-facing lemma for reasoning about an
   n-ary letrec. Its statement makes use of [unfold_spec] to generate
   an appropriate lemma for every arity. *)

(** For example, if we have [arg_τ := tele[ list Z; Nat ] ],
    [pure_eval_letrec] becomes equal to

    Lemma pure_eval_letrec (P : list Z -> Nat -> microvx -> Prop)
    (R : (list Z * Nat) -> (list Z * Nat) -> Prop)
    η f x e e2 φ ζ :
    wf R ->
    (∀ c (l : list Z) (n : Nat),
       (∀ (l' : list Z) (n' : Nat), R (l', n') (l, n) -> aSpec c P l' n') ->
       P l n (eval ((y, n) :: (x, l) :: (f, c) :: η) e)) ->
    (∀ c, Spec c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
    pure (eval η (ELetRec [RecBinding f (AnonFun x (EAnonFun (AnonFun y e)))] e2)) φ ζ.

*)

Lemma pure_eval_letrec `{Encode X} (arg_τ : arg_type) `{Inhabited arg_τ}
  (P : arg_τ -#> microvx -> Prop)
  (R : to_product_type arg_τ -> to_product_type arg_τ -> Prop) η f (x : var) e
  e2 (φ : X -> Prop) ζ :
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  wf R ->
  (* Show the specification [P] holds over a call to any arguments,
     under the assumption that [P] holds to a call over any
     smaller arguments. *)
  unfold_spec arg_τ η f x e
    (λ arg1 arg2, R (to_tuple arg1) (to_tuple arg2)) P ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros Hwf Hmkspec He2. simpl_eval. eapply He2.
  eapply prove_Spec_rec; eauto.
  apply by_unfold_spec.
  apply Hmkspec.
Qed.


(* [pure_eval_anonfun_nonrec] is to be used when a letrec expression
   defines a non-recursive function.  *)

Lemma pure_eval_letrec_nonrec `{Encode X} (arg_τ : arg_type)
  (P : arg_τ -#> microvx -> Prop) η f x e e2 (φ : X -> Prop) ζ :
  let v := VCloRec η [RecBinding f (AnonFun x e)] f in
  (* Show the specification [P] holds over a call to any argument. *)
  (build_prop arg_τ ((f, v) :: η) (EAnonFun (AnonFun x e)) P) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros v Hmkspec He2. simpl_eval. eapply He2.
  pose proof (prove_Spec _ _ _ _ _ Hmkspec) as HSpec.
  destruct arg_τ;
    simp Spec;
    simpl in *; rewrite String.eqb_refl; apply HSpec.
Qed.


(* [pure_call_spec'] illustrates how we may want to use a [Spec c P]
   specification. *)

Local Lemma pure_call_spec' `{Encode X, Encode Y} (P : X -> microvx -> Prop) c v (φ : Y -> Prop) ζ :
  Spec' c P ->
  (∀ m, P v m -> pure m φ ζ) ->
  pure (eval.call c #v) φ ζ.
Proof.
  intros HSpec Hmon. eapply pure_call_equiv.
  apply Hmon. apply HSpec.
Qed.

(* [pure_EApp_partial] is a lemma for partial application. *)

Lemma pure_EApp_partial `{Encode X} (arg_τ: arg_type) η e e1 ζ
  (φ1 : X -> Prop) (P : ArgS X arg_τ -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η (EApp e e1)) (λ c, ∃ v1, φ1 v1 ∧ Spec c (P v1)) ζ.
Proof.
  intros.
  eapply pure_eval_app; eauto.
  intros c v1 Hc Hv1.
  apply pure_call_equiv. simpl in Hc.
  eapply pure_wp_mono. simp Spec in Hc.
  - intros c' Hc'. unfold returns; eexists; split; [ reflexivity | ].
    eauto.
  - intros ? [].
Qed.

Lemma pure_EApp_partial_alt `{Encode X} (arg_τ : arg_type) η e e1 ζ
  (φ1 : X -> Prop) (P : ArgS X arg_τ -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η (EApp e e1))
    (λ c,
      Spec c (arg_bind (λ (tt : arg_τ) m,
                  ∃ (x : X),
                      arg_app P
                      {|
                        arg_head := x ;
                        arg_tail := tt
                      |} m ∧
                      φ1 x))
    )
    ζ.
Proof.
  intros.
  eapply pure_eval_app; eauto.
  intros c v1 Hc Hv1.
  apply pure_call_equiv. simpl in Hc.
  eapply pure_wp_mono. simp Spec in Hc.
  - intros c' Hc'. unfold returns; eexists; split; [ reflexivity | ].
    eapply Spec_mono; [ apply Hc' | ].
    apply forallArgs_forall; intros args m HP.
    rewrite args_app_bind.
    exists v1. split; [ apply HP | apply Hv1 ].
  - intros ? [].
Qed.

(* The following lemmas illustrate that we can reach our desired
   reasoning rule using chained applications of [pure_EApp_partial] or
   [pure_EApp_partial_alt]. *)

(* Although we still are missing a single lemma for n-ary applications,
   this demonstrates that a user could repeatedly use the partial
   application lemmas to prove an n-ary application. *)

Local Lemma pure_EApp_prop2 `{Encode A, Encode B, Encode C} η e e1 e2 (Ψ : C -> Prop) ζ
  (φ1 : A -> Prop) (φ2 : B -> Prop) (P : tele[A; B] -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec c P) ζ ->
  pure (eval η e1) φ1 ζ ->
  pure (eval η e2) φ2 ζ ->
  (∀ v1 v2, φ1 v1 -> φ2 v2 -> ∀ m, P v1 v2 m -> pure m Ψ ζ) ->
  pure (eval η (EApp (EApp e e1) e2)) Ψ ζ.
Proof.
  intros He He1 He2 Hmono.
  eapply pure_eval_app; eauto.
  eapply pure_EApp_partial; eauto. simpl.
  intros c v2 (v1 & HP & Hv1) Hv2.
  apply pure_call_equiv.
  eapply Hmono; eauto. simp Spec in Hv1.
Qed.

Local Lemma pure_EApp_prop3 `{Encode A, Encode B, Encode C, Encode D} η e e1 e2 e3 (Ψ : D -> Prop) ζ
  (φ1 : A -> Prop) (φ2 : B -> Prop) (φ3 : C -> Prop) (P : tele[A; B; C] -#> microvx -> Prop) :
  pure (eval η e) (λ c, Spec c P) ζ ->
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
  destruct (HSpec v3) as (v2 & (v1 & HP & Hv2) & HH).
  apply pure_call_equiv.
  eapply Hmono; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* We provide a gallina function [pure_EApp_prop], which computes a
   proposition from an argument type. This proposition generalises
   [pure_EApp_prop2] to n-ary applications. *)

Fixpoint app_exprs e (es : list expr) :=
  match es with
  | [] => e
  | e' :: es =>
      EApp (app_exprs e es) e'
  end.

Section pure_EApp_prop_aux_def.

  Context (η : env) (ζ : exn -> Prop).
  Context (expr_base : expr) (goal_hyp : expr -> Prop).

  Equations pure_EApp_prop_aux (arg_τ : arg_type)
    (es : list expr) (mon_acc : arg_τ -#> Prop -> Prop) : Prop :=
  | Arg1 X, es, mon_acc :=
      ∀ (e : expr) (φ : X -> Prop),
        pure (eval η e) φ ζ ->
        let Hmono := ∀ (x : X), mon_acc x (φ x) in
        (* [nested_eapp] is the nested application from [expr_base] and [exprs]. *)
        let nested_eapp := app_exprs expr_base (e :: es) in
        (* we want to prove [goal_hyp], i.e. that evaluating the nested
           application satisfies [Ψ]. *)
        let goal_hyp := goal_hyp nested_eapp in
        (* [all_hyps] is the list of all hypotheses that we will chain with [->] arrows. *)
        Hmono -> goal_hyp
  | ArgS X arg_τ', es, mon_acc :=
      (* Quantify over the expression of a new argument and its postcondition. *)
      ∀ (e : expr) (φ : X -> Prop),
        pure (eval η e) φ ζ ->
        (* Add [e] to our list of expressions. *)
        let es' := e :: es in
        (* Add the hypothesis that evaluating [e] produces a value
            over which [φ] holds to our list of hypotheses. *)
        let mon_acc :=
          arg_bind (λ (tt : arg_τ') (B : Prop),
              ∀ (x : X),
                φ x ->
                (arg_app mon_acc {| arg_head := x; arg_tail := tt |} B))
        in
        pure_EApp_prop_aux arg_τ' es' mon_acc.

  Arguments pure_EApp_prop_aux !arg_τ /.
  Transparent pure_EApp_prop_aux.

End pure_EApp_prop_aux_def.

Definition pure_EApp_prop (arg_τ : arg_type) (η : env) (e : expr) (Ψ : val -> Prop)
  (ζ : exn -> Prop) (P : arg_τ -#> microvx -> Prop) : Prop :=
  pure (eval η e) (λ c, Spec c P) ζ ->
  pure_EApp_prop_aux η ζ e (λ e, pure (eval η e) Ψ ζ)
    arg_τ
    []
    (arg_bind (λ (tt : arg_τ) (B : Prop),
         B -> ∀ m, (arg_app P tt) m -> pure m Ψ ζ)).

Arguments pure_EApp_prop !arg_τ /.
Transparent pure_EApp_prop.

(* We always want [pure_EApp_prop] to unfold, the user should only be
   exposed to the generated lemma. *)

Strategy transparent [ pure_EApp_prop pure_EApp_prop_aux ].

(* The lemmas generated by [pure_EApp_prop] are monotonic in the
   consequence hypothesis. *)

Local Lemma pure_EApp_mono (arg_τ : arg_type) (η : env) ζ e fe es
  (Hmon' Hmon : arg_τ -#> Prop -> Prop) :
  pure_EApp_prop_aux η ζ e fe arg_τ es Hmon' ->
  (∀ args P, Hmon args P -> Hmon' args P) ->
  pure_EApp_prop_aux η ζ e fe arg_τ es Hmon.
Proof.
  revert es.
  induction arg_τ as [ X HX | X HX TT IH ];
    intros es HEApp' Hmono; simpl; intros ex φx Hex.
  { intros Hx.
    simp pure_EApp_prop_aux in HEApp'.
    eapply HEApp'. apply Hex.
    intros x; apply Hmono; apply Hx. }

  eapply IH; [ apply HEApp' | ]. apply Hex.
  intros args P; rewrite !args_app_bind.
  intros Hx x Hφ.
  apply Hmono. apply Hx. apply Hφ.
Qed.

Local Lemma pure_EApp_prop_induction_step (arg_τ : arg_type) (η : env) e
  (ζ : exn -> Prop) f :
  ∀ (Hmono : arg_τ -#> Prop -> Prop) (es : list expr) (ei : expr),
    app_exprs (EApp e ei) es = app_exprs e (es ++ [ei]) ->
    pure_EApp_prop_aux η ζ
      (EApp e ei)
      (λ e0, f e0) arg_τ
      es
      Hmono ->
    pure_EApp_prop_aux η ζ
      e
      (λ e0, f e0) arg_τ
      (es ++ [ei])
      Hmono.
Proof.
  induction arg_τ as [ X HX | X HX TT IH ];
    intros Hmono es ei HeqEApp Happlied.
  { simpl in *; rewrite <- HeqEApp; apply Happlied. }

  intros ex φx Hx; cbn zeta.
  simp pure_EApp_prop_aux in Happlied.
  specialize (IH (arg_bind (λ (tt : TT) (B : Prop),
            ∀ x : X,
              φx x →
              arg_app
                Hmono
                {|
                  arg_head := x ;
                  arg_tail := tt
                |} B))).
  specialize (IH (ex :: es) ei).
  apply IH; [ simpl; f_equal; apply HeqEApp | ].
  apply Happlied. apply Hx.
Qed.

Lemma pure_EApp (arg_τ : arg_type) η e Ψ ζ (P : arg_τ -#> microvx -> Prop) :
  pure_EApp_prop arg_τ η e Ψ ζ P.
Proof.
  (* Unfold [pure_EApp_prop]. *)
  unfold pure_EApp_prop.

  (* We proceed by induction on [arg_τ]. *)
  revert e.
  induction arg_τ as [ X HX | X HX arg_τ IH];
    intros e HSpec ex φx Hx; cbn zeta.

  { (* Base case. *)
    intros Hmono; simpl in Hmono.
    eapply pure_eval_app; eauto.
    intros c x Hc Hφx. apply pure_call_equiv.
    eapply Hmono; [ apply Hφx | ].
    simpl in Hc; simp Spec in Hc; apply Hc. }

  (* General case: our aim is to use [worse_pure_EApp_induction_step]. *)
  change [ex] with ([] ++ [ex]).
  apply pure_EApp_prop_induction_step; [ reflexivity | ].

  (* Specialize the induction hypothesis with a
     [P' : TeleS Y TT -#> microvx -> Prop] such that
     [pure (eval η (EApp e ex)) (λ c, Spec c P')] and
     [∀# args, ∀ B, P' args B -> (∀ x, φ x -> B -> ∀ m, (P x) args m -> pure m Ψ ζ)]. *)
  specialize (IH (arg_bind (λ (tt : arg_τ) m,
                      ∃ x,
                        φx x ∧
                          (arg_app
                             P
                             {|
                               arg_head := x;
                               arg_tail := tt |}
                          ) m))).
  specialize (IH (EApp e ex)).

  (* Use the induction hypothesis. *)
  eapply pure_EApp_mono; [ eapply IH | ].

  { (* Subgoal: [ pure (eval η (EApp e ex)) (λ c, Spec c P') ζ ]. *)
    eapply pure_eval_app; eauto.
    intros c x Hc Hφx. eapply pure_call_equiv.
    eapply pure_wp_mono. simpl in Hc; simp Spec in Hc; apply Hc.
    - intros c' HSpec'; cbn beta in HSpec'.
      unfold returns; eexists; split; [ reflexivity | ].
      eapply Spec_mono; [ apply HSpec' | ].
      apply forallArgs_forall; intros args m HP.
      rewrite args_app_bind.
      exists x; split; [ apply Hφx | apply HP ].
    - intros ? []. }

  (* Subgoal:
     [ ∀# args, ∀ B,
       P' args B ->
       ∀ x, φx x -> B ->
       ∀ m, (P x) arg m -> pure m Ψ ζ ]. *)
  intros args B.
  rewrite !args_app_bind. intros Hmon HB m (x & Hφx & HP).
  specialize (Hmon x Hφx). rewrite args_app_bind in Hmon.
  eapply Hmon; eauto.
Defined.

(* -------------------------------------------------------------------------- *)

(* [pure_EApp_prop] generates a lemma that allows us to use our [Spec]
   hypotheses. [pure_EApp_aSpec] is essentially the same, but for using
   [aSpec] hypotheses. *)

(* An example of the shape we want [pure_EApp_aSpec] lemmas to take: *)

Local Lemma pure_EApp_aSpec1 `{Encode X, Encode Y} η e e2
  (P : tele[X] -#> microvx -> Prop) (Ψ : Y -> Prop) ζ
  :
  ∀# (sargs : Arg1 X),
  pure (eval η e) (λ c, aSpec c P sargs) ζ ->
  pure (eval η e2) (singleton sargs) ζ ->
  (∀ m, P sargs m -> pure m Ψ ζ) ->
  pure (eval η (EApp e e2)) Ψ ζ.
Proof.
  apply forallArgs_forall; intros args He He2 Hmono.
  eapply pure_eval_app; eauto.
  intros c x Hc ->.
  apply pure_call_equiv.
  apply Hmono. apply Hc.
Qed.

Section pure_EApp_aSpec_def.

  Context (η : env) (ζ : exn -> Prop).
  Context (expr_base : expr) (goal_hyp : expr -> Prop).

  Equations pure_EApp_aSpec (arg_τ : arg_type) (args : arg_τ) (exprs : list expr) : Prop :=
  | Arg1 X, x, exprs :=
      ∀ (e : expr),
        pure (eval η e) (singleton x) ζ ->
        let nested_eapp := app_exprs expr_base (e :: exprs) in
        goal_hyp nested_eapp
  | ArgS X arg_τ', {| arg_head := x; arg_tail := args' |}, exprs :=
       ∀ (e : expr),
         pure (eval η e) (singleton x) ζ ->
         pure_EApp_aSpec arg_τ' args' (e :: exprs).

End pure_EApp_aSpec_def.

Strategy transparent [ pure_EApp_aSpec ].

Lemma pure_EApp_aSpec_induction_step (arg_τ : arg_type) η e ζ f :
  ∀ args (es : list expr) (ei : expr),
    app_exprs (EApp e ei) es = app_exprs e (es ++ [ei]) ->
    pure_EApp_aSpec η ζ
      (EApp e ei)
      (λ e  : expr, f e)
      arg_τ
      args
      es  ->
    @pure_EApp_aSpec η ζ
      e
      (λ e  : expr, f e)
      arg_τ
      args
      (es ++ [ei]).
Proof with Spec_auto.
  induction arg_τ as [ X HX | X HX TT IH ]; intros args es ei Heqapp Heapp...

  { simpl in *. rewrite <- Heqapp. apply Heapp. }

  intros ex Hex.

  specialize (IH arg_tail (ex :: es) ei).

  apply IH. { simpl. f_equal. apply Heqapp. }
  apply Heapp. apply Hex.
Qed.

(* The lemmas generated by [pure_EApp_aSpec] are monotonic in the goal
   hypothesis. *)

Local Lemma pure_EApp_aSpec_mono (arg_τ : arg_type) η e ζ args es
  (f f' : expr -> Prop) :
  pure_EApp_aSpec η ζ
    e
    (λ e0  : expr, f' e0)
    arg_τ
    args
    es  ->
  (∀ e, f' e -> f e) ->
  @pure_EApp_aSpec η ζ
    e
    (λ e0  : expr, f e0)
    arg_τ
    args
    es.
Proof with Spec_auto.
  intros HEApp Hmono.
  revert HEApp. revert es.
  induction arg_τ; intros es...
Qed.

Lemma pure_EApp' `{Encode Y} (arg_τ : arg_type) η e (Ψ : Y -> Prop) ζ
  (P : arg_τ -#> microvx -> Prop) :
  ∀# (args : arg_τ),
    @pure_EApp_aSpec η ζ
      e
      (λ e0, pure (eval η e) (λ c, aSpec c P args) ζ ->
             (∀ m, P args m -> pure m Ψ ζ) ->
             pure (eval η e0) Ψ ζ)
      arg_τ
      args
      [].
Proof with Spec_auto.
  apply forallArgs_forall; intros args.
  revert e.
  induction arg_τ as [ X HX | X HX TT IH]; intros e...
  { intros ex Hex He Hmono.
    eapply pure_eval_app; eauto.
    intros c y HP ->.
    apply pure_call_equiv.
    apply Hmono. apply HP. }

  intros ex Hex.
  specialize (IH (P arg_head) arg_tail (EApp e ex)).

  replace [ex] with ([] ++ [ex]) by reflexivity.
  eapply pure_EApp_aSpec_induction_step.
  { reflexivity. }

  eapply pure_EApp_aSpec_mono.
  { apply IH. }
  intros e0; simpl.
  intros Hpure He Hmono.
  apply Hpure; [ | apply Hmono ].

  eapply pure_eval_app; eauto.
  intros c ? Hc ->.
  eapply pure_call_equiv.
  simpl in Hc |-*... rewrite args_app_bind in Hc.

  eapply pure_wp_mono_throw...
  { eapply pure_wp_mono_ret; [ by simp aSpec_aux in Hc | ].
    intros...
    unfold returns; eexists; split; [ reflexivity | ]...
    done. }
  intros ? [].
Qed.



Lemma structs_letrec (arg_τ : arg_type) `{Inhabited arg_τ}
  (R : to_product_type arg_τ -> to_product_type arg_τ -> Prop)
  η δ f (x : var) e (P : arg_τ -#> microvx -> Prop) sitems φ :
  wf R ->
  unfold_spec arg_τ η f x e (λ arg1 arg2, R (to_tuple arg1) (to_tuple arg2)) P ->
  (∀ c, Spec c P -> struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
  struct_items (η, δ) (ILetRec [RecBinding f (AnonFun x e)] :: sitems) φ.
Proof.
  intros Hwf Hmkspec He2.
  unfold struct_items. simpl_eval_sitems.
  eapply He2.
  eapply prove_Spec_rec; eauto.
  apply by_unfold_spec.
  apply Hmkspec.
Qed.

(* TODO: What is this lemma doing here? *)
Local Lemma structs_letrec_single `{Encode X} (R : X -> X -> Prop) η δ f (x : var) e
  (P : X -> microvx -> Prop)
  sitems φ :
  wf R ->
  (∀ c v',
      Spec' c (λ v m, R v v' -> P v m) ->
      P v' (eval ((x, #v') :: (f, c) :: η) e)) ->
  (∀ c, Spec' c P ->
       struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
  struct_items (η, δ) (ILetRec [RecBinding f (AnonFun x e)] :: sitems) φ.
Proof.
  intros Hwf Hmkspec He2.
  unfold struct_items; simpl_eval_sitems.
  eapply He2. intros v.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  simpl; rewrite String.eqb_refl; simpl.
  by eapply Hmkspec.
Qed.


(* [prove_Spec_recer] gives an induction principle for [Spec] by
   well-foundedness over the argument type. *)

Lemma prove_Spec_recer1 `{Encode X, Inhabited (Arg1 X)}
  (R : X -> X -> Prop) c
  (P : X -> microvx -> Prop) :
  wf R ->
  (∀ (args : X),
      Spec c (arg_bind(λ (x : Arg1 X) m, R x args -> P x m)) ->
    @aSpec (Arg1 X) c P args)->
  @Spec (Arg1 X) c P.
Proof.
  intros Hwf HP.
  eapply prove_Spec_rec; eassumption.
Qed.

Lemma prove_Spec_recer2 `{Encode X, Inhabited (ArgS X arg_τ)}
  (R : ArgS X arg_τ -> ArgS X arg_τ -> Prop)
  (P : ArgS X arg_τ -#> microvx -> Prop)
  η f xvar af :
  let c := VCloRec η [RecBinding f (AnonFun xvar (EAnonFun af))] f in
  wf R ->
  (∀ (args : ArgS X arg_τ),
      Spec c (arg_bind(λ (x : Arg1 X) (m : microvx),
                  ∀# (sargs : arg_τ),
                  R (ArgCons x sargs) args ->
                  pure m (λ c', aSpec c' (P x) sargs) ⊥)) ->
    arg_app (@aSpec (ArgS X arg_τ) c P args.(arg_head)) args.(arg_tail))->
  @Spec (ArgS X arg_τ) c P.
Proof.
  intros Hc Hwf HP.
  eapply prove_Spec_rec; try eassumption.
  rewrite spec_once; intros x.
  apply forallArgs_forall; intros args.
  intros IH.
  rewrite spec_once in IH.
  unfold aSpec; rewrite args_app_bind.
  simp aSpec_aux.
  rewrite spec_once_tele in HP.
  specialize (HP x args).
  unfold aSpec in HP.
  simpl in HP; rewrite args_app_bind in HP.
  simp aSpec_aux in HP.
  apply HP.
  simp Spec. intros y.
  apply forallArgs_forall; intros sargs HR.
  specialize (IH y). rewrite forallArgs_forall in IH.
  specialize (IH sargs HR).
  unfold aSpec in IH; rewrite args_app_bind in IH.
  simp aSpec_aux in IH.
  eapply pure_wp_mono_ret; [ apply IH | ].
  intros c' HSpec'.
  unfold returns; eexists; split; [ reflexivity | ].
  rewrite args_app_bind; apply HSpec'.
Qed.


Lemma prove_Spec_recer `{Encode X, Encode Y, Inhabited (ArgS X (ArgS Y arg_τ))}
  (R : ArgS X (ArgS Y arg_τ) -> ArgS X (ArgS Y arg_τ) -> Prop)
  (P : ArgS X (ArgS Y arg_τ) -#> microvx -> Prop)
  η f xvar yvar e :
  let c := VCloRec η [RecBinding f
                        (AnonFun xvar
                           (EAnonFun
                              (AnonFun yvar e)))] f in
  wf R ->
  (∀ (args : ArgS X (ArgS Y arg_τ)),
      @Spec tele[ X; Y ] c (λ (x : X) (y : Y) (m : microvx),
                  ∀# (sargs : arg_τ),
                  R (ArgCons x (ArgCons y sargs)) args ->
                  pure m (λ c', aSpec c' (P x y) sargs) ⊥) ->
      let x := args.(arg_head) in
      let y := args.(arg_tail).(arg_head) in
      let args := args.(arg_tail).(arg_tail) in
    arg_app (@aSpec (ArgS X (ArgS Y arg_τ)) c P x y) args)->
  @Spec (ArgS X (ArgS Y arg_τ)) c P.
Proof.
  intros Hc Hwf HP.
  eapply prove_Spec_rec; try eassumption.
  rewrite spec_once; intros x.
  rewrite spec_once; intros y.
  apply forallArgs_forall; intros args.
  intros IH.

  unfold aSpec; rewrite args_app_bind.
  simp aSpec_aux.
  rewrite spec_once_tele in HP; specialize (HP x).
  rewrite spec_once_tele in HP; specialize (HP y args).
  simpl in HP.

  unfold aSpec in HP.
  simpl in HP; rewrite args_app_bind in HP.
  simp aSpec_aux in HP.
  apply HP.
  simp Spec. intros x'.
  simpl; rewrite String.eqb_refl; simpl; simpl_eval; apply pure_wp_ret.
  simp Spec. intros y'.
  apply forallArgs_forall; intros sargs HR.
  simpl.

  rewrite spec_once in IH; specialize (IH x').
  rewrite spec_once in IH; specialize (IH y').
  rewrite forallArgs_forall in IH; specialize (IH sargs HR).
  unfold aSpec in IH; rewrite args_app_bind in IH.
  simp aSpec_aux in IH.

  simpl in IH; rewrite String.eqb_refl in IH; simpl in IH.
  unfold eval in IH; rewrite seal_eq in IH; simpl in IH.
  apply invert_pure_wp_ret in IH.
  simp aSpec_aux in IH.
  simpl in IH.
  eapply pure_wp_mono_ret. apply IH.
  intros c' HSpec'.
  unfold returns; eexists; split; [ reflexivity | ].
  rewrite args_app_bind; apply HSpec'.
Qed.
