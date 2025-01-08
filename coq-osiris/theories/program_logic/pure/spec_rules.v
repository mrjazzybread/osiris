From osiris Require Import base lang semantics.

From osiris.program_logic.pure Require Import
  judgements pure_rules pattern_rules call_rules.

(* -------------------------------------------------------------------------- *)

(* TODO Comment *)

Local Definition acall η a v :=
  let 'AnonFun x e := a in
  eval ((x, v) :: η) e.

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

(* -------------------------------------------------------------------------- *)

(** Properties about [acall], [call]. *)

Local Lemma pure_acall_equiv `{Encode A} η a v φ ζ :
  pure (A := A) (eval.acall η a v) φ ζ <->
  pure (acall η a v) φ ζ.
Proof.
  destruct a; split;
    [ apply invert_pure_wp_eval | apply pure_CEval_inject2 ].
Qed.

(* TODO Move *)
Corollary pure_wp_bind_mono {A B E} (m : micro A E) (f g : A -> micro B E) φ ζ :
  (∀ a, pure_wp (f a) φ ζ -> pure_wp (g a) φ ζ) ->
  pure_wp (bind m f) φ ζ -> pure_wp (bind m g) φ ζ.
Proof.
  intros Hmono Hf. apply invert_pure_wp_bind in Hf.
  eapply pure_wp_bind, pure_wp_mono; eauto.
Qed.

Local Lemma pure_call_equiv `{Encode A} f v φ ζ :
  pure (A := A) (eval.call f v) φ ζ <->
  pure (call f v) φ ζ.
Proof.
  destruct f; try done; [ apply pure_acall_equiv | ].
  split; apply pure_wp_bind_mono; intros; simpl; by apply pure_acall_equiv.
Qed.

(* -------------------------------------------------------------------------- *)

(* As an example, we define [Spec_Unary'] as a way to spec_unaryify unary functions. *)

(* [call_spec_unary] is the type of spec_unaryifications over function calls. It
  depends on two arguments: the argument of the function call, and the
  computation resulting from calling the function on that argument. *)

(* [Spec_Unary c P] states that given a closure [ρ], the spec_unaryification [P]
  holds for any call of [c] on an argument. *)

Local Definition Spec_Unary `{Encode X} (ρ : val) (P : X -> microvx -> Prop) :=
  ∀ (x : X), P x (call ρ #x).

(* Consider for example the spec_unaryification of a function [sort]:
  [ Spec_Unary sort (λ l m, pure m (λ l', Sorted l' ∧ l' ≡ l) ⊥) ] *)

(* Example of a reasoning rule, for the creation of a [Spec_Unary c P]. *)

Local Lemma pure_eval_anon_unary `{Encode X} (P : X -> microvx -> Prop) η (xvar : var) e ζ :
  (∀ (x : X),
      P x (eval ((xvar, #x) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun xvar e))) (λ c, Spec_Unary c P) ζ.
Proof. intros; simpl_eval; by eapply pure_ret; eauto. Qed.

(* [pure_eval_letrec] allows us to prove that the body [e] of a letrec
  expression satisfies a spec_unaryification given by [P].

  In a first subgoal, we prove that any function call satisfies [P],
  under the assumption that calls to smaller arguments (according to
  [R]) are well-behaved.
  In the second subgoal, we prove [e2] while abstracting over [e]. *)

Local Lemma pure_eval_letrec_unary `{Encode X, Encode Y}
  (P : _ -> microvx -> Prop) η f (x : var) e1 e2 (φ : Y -> Prop) ζ
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  {WF_x : WellFounded X} :
  (* Show the specification [P] holds over a call to any argument
    [arg], under the assumption that [P] holds to a call over any
    argument [yval] smaller than [arg]. *)
  (∀ c (arg : X),
      Spec_Unary c (λ yval m, wf_relation (WF := WF_x) yval arg -> P yval m) ->
      P arg (eval ((x, #arg) :: (f, c) :: η) e1)) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec_Unary c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e1)] e2)) φ ζ.
Proof.
  intros Hmkspec_unary He2. simpl_eval. eapply He2.
  unfold Spec_Unary. intros v.
  induction v as [v IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl; simpl.
  eapply Hmkspec_unary. intros y. intros HR. by apply IH.
Qed.

(* -------------------------------------------------------------------------- *)

From Equations Require Import Equations.

(** Specification over function calls. *)

(* [Spec] matches on the list of argument types [args], producing a
   series of nested calls, where the base case is identical to the
   definition of [Spec_Unary]. *)

(* [Spec args c P] should be read as "[c] is a function value, with
   arguments described by [args], and with specification [P]." *)

Fixpoint lookup_rec_bindings rbs g : option anonfun :=
  match rbs with
  | RecBinding g' a :: rbs =>
      if (g =? g')%string then Some a else lookup_rec_bindings rbs g
  | [] =>
      None
  end.

Definition closure (f : val) : option (env * anonfun) :=
   match f with
  | VClo η a => Some (η, a)
  | VCloRec η rbs g =>
      let δ := eval_rec_bindings η rbs in
      let η0 := δ ++ η in
      match lookup_rec_bindings rbs g with
      | Some a => Some (η0, a)
      | None => None
      end
  | _ => None
  end.

Equations aSpec (A : types) (η : env) (f : anonfun) (P : A -#> microvx -> Prop) : Prop :=
| Tbase X, η, f, P :=
    ∀ (x : X), P x (acall η f #x)
| Tcons X TT, η, f, P :=
    ∀ (x : X),
      pure (acall η f #x)
        (λ c, match closure c with
                | None => False
                | Some (η, f) => aSpec TT η f (P x) end) ⊥.

(* [Spec] lifted to propositions over values. *)

Definition aSpec_val (A : types) (c : val) (P : A -#> microvx -> Prop) :=
  match closure c with
    | None => False
    | Some (η, f) => aSpec A η f P
  end.

Arguments aSpec {A} η f P.
Arguments aSpec_val {A} c P.

(* Spec η (AnonFun x e) P <-> *)
(* forall v, pure (eval ((x, v) :: η) e) (Spec_val P *)
(*   eval ((x, v) :: η) e. *)

(* -------------------------------------------------------------------------- *)


Equations Spec (A : types) (ρ : val) (P : A -#> microvx -> Prop) : Prop :=
| Tbase X, ρ, P :=
    ∀ (x : X), P x (call ρ #x)
| Tcons X TT, ρ, P :=
    ∀ (x : X), pure_wp (call ρ #x) (λ c, Spec TT c (P x)) ⊥.

Arguments Spec {A} ρ P.

(* -------------------------------------------------------------------------- *)

(** Basic properties about [Spec]. *)

(* [Spec_mono] states that [Spec] is monotonic over specifications. *)

Lemma Spec_mono {A : types} (P P' : A -#> microvx -> Prop) c :
  Spec c P ->
  (∀# args, ∀ m, P args m -> P' args m) ->
  Spec c P'.
Proof.
  revert c.
  induction A as [ | X HX arg_τ IH ]; intros c HP Hmono.
  { simp Spec in HP |-*. intros x.
    apply Hmono. apply HP. }
  simp Spec in HP |-*; intros x.
  eapply pure_wp_mono_ret; [ apply HP | ].
  intros c' HSpec'.
  apply IH with (P := P x); [ apply HSpec' | ].
  rewrite tforall_unroll in Hmono. apply Hmono.
Qed.

(* -------------------------------------------------------------------------- *)

(** Basic properties about [Spec]. *)

(* [Spec_mono] states that [Spec] is monotonic over specifications. *)

(* Lemma aSpec_mono {A : types} (P P' : A -#> microvx -> Prop) η f : *)
(*   aSpec η f P -> *)
(*   (∀# args, ∀ m, P args m -> P' args m) -> *)
(*   aSpec η f P'. *)
(* Proof. *)
(*   revert η f. *)
(*   induction A as [ | X HX arg_τ IH ]; intros η f HP Hmono. *)
(*   { simp aSpec in HP |-*. intros x. *)
(*     apply Hmono. apply HP. } *)
(*   simp aSpec in HP |-*; intros x. *)
(*   eapply pure_wp_mono_ret; [ apply HP | ]. *)
(*   cbn ; intros c' HSpec'. destruct (closure c') eqn: Hn; eauto. *)
(*   destruct p; subst. *)
(*   apply IH with (P := P x); [ apply HSpec' | ]. *)
(*   rewrite tforall_unroll in Hmono. apply Hmono. *)
(* Qed. *)

(* -------------------------------------------------------------------------- *)

(* [pure_call] specifies the nested call on expression [e] under environment [η]
   with specification [P]. *)

Equations pure_anonfun (A : types) (η : env) (e : expr) (P : A -#> microvx -> Prop) : Prop :=
| Tbase X, η, EAnonFun (AnonFun arg e), P :=
    ∀ (x : X), P x (eval ((arg, #x) :: η) e)
| Tcons X A', η, EAnonFun (AnonFun arg e), P :=
    ∀ (x : X), pure_anonfun A' ((arg, #x) :: η) e (P x)
(* If the expression isn't an [EAnonFun] we produce an unprovable proposition. *)
| _, _, _, _ := False.

Transparent pure_anonfun.
Arguments pure_anonfun {A} η e P.

Fixpoint AnonFun_depth e : nat :=
  match e with
  | EAnonFun (AnonFun _ e) => 1 + AnonFun_depth e
  | _ => 0
  end.

Local Instance afun_wf :
  WellFoundedRel _ (λ e1 e2, AnonFun_depth e1 < AnonFun_depth e2)%nat.
Proof.
  constructor. eapply Inverse_Image.wf_inverse_image. apply Nat.lt_wf_0.
Qed.

(* TODO Comment *)

Local Lemma pure_anonfun_Spec (A : types) η x e (P : A -#> microvx -> Prop) :
  pure_anonfun η (EAnonFun (AnonFun x e)) P ->
  @Spec A (VClo η (AnonFun x e)) P.
Proof.
  revert dependent x; revert η; revert dependent A.
  (* We do induction on the depth of the number or arguments that the function takes.*)
  induction e as [e IH] using
    (well_founded_induction (wf_def (WF := @WellFoundedRel_WellFounded _ _ afun_wf))).
  intros A P η arg HP.
  destruct A.
  (* Case: the tuple has size 1. *)
  { apply HP. }
  simp Spec; intros x.
  (* Case: the tuple has size [≥ 2]. *)
  (* Because the tuple has size greater than 1, we must have that the
     function body [e] is equal to [EAnonFun a] for some [a]. *)
  simpl in HP; specialize (HP x); simpl.
  destruct e; try (destruct A; contradiction);
    destruct a as [arg2 e2].
  (* Goal: [ P (x, args) (ret (VClo η ..)) (x, args)) ]. *)
  specialize (IH e2); simpl in IH.
  simpl; simpl_eval; simpl. apply pure_wp_ret.
  (* Apply the induction hypothesis. *)
  apply IH; [ lia | apply HP ].
Qed.

(* The reasoning rule for an n-ary non-recursive function. *)

Lemma pure_eval_anonfun (A : types) (P : A -#> microvx -> Prop) η (x : var) e ζ :
  pure_anonfun η (EAnonFun (AnonFun x e)) P ->
  pure (eval η (EAnonFun (AnonFun x e))) (λ c, Spec c P) ζ.
Proof.
  intros HP.
  simpl_eval; apply pure_wp_ret.
  unfold returns; eexists; split; [ reflexivity | ].
  by apply pure_anonfun_Spec.
Qed.

(* -------------------------------------------------------------------------- *)

From osiris Require Import program_logic.pure.toplevel_rules.

Lemma pure_eval_letrec (A : types)
  (R : A -> A -> Prop) (* LATER : State that this relation is well-founded *)
  (P : A -#> microvx -> Prop)
  (f : var) η e φ δ :
  (forall vf (x' : A),
    (forall x,
      R x x' ->
      Spec vf
        (tbind (fun (x' : A) (m : microvx) => x' = x /\ P x' m))) ->
     Spec (VCloRec ((f, vf) :: η) [RecBinding f e] f) P) ->
  struct_items (η, δ) [ILetRec [RecBinding f e]] φ.
Proof.
Admitted.

Local Lemma pure_eval_letrec' `{Encode X, Encode Y}
  (P : call_spec') (R : X -> X -> Prop) η f (x : var) e
  e2 (φ : Y -> Prop) ζ :
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  wf R ->
  (* Show the specification [P] holds over a call to any argument
    [arg], under the assumption that [P] holds to a call over any
    argument [yval] smaller than [arg]. *)
  (∀ c (arg : X),
      Spec' c (λ yval m, R yval arg -> P yval m) ->
      P arg (eval ((x, #arg) :: (f, c) :: η) e)) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec' c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.


(* (* [prove_Spec_rec] gives an induction principle for [Spec] by *)
(*    well-foundedness over the argument type. *) *)

(* Lemma prove_Spec_rec {A : types} *)
(*   (R : A -> A -> Prop) c *)
(*   (P : A -#> microvx -> Prop) : *)
(*   WellFounded R -> *)
(*   (∀# (args : A), *)
(*     (∀# sargs, R sargs args -> Spec c P) -> *)
(*     Spec c P)-> *)
(*   Spec c P. *)
(* Proof. *)
(*   intros Hwf HP. *)
(*   apply aSpec_Spec; eauto. *)
(*   intros args. *)

(*   induction args as [args IHR] using (well_founded_induction Hwf); clear Hwf. *)

(*   rewrite forallArgs_forall in HP. specialize (HP args). *)
(*   apply HP. *)
(*   apply forallArgs_forall; apply IHR. *)
(* Qed. *)
