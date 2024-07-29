From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality.
From osiris.proofmode Require Import simp_eval notations.

(* Because the relation [simp] is inductively defined, the [pure] judgement
   implies that [m] terminates. This forms a Hoare logic of total correctness
   for pure computations. *)

(* This file offers lemmas and tactics that help work with [pure] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)

Lemma pure_prove_bind_bind `{Encode A} `{Encode X} {E} m (a : A)
  (f : A -> _) (g : val -> _) (φ : X -> Prop) :
  simp ('c ← m;
        f c) (ret #a) ->
  pure (g #a) φ ->
  pure (X := E) ('v1 ← m;
        'v2 ← f v1;
        g v2) φ.
Proof.
  intros Hsimp ?.
  destruct_pure x.
  exists x. split; last auto.
  apply invert_simp_bind_ret in Hsimp as (b & Hb & Ha).

  eapply prove_simp_bind; first apply Hb.
  eapply prove_simp_bind; eauto.
Qed.

Lemma pure_bind_bind `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  pure ('x ← m;
        f x) ψ ->
  (forall y, ψ y -> pure (g #y) φ) ->
  pure ('v1 ← m;
        v2 ← f v1;
        g v2) φ.
Proof.
  intros (x & Hsimp & ?) ?.
  eapply pure_prove_bind_bind; first apply Hsimp.
  rewrite <- solve_encode_val.
  auto.
Qed.

Lemma pure_bind_binary `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  pure m (fun x => pure (f x) ψ) ->
  (forall y, ψ y -> pure (g #y) φ) ->
  pure ('x ← m;
        y ← f x;
        g y) φ.
Proof.
  intros.
  eapply pure_bind_bind; last done.
  eapply pure_bind; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [bind] composed with [as_bool]. *)

Lemma simp_as_bool (x : bool) (m : microvx) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma pure_bind_as_bool Y (_ : Encode Y)
  m (f : bool → microvx) (φ : bool → Prop) (ψ : Y → Prop) :
  pure m φ →
  (∀ (x : bool), φ x → pure (f x) ψ) →
  pure (bind (as_bool m) f) ψ.
  (* This is [@bind bool val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_bool.
Qed.

(* [bind] composed with [as_int]. *)

Lemma simp_as_int (x : Z) (m : microvx) :
  simp m (ret #x) →
  simp (as_int m) (ret (repr x)).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma pure_bind_as_int `{Encode Y}
  m (f : int → microvx) (φ : Z → Prop) (ψ : Y → Prop) :
  pure m φ →
  (∀ (x : Z), φ x → pure (f (repr x)) ψ) →
  pure (bind (as_int m) f) ψ.
  (* This is [@bind int val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_int.
Qed.

(* [bind] composed with [as_loc]. *)

Lemma simp_as_loc (x : loc) (m : microvx) :
  simp m (ret #x) ->
  simp (as_loc m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma pure_bind_as_loc `{Encode Y}
  m (f : loc → microvx) (φ : loc → Prop) (ψ : Y → Prop) :
  pure m φ →
  (∀ (x : loc), φ x → pure (f x) ψ) →
  pure (bind (as_loc m) f) ψ.
  (* This is [@bind loc val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_loc.
Qed.

(* [bind] composed with [as_struct]. *)

Lemma simp_as_struct (x : env) (m : microvx) :
  simp m (ret (VStruct x)) ->
  simp (as_struct m) (ret x).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma pure_bind_as_struct Y (_ : Encode Y)
  m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) :
  pure m (λ y : val, (exists y', y = VStruct y' /\ φ y)) →
  (∀ (x : env), φ (VStruct x) → pure (f x) ψ) →
  pure (bind (as_struct m) f) ψ.
  (* This is [@bind env val]. *)
Proof.
  intros (x & H & Hx) Hf.
  destruct Hx as (x' & ? & Hx').
  subst x. rewrite <- solve_encode_val in H.
  specialize (Hf x' Hx').
  destruct_pure y.
  exists y; eauto using prove_simp_bind, simp_as_struct.
Qed.

(* [bind] composed with [as_record]. *)

Lemma simp_as_record (x : env) (m : microvx) :
  simp m (ret (VRecord x)) ->
  simp (as_record m) (ret x).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma pure_bind_as_record Y (_ : Encode Y)
  m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) :
  pure m (λ y : val, exists y', y = VRecord y' /\ φ y) →
  (∀ (x : env), φ (VRecord x) → pure (f x) ψ) →
  pure (bind (as_record m) f) ψ.
  (* This is also [@bind env val]. *)
Proof.
  intros (x & H & Hx) Hf.
  destruct Hx as (x' & ? & Hx').
  subst x. rewrite <- solve_encode_val in H.
  specialize (Hf x' Hx').
  destruct_pure y.
  exists y; eauto using prove_simp_bind, simp_as_record.
Qed.

(* TODO add similar lemmas for other constructs *)

(* -------------------------------------------------------------------------- *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma pure_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ →
  pure (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [pure_consequence] and [pure_call]. *)

Lemma pure_call_consequence `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ →
  (∀ y, φ y → ψ y) →
  pure (call v1 v'2) ψ.
Proof.
  eauto using pure_consequence, pure_call.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma pure_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) :
  pure (acall η a v2) φ ->
  pure (call (VClo η a) v2) φ.
Proof.
  tauto.
Qed.

Lemma pure_enter_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  pure (
    let δ := eval_rec_bindings η rbs in
    let η := δ ++ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ ->
  pure (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma pure_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  pure (
    let δ := eval_rec_bindings η rbs in
    let η := δ ++ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ =
  pure (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma invert_pure_crash `{Encode Y} {X} (φ : Y -> Prop) :
  pure (X := X) Crash φ -> False.
Proof.
  intros. destruct_pure a. clarify_simp.
Qed.

Lemma invert_pure_call `{Encode Y} f v (φ : Y -> Prop) :
  pure (call f v) φ ->
  (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g.
Proof.
  intros Hcall.
  unfold call in Hcall.
  destruct f; simpl in Hcall;
    ((exfalso; by eapply invert_pure_crash) || eauto).
Qed.

Lemma pure_stop_eval {Y} `{Encode X} η e k (φ : X -> Prop) :
  pure (try2 (eval η e) k) φ ->
  @pure X _ Y (Stop CEval (η, e) k) φ.
Proof.
  intros.
  eapply pure_simp; [ apply SimpEval | assumption ].
Qed.

(* - [X] is the type of the argument.
   - [Y] is the type of result.
   - [a : A] is an auxiliary variable used to relate the pre and post. *)

Lemma pure_rec_call `{Encode X, Encode Y} {A}
  (η : env) (f : var) arg e1 (a : A) (x : X)
  (P : A -> X -> Prop) (φ : A -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P a x ->
  (∀ vf x,
      (∀ (a : A) (y : X), R y x -> P a y -> pure (call vf #y) (φ a)) ->
      (∀ (a : A), P a x -> pure (eval (arg ~> #x; f ~> vf; η) e1) (φ a))) ->
  pure (call (VCloRec η [RecBinding f (AnonFun arg e1)] f) #x) (φ a).
Proof.
  intros Hwf HPx Hrec.
  generalize dependent a.
  induction x as [x IH] using (well_founded_induction Hwf); intros.
  simpl; rewrite String.eqb_refl; apply pure_stop_eval; rewrite try2_ret_right.
  apply Hrec; [ intros a2 y HR HPy | assumption ].
  apply IH; auto.
Qed.

(* - [φ] is the toplevel specification.
   - [φf] is the specification of the function [f]. *)

Lemma pure_letrec `{Encode X, Encode Y} {A}
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : A -> Y -> Prop)
  (P : A -> X -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (a : A) (y : X), R y x -> P a y -> pure (call vf #y) (φf a)) ->
      ∀ (a : A), P a x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf a)) ->
  (* Subogal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ a x, P a x -> pure (call vf #x) (φf a)) ->
      pure (eval ((f, vf) :: η) e2) φ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ.
Proof.
  intros Hwf He1 He2.
  simpl_eval. apply He2. clear He2.
  intros a y HPy.
  eapply pure_rec_call; eauto.
Qed.

Lemma pure_rec_call_no_pre `{Encode X} `{Encode Y}
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : Y -> Prop)
  (R : X -> X -> Prop) :
  well_founded R ->
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (y : X), R y x -> pure (call vf #y) φf) ->
      pure (eval ((arg, #x) :: (f, vf) :: η) e1) φf) ->
  (* Subogal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ (x : X), pure (call vf #x) φf) ->
      pure (eval ((f, vf) :: η) e2) φ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ.
Proof.
  intros Hwf He1 He2.
  simpl_eval. apply He2. clear He2.
  intros y. change φf with ((fun (x : unit) => φf) ()).
  eapply pure_rec_call with (P := fun _ _ => True); eauto.
Qed.

Definition pure_call2 `{Encode X} vf arg1 arg2 (φ : X -> Prop) :=
  pure (call vf arg1) (fun c =>
                         pure (call c arg2) φ).

Lemma pure_rec_call2 `{Encode X, Encode Y, Encode W} {A}
  η f arg e1 (x : X) (y : Y) (a : A) (φ : A -> W -> Prop)
  (R : (X * Y) -> (X * Y) -> Prop) (P : A -> (X * Y) -> Prop)
  :
  well_founded R ->
  P a (x, y) ->
  (∀ vf x1 y1,
      (∀ (a : A) (x2 : X) (y2 : Y),
          R (x2, y2) (x1, y1) ->
          P a (x2, y2) ->
          pure_call2 vf #x2 #y2 (φ a)) ->
      (∀ (a : A),
          P a (x1, y1) ->
          pure (eval ((arg, #x1) :: (f, vf) :: η) e1) (λ c, pure (call c #y1) (φ a)))) ->
  pure_call2 (VCloRec η [RecBinding f (AnonFun arg e1)] f) #x #y (φ a).
Proof.
  intros Hwf HP Hrec.
  remember (x, y) as p eqn:Hpeq.
  rewrite (surjective_pairing p) in Hpeq.
  apply pair_eq in Hpeq as [<- <-].
  revert HP. generalize a. clear a.
  induction p as [p IH] using (well_founded_induction Hwf); intros.
  unfold pure_call2; simpl;
    rewrite String.eqb_refl; apply pure_stop_eval; rewrite try2_ret_right.
  apply Hrec; [ intros a2 x2 y2 HR HP2 | rewrite <- surjective_pairing; apply HP ].
  apply (IH (x2, y2)); auto.
  rewrite surjective_pairing; apply HR.
Qed.
