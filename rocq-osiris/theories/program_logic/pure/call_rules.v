From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic.pure Require Import
  judgements pure_rules pattern_rules.

(* This file defines contains reasoning rules about function calls. *)


(* -------------------------------------------------------------------------- *)
(** *Evaluating function calls *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma pure_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ ⊥ →
  pure (call v1 v'2) φ ⊥.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [pure_enc_consequence] and [pure_call]. *)

Lemma pure_call_consequence `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ ⊥ →
  (∀ y, φ y → ψ y) →
  pure (call v1 v'2) ψ ⊥.
Proof.
  intros -> Hcall1 Hconseq.
  eapply pure_mono;
  eauto using pure_call.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma pure_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) ψ :
  pure (acall η a v2) φ ψ ->
  pure (call (VClo η a) v2) φ ψ.
Proof.
  tauto.
Qed.

Lemma pure_enter_call_VCloRec `{Encode Y} η rbs g x e v2 (φ : Y → Prop) ψ :
  lookup_rec_bindings rbs g = Some (AnonFun x e) ->
  pure (eval ((x, v2) :: eval_rec_bindings η rbs ++ η) e) φ ψ ->
  pure (call (VCloRec η rbs g) v2) φ ψ.
Proof.
  intros Hlookup Hpure.
  simpl; rewrite Hlookup.
  eapply pure_CEval; rewrite try2_inject2_right.
  done.
Qed.

Lemma invert_pure_call `{Encode Y} f v (φ : Y -> Prop) :
  pure (call f v) φ ⊥ ->
  (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g.
Proof.
  intros Hcall.
  unfold call in Hcall.
  destruct f; simpl in Hcall;
    ((exfalso; by eapply invert_pure_wp_crash) || eauto).
Qed.

(* -------------------------------------------------------------------------- *)

(* A well-founded relation *)

Class WellFounded (A : Type) : Type :=
  { wf_relation : (A -> A -> Prop);
    wf_def : @well_founded A wf_relation }.

Class WellFoundedRel (A : Type) (R : A -> A -> Prop) :=
  { wf_rel_def : @well_founded A R }.

Definition WellFoundedRel_WellFounded {A} (R : A -> A -> Prop)
  {wfr: WellFoundedRel _ R} : WellFounded A :=
  {| wf_relation := R; wf_def := wf_rel_def |}.

Arguments wf_relation {_ WF} : rename.
Arguments wf_def {_ WF} : rename.


(* Recursive calls *)
Lemma pure_rec_call `{Encode X, Encode Y} (WF_x : WellFounded X)
  (η : env) (f : var) arg e (x : X) Ψ (P : X -> Prop) (φ : X -> Y -> Prop):
  P x ->
  (∀ vf x,
      (∀ (y : X), wf_relation (WF := WF_x) y x -> P y -> pure (call vf #y) (φ y) Ψ) ->
      (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e) (φ x) Ψ)) ->
  pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof.
  intros HPx Hrec.
  induction x as [x IH] using (well_founded_induction wf_def); intros.
  simpl. rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_inject2_right.
  apply Hrec; [ intros y HR HPy | assumption ].
  apply IH; eauto.
Qed.

Lemma pure_rec_call_simple `{Encode X, Encode Y} (WF_x : WellFounded X)
  (η : env) (f : var) arg e (x : X) Ψ (φ : X -> Y -> Prop):
  (∀ vf x,
    (∀ (y : X), wf_relation (WF := WF_x) y x -> pure (call vf #y) (φ y) Ψ) ->
    (pure (eval ((arg, #x) :: (f, vf) :: η) e) (φ x) Ψ)) ->
  pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof. intros; eapply pure_rec_call with (P := fun _ => True); eauto. Qed.

Lemma pure_rec_call_measure `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M)
  (η : env) (f : var) arg e Ψ (φ : Y -> Prop):
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        pure (call vf #y) φ Ψ) ->
    (pure (eval ((arg, #y') :: (f, vf) :: η) e) φ Ψ)) ->
  forall (x : X),
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) φ Ψ.
Proof.
  intros Hrec x.
  remember (measure x). revert x Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_inject2_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done.
Qed.

Lemma pure_rec_call_measure_gen `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M) x
  (η : env) (f : var) arg e Ψ (φ : X -> Y -> Prop):
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        pure (call vf #y) (φ y) Ψ) ->
    (pure (eval ((arg, #y') :: (f, vf) :: η) e) (φ y') Ψ)) ->
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof.
  intros Hrec.
  remember (measure x). revert x Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_inject2_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done.
Qed.

Lemma pure_rec_call_measure' `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M)
  (η : env) (f : var) arg e Ψ (φ : Y -> Prop) x P:
  P x ->
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        (P y -> pure (call vf #y) φ Ψ)) ->
    (pure (eval ((arg, #y') :: (f, vf) :: η) e) φ Ψ)) ->
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) φ Ψ.
Proof.
  intros HP Hrec.
  remember (measure x). revert x HP Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_inject2_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done.
Qed.

Lemma pure_rec_call_measure_gen' `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M) x P
  (η : env) (f : var) arg e Ψ (φ : X -> Y -> Prop):
  P x ->
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        (P y -> pure (call vf #y) (φ y) Ψ)) ->
    (P y' -> pure (eval ((arg, #y') :: (f, vf) :: η) e) (φ y') Ψ)) ->
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof.
  intros HP Hrec.
  remember (measure x). revert x HP Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_inject2_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done. done.
Qed.

Definition pure_call2 `{Encode X} vf arg1 arg2 (φ : X -> Prop) Ψ :=
  pure (call vf arg1)
    (λ c, pure (call c arg2) φ Ψ) Ψ.

Lemma pure_rec_call2 `{Encode X, Encode Y, Encode W}
  `{WF_x: WellFounded (X * Y)%type}
  η f arg e1 (x : X) (y : Y) (φ : X -> Y -> W -> Prop) Ψ
  (R : (X * Y) -> (X * Y) -> Prop) (P : X -> Y -> Prop)
  :
  P x y ->
  (∀ vf x1 y1,
      (∀ (x2 : X) (y2 : Y),
          wf_relation (WF := WF_x) (x2, y2) (x1, y1) ->
          R (x2, y2) (x1, y1) ->
          P x2 y2 ->
          pure_call2 vf #x2 #y2 (φ x2 y2) Ψ) ->
      (P x1 y1 ->
        pure (eval ((arg, #x1) :: (f, vf) :: η) e1)
          (λ c, pure (call c #y1) (φ x1 y1) Ψ) Ψ)) ->
  pure_call2 (VCloRec η [RecBinding f (AnonFun arg e1)] f) #x #y (φ x y) Ψ.
Proof.
  intros HP Hrec.
  remember (x, y) as p eqn:Hpeq.
  rewrite (surjective_pairing p) in Hpeq.
  apply pair_eq in Hpeq as [<- <-].
  revert HP.
  induction p as [p IH] using (well_founded_induction wf_def); intros.
  unfold pure_call2; simpl;
    rewrite String.eqb_refl; apply pure_CEval; rewrite try2_inject2_right.
  eapply pure_ret_mono.
  - apply Hrec; [ intros x2 y2 HR HP2 | apply HP ].
    apply (IH (x2, y2)); auto.
    rewrite surjective_pairing; apply HR.
  - auto.
Qed.

Arguments wf_relation {_ WF} : rename.
Arguments wf_def {_ WF} : rename.


(* Tactics for reasoning about recursive calls. *)

Tactic Notation "recursion" constr(t) :=
(eapply (pure_rec_call (X := t) _)).
Tactic Notation "recursion" "with" uconstr(R) :=
(eapply (pure_rec_call_simple (WellFoundedRel_WellFounded R))).
Tactic Notation "recursion" uconstr(H) "with" uconstr(R) :=
(eapply (pure_rec_call (WellFoundedRel_WellFounded R)) with (P := H)).
Tactic Notation "recursion" "{" "measure " uconstr(measure) "}" "∀" uconstr(g) :=
(eapply (pure_rec_call_measure_gen measure _ g)).
Tactic Notation "recursion" "{" "measure " uconstr(measure) "}" "∀" uconstr(g) "gen" uconstr(P) :=
(eapply (pure_rec_call_measure_gen' measure _ g P)).
Tactic Notation "recursion" "with" uconstr(R) "{" "measure " uconstr(measure) "}" :=
(eapply (pure_rec_call_measure measure (WellFoundedRel_WellFounded R))).
Tactic Notation "recursion" "with" uconstr(R) "{" "measure " uconstr(measure) "}" "∀" uconstr(g) :=
(eapply (pure_rec_call_measure_gen measure (WellFoundedRel_WellFounded R) g)).
