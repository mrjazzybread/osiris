From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality simp.

(* This file also defines the judgement [SIMP m φ], which asserts that the
   computation [m] is pure and eventually produces a result that satisfies
   the postcondition [φ]. This judgement and its reasoning rules for a
   simple Hoare logic (of total correctness) for pure computations. *)

(* This file offers lemmas and tactics that help work with [SIMP] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)

(* The judgement [SIMP m φ] asserts that the computation [m] can be simplified
   to [ret #x], where [x] is a (logical) value so that [φ x] holds. *)

(* Because the relation [simp] is inductively defined, this judgement implies
   that [m] terminates. This is a Hoare logic of total correctness. *)

Definition SIMP `{Encode X} (m : micro val) (φ : X → Prop) :=
  ∃ x, simp m (ret #x) ∧ φ x.

(* -------------------------------------------------------------------------- *)

(* Basic reasoning rules for [ret], [bind], [try]. *)

Lemma SIMP_ret `{Encode X} (φ : X → Prop) v x :
  v = #x →
  φ x →
  SIMP (ret v) φ.
Proof.
  unfold SIMP. intros. subst. eauto with simp.
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [Next],
   so the handler [g] is dead and no proof obligation bears on it. *)

Lemma SIMP_try X (_ : Encode X) Y (_ : Encode Y)
  m f g (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (try m f g) ψ.
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_try.
Qed.

(* This variant of the Bind rule has two premises. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind X (_ : Encode X) Y (_ : Encode Y)
  m f (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (bind m f) ψ.
Proof.
  rewrite bind_as_try. eauto using SIMP_try.
Qed.

(* This Iris-style variant of the Bind rule has just one premise. It is
   obtained by choosing the least precise φ in the above lemma. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind_unary X (_ : Encode X) Y (_ : Encode Y)
  m f (ψ : Y → Prop) :
  SIMP m (λ (x : X), SIMP (f #x) ψ) →
  SIMP (bind m f) ψ.
Proof.
  eauto using SIMP_bind.
Qed.

(* -------------------------------------------------------------------------- *)

(* This lemma allows simplifying a goal of the form [SIMP m φ] by first
   simplifying [m] into [m'], then reasoning about [m']. *)

Lemma SIMP_simp `{Encode X} m m' (φ : X → Prop) :
  simp m m' →
  SIMP m' φ →
  SIMP m φ.
Proof.
  unfold SIMP.
  intros ? (x & ? & ?).
  eauto with simp.
Qed.

(* The Consequence rule. *)

Lemma SIMP_covariant `{Encode X} m (φ ψ : X → Prop) :
  SIMP m φ →
  (∀ x, φ x → ψ x) →
  SIMP m ψ.
Proof.
  intros (x & Hm & Hx) ?. exists x. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [bind] composed with [as_bool]. *)

Lemma simp_as_bool (x : bool) (m : micro val) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_bool Y (_ : Encode Y)
  m (f : bool → micro val) (φ : bool → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : bool), φ x → SIMP (f x) ψ) →
  SIMP (bind (as_bool m) f) ψ.
  (* This is [@bind bool val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_bool.
Qed.

(* [bind] composed with [as_int]. *)

Lemma simp_as_int (x : Z) (m : micro val) :
  simp m (ret #x) →
  simp (as_int m) (ret (repr x)).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_int Y (_ : Encode Y)
  m (f : int → micro val) (φ : Z → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : Z), φ x → SIMP (f (repr x)) ψ) →
  SIMP (bind (as_int m) f) ψ.
  (* This is [@bind int val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_int.
Qed.

(* TODO add similar lemmas for [as_loc] and possibly others *)

(* -------------------------------------------------------------------------- *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma SIMP_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [SIMP_covariant] and [SIMP_call]. *)

Lemma SIMP_call_covariant `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  (∀ y, φ y → ψ y) →
  SIMP (call v1 v'2) ψ.
Proof.
  eauto using SIMP_covariant, SIMP_call.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma SIMP_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) :
  SIMP (acall η a v2) φ →
  SIMP (call (VClo η a) v2) φ.
Proof.
  tauto.
Qed.

Lemma SIMP_enter_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  SIMP (
    let δ := eval_rec_bindings η rbs in
    let η := concat δ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ →
  SIMP (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma invert_SIMP_crash `{Encode Y} (φ : Y -> Prop) :
  SIMP Crash φ -> False.
Proof.
  intros (? & Hsimp & _).
  by apply simp_crash_ret in Hsimp.
Qed.

Lemma invert_SIMP_call `{Encode Y} f v (φ : Y -> Prop) : 
  SIMP (call f v) φ ->
  (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g. 
Proof.
  intros Hcall.
  unfold call in Hcall.
  destruct f; simpl in Hcall;
    ((exfalso; by eapply invert_SIMP_crash) || eauto).
Qed.

Fixpoint replace_rec_bindings rbs fname a {struct rbs} :=
  match rbs with
  | RecBiNil => RecBiNil
  | RecBiCons (RecBinding gname a') rbs' =>
      if (fname =? gname)%string then
        RecBiCons (RecBinding fname a) rbs'
      else
        RecBiCons (RecBinding gname a') (replace_rec_bindings rbs' fname a)
  end.

Lemma destruct_lookup_rec_bindings rbs g :
  lookup_rec_bindings rbs g = missing_variable g \/ exists a, lookup_rec_bindings rbs g = ret a.
Proof.
  induction rbs as [|[f a] ? IH]; first auto.
  simpl.
  destruct (g =? f)%string; first eauto.
  apply IH.
Qed.

Lemma replace_rec_bindings_not_in rbs g :
  lookup_rec_bindings rbs g = missing_variable g ->
  forall a, replace_rec_bindings rbs g a = rbs.
Proof.
  intros H a.
  induction rbs as [|[f a'] ? IH]; first done.
  simpl in *.
  destruct (g =? f)%string; first discriminate.
  by rewrite IH.
Qed.

Lemma replace_rec_bindings_in rbs g a :
  lookup_rec_bindings rbs g = ret a ->
  forall a', lookup_rec_bindings (replace_rec_bindings rbs g a') g = ret a'.
Proof.
  intros H.
  induction rbs as [|[f ?] ? IH]; first discriminate.
  simpl in *.
  destruct (g =? f)%string eqn:Hcmp; simpl.
  { simpl. rewrite String.eqb_refl. reflexivity. }
  rewrite Hcmp.
  by apply IH.
Qed.

Notation "'RecBnd' recbnd " := (RecBiCons recbnd RecBiNil) (at level 90).

Lemma SIMP_rec_call `{Encode X} `{Encode Y} (fname : var) (v : X)
  (P : X -> Prop) (ψ : X -> Y -> Prop) (φ : Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall x y, ψ x y -> φ y) ->
  (forall (vf : val) v, P v ->
      (forall v', R v' v ->
             P v' ->
             match vf with
             | VCloRec η rbs f =>
                 let δ := eval_rec_bindings η rbs in
                 let η := concat δ η in
                   SIMP (
                       a ← lookup_rec_bindings rbs f ;
                      acall η a #v'
                    ) (ψ v')
              | _ => False
             end) ->
      SIMP (call vf #v) (ψ v)) ->
  (forall η rbs f, SIMP (call (VCloRec η rbs f) #v) φ).
Proof.
  intros Hwf HP Hcov Hrec. intros ???.
  eapply SIMP_covariant; last apply Hcov.
  induction v as [v IH] using (well_founded_induction Hwf).
  apply Hrec; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* TODO reduce just beta-redexes in the goal (possibly under ∀ and →) *)

Ltac beta :=
  cbn beta.

Goal (λ (x : bool), negb x = ((λ (x : bool), x) false)) true.
Proof.
  beta. reflexivity.
Qed.

(* [SIMP_ret] expects a goal of the form [SIMP (ret v) φ]. It applies
   the lemma [SIMP_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac SIMP_ret :=
  simple eapply SIMP_ret; [ solve [ encode ] | beta ].

(* [SIMP_simp] expects a goal of the form [SIMP m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [SIMP m' φ]. *)

Ltac SIMP_simp :=
  simple eapply SIMP_simp; [ simp_really |].

(* SIMP0 leaves zero subgoal. *)
(* SIMP1 leaves one subgoal, which may have an arbitrary shape. *)

Ltac SIMP0 :=
  try SIMP_simp;
  first [

    SIMP_ret; [
      (* goal: [φ x] *)
      SIMP_close
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* goal: [SIMP (call #x) φ] *)
      SIMP_close
    ]

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* goal: [∀ x, φ x → φ' x] *)
    | SIMP_close
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind        ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_try         ; [ SIMP0 | beta; intros; SIMP0 ]

  | SIMP_close

  ]

with SIMP1 :=
  try SIMP_simp;
  first [

    SIMP_ret (* residual goal: [φ x] *)

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* residual goal: [∀ x, φ x → φ' x] *)
    | beta
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* residual goal: [SIMP (call #x) φ] *)
      idtac
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind        ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_try         ; [ SIMP0 | (* residual goal *) beta ]

  | idtac (* residual goal *)

  ]

with SIMP_close :=
  solve [ eauto with SIMP_specs representable ].

Ltac SIMP1_call_step :=
  first [
    eapply SIMP_enter_call_VClo
  | eapply SIMP_enter_call_VCloRec
  ].

Ltac SIMP_enter :=
  SIMP1_call_step;
  SIMP1.

Ltac SIMP_continue :=
  lazymatch goal with
  | |- SIMP ?m _ =>
      unfold_breakpoint m;
      SIMP1
  | _ =>
      fail "[SIMP_continue] expects a goal of the form [SIMP _ _]"
  end.

Ltac SIMP_specify x φ :=
  lazymatch goal with
  | |- SIMP (bind (ret_dconcat ?δ _) _) _ =>
      (* hnf to avoid unnecessary reductions *)
      let o := eval hnf in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* It is debatable in which order the two premises of the lemma [SIMP_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [SIMP (call v1 #x) φ]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [SIMP (call v1 #x) φ], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb SIMP_specs.

(* TODO may be unused *)
Ltac SIMP_call :=
  first [
    simple eapply SIMP_call; [ solve [encode] | solve [eauto with SIMP_specs] ]
  | simple eapply SIMP_covariant; [
      simple eapply SIMP_call; [ solve [encode] | eauto with SIMP_specs ]
    | cbn ]
  ].

Ltac SIMP_enter_and_abstract :=
  lazymatch goal with |- SIMP (call ?v _) _ =>
    (* First, expand [call] away. *)
    SIMP1_call_step;
    cbn zeta;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.
