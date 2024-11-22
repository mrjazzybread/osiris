From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval simplification.
From osiris.program_logic.pure Require Export wp judgements.

(** This file defines basic reasoning rules over [pure] judgements. *)

Section pure_rules.

  Context {A E : Type} {EncA : Encode A}.

  Implicit Type φ : A -> Prop.
  Implicit Type ψ : E -> Prop.

  (** *Basic properties about [returns]. *)

  (* [returns] is idempotent. *)

  Lemma returns_idem (ψ : A -> Prop):
    ∀ a : val, returns ψ a <-> returns (returns ψ) a.
  Proof.
    intros; split; intros (?&->&?).
    - by repeat econstructor.
    - destruct H as (?&->&?); by repeat econstructor.
  Qed.

  (* [returns] is monotone. *)

  Lemma returns_mono (φ ψ : A -> Prop):
    (forall a, φ a -> ψ a) ->
    ∀ a : val, returns φ a  -> returns ψ a.
  Proof.
    intros ? * (?&->&?); repeat econstructor; eauto.
  Qed.

  (** *Basic reasoning rules for [pure]. *)

  (* A reasoning rule for [ret]. *)

  (* The subgoal [v = #a] is explicitly isolated so as to make this lemma
    more widely applicable. A subgoal of the form [v = #a], where [a] is
    a Coq metavariable, can be solved by the tactic [encode]. *)

  Lemma pure_ret (φ : A → Prop) ψ v a :
    v = #a →
    φ a →
    pure (E := E) (ret v) φ ψ.
  Proof.
    intros; apply pure_wp_ret; esplit; eauto.
  Qed.

  (* A reasoning rule for ret that can instantiate the goal when it is an evar *)

  Lemma pure_ret_eq (a : A) ψ :
    pure (ret #a) (λ a', a' = a) ψ.
  Proof.
    intros; eapply pure_ret; eauto.
  Qed.


  Lemma pure_returns (a : val) (k : val -> micro val E) φ ψ:
    pure (k a) φ ψ ->
    returns (λ v : val, pure (k v) φ ψ) a.
  Proof.
    intros; eauto with pure.
  Qed.

  Lemma pure_throw φ ψ e :
    ψ e →
    pure (E := E) (throw e) φ ψ.
  Proof.
    intros; by apply pure_wp_throw.
  Qed.

  (* The consequence rule. *)

  Lemma pure_strong_mono m φ φ' ψ ψ' :
    pure m φ ψ →
    (∀ a, φ a → φ' a) →
    (∀ a, ψ a → ψ' a) →
    pure m φ' ψ'.
  Proof.
    intros; eapply pure_wp_mono; [ eauto | |]; firstorder.
  Qed.

  Lemma pure_mono m φ φ' ψ :
    pure m φ ψ →
    (∀ a, φ a → φ' a) →
    pure m φ' ψ.
  Proof.
    intros; eapply pure_strong_mono ; eauto.
  Qed.

  Lemma pure_exn_mono m φ ψ ψ':
    pure m φ ψ →
    (∀ a, ψ a → ψ' a) →
    pure m φ ψ'.
  Proof.
    intros; eapply pure_strong_mono ; eauto.
  Qed.

  Lemma pure_simp φ ψ m m' :
    simp m m' → pure m' φ ψ → pure m φ ψ.
  Proof.
    by eapply pure_wp_simp.
  Qed.

  (* A reasoning rule for [try2]. *)

  (* The rule is degenerate; [m] is not allowed to reduce to [throw _],
    so the handler [z] is dead and no proof obligation bears on it. *)

  Lemma pure_try2 {B E'} `{Encode B} (m : micro val _) (h : outcome2 val E' -> micro val E)
    φ (φ' : B -> _) ψ (ψ' : E' -> Prop):
    pure m φ' ψ' →
    (∀ a, φ' a → pure (continue h #a) φ ψ) →
    (∀ a, ψ' a → pure (discontinue h a) φ ψ) →
    pure (try2 m h) φ ψ.
  Proof.
    intros; eapply pure_wp_try2_conseq; eauto;
    simpl; intros v Hv; eauto with pure.
  Qed.

  (* A reasoning rule for [try]; corollary of [pure_try2] *)

  Corollary pure_try {B} `{Encode B} (m : micro val _) k z φ (φ' : B -> _)  ψ :
    pure m φ' ψ →
    (∀ a, φ' a → pure (k #a) φ ψ) →
    (∀ a, ψ a → pure (z a) φ ψ) →
    pure (try m k z) φ ψ.
  Proof.
    intros; eapply pure_try2; eauto.
  Qed.

  (* A reasoning rule for [bind]. *)

  (* This is [@bind val val]. Attempting to apply this lemma to [@bind A B]
    where [A] and [B] are types other than [val] will not work! *)

  Lemma pure_bind {B} `{Encode B} m k φ (φ' : B -> _) ψ :
    pure m φ' ψ →
    (∀ a, φ' a → pure (k #a) φ ψ) →
    pure (bind m k) φ ψ.
  Proof.
    rewrite bind_as_try.
    intros; eapply pure_try; intros; eauto with pure.
  Qed.

  Lemma pure_strong_bind {B} `{Encode B} m k φ (φ' : B -> _) ψ ψ' :
    pure m φ' ψ' →
    (∀ a, φ' a → pure (k #a) φ ψ) →
    (∀ a, ψ' a → ψ a) →
    pure (bind m k) φ ψ.
  Proof.
    rewrite bind_as_try.
    intros; eapply pure_try; intros; eauto with pure.
    eapply pure_wp_mono; eauto.
  Qed.

  Lemma pure_bind_unary m k (φ : A -> Prop) ψ :
    total m (λ (a : A), pure (k #a) φ ψ) →
    pure (bind m k) φ ψ.
  Proof.
    intros; eapply pure_strong_bind; eauto; done.
  Qed.

  (* A reasoning rule for [Par m1 m2 k z]. *)

  (* We cannot give a reasoning rule for [par m1 m2] because its type is
    [micro (val * val)], not [micro val]. However, we can give a rule
    for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

  Lemma pure_par `{Encode B} {X Y}
    m1 m2 k (φ1 : A → Prop) (φ2 : B → Prop) (φ : A * B → Prop)
    (ψ : X -> Prop) (ψ' : Y -> Prop) z :
    pure (E := X) m1 φ1 ψ →
    pure (E := X) m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → pure (k (#a1, #a2)) φ ψ') →
    (∀ e, ψ e → pure (z e) φ ψ') ->
    pure (E := Y) (Par m1 m2 (glue2 k z)) φ ψ'.
  Proof.
    intros Hm1 Hm2 Hentail1 Hentail2. rewrite <- try_par.
    eapply pure_wp_try_conseq; eauto.
    { eapply pure_wp_par with (φ := λ v, pure (k v) φ ψ');
        [ eauto | eauto |].
      simpl. intros v1 v2 ? ?. eauto with pure. }
    { intros v. tauto. }
  Qed.

  Lemma pure_par_cont `{Encode B} {X Y}
    m1 m2 k (φ1 : A → Prop) (φ2 : B → Prop) (φ : A * B → Prop)
    (ψ : X -> Prop) (ψ' : Y -> Prop):
    pure (E := X) m1 φ1 ψ →
    pure m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → pure (continue k (#a1, #a2)) φ ψ') →
    (forall e, ψ e -> pure (discontinue k e) φ ψ') ->
    pure (E := Y) (Par m1 m2 k) φ ψ'.
  Proof.
    intros. eapply pure_wp_Par_conseq; eauto; firstorder subst; eauto.
  Qed.

  (* Sequentializations of previous lemmas, considering the LHS first *)

  (* TODO: I do not seem to be able to use those, for example in pure_wp_eval.v's
  [pure_wp_eval_pair] *)

  Lemma pure_par_seq `{Encode B} {X} m1 m2 k (φ : A * B → Prop) ψ z
  :
    total (E := X) m1 (λ a1 : A,
      total m2 (λ a2 : B, pure (k (#a1, #a2)) φ ψ)) →
    pure (Par m1 m2 (glue2 k z)) φ ψ.
  Proof.
    intros Hm1.
    apply pure_wp_Par_vals_left.
    eapply (pure_wp_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
    eapply (pure_wp_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
    eauto.
  Qed.

  Lemma pure_par_seq_cont `{Encode B} {X} m1 m2 k (φ : A * B → Prop) ψ
  :
    total (E := X) m1 (λ a1 : A,
      total m2 (λ a2 : B, pure (continue k (#a1, #a2)) φ ψ)) →
    pure (Par m1 m2 k) φ ψ.
  Proof.
    intros Hm1.
    apply pure_wp_Par_vals_left.
    eapply (pure_wp_mono_ret _ Hm1). intros ? (a1 & -> & Hm2).
    eapply (pure_wp_mono_ret _ Hm2). intros ? (a2 & -> & Hk).
    eauto.
  Qed.

  (* A reasoning rule for [choose]. *)

  Lemma pure_choose m1 m2 (φ : A → Prop) (ψ : exn -> Prop) :
    pure m1 φ ψ →
    pure m2 φ ψ →
    pure (choose m1 m2) φ ψ.
  Proof.
    apply pure_wp_choose.
  Qed.

  (* This is the reciprocal bind rule for [pure_wp]. *)

  (* Because [pure_wp m ##_ ⊥] requires the result of [m] to lie in the image of the
    function [encode], and because this image cannot include every inhabitant
    of the type [val], we cannot expect that [pure_wp (bind m k) ##φ ⊥] implies
    [pure_wp m ##_ ⊥]. Thus, we can establish the reciprocal bind rule only under
    the side condition [pure_wp m ##(λ a, True) ⊥], which means that the result of
    the computation [m] lies in the image of the function [encode] at type
    [A]. *)

  Lemma invert_pure_bind `{Encode B} m k (φ : B → Prop) ψ :
    pure (bind m k) φ ψ →
    pure m (λ (a : A), True) ψ →
    pure m (λ (a : A), pure (k #a) φ ψ) ψ.
  Proof.
    intros Hmk%invert_pure_wp_bind Hm.
    pose proof pure_wp_binary_intersection _ Hmk Hm as I.
    eapply (pure_wp_mono _ I); firstorder subst; eauto.
  Qed.

  (* That said, if we take the type [A] to be [val], then -- because [encode]
    at type [val] is the identity function -- this side condition becomes
    trivial, and we can prove a version of the rule that does not have this
    side condition. *)

  Lemma invert_pure_bind_unary m k (φ : A → Prop) ψ:
    pure (bind m k) φ ψ →
    pure m (λ (v : val), pure (k v) φ ψ) ψ.
  Proof.
    intros Hmk%invert_pure_wp_bind.
    eapply pure_wp_mono; eauto; intros.
    eauto with pure.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Because the relation [pure_wp] is inductively defined, the [pure_wp] judgement
    implies that [m] terminates. This forms a Hoare logic of pure correctness
    for pure_wp computations. *)

  (* This file offers lemmas and tactics that help work with [pure_wp] goals.
    These lemmas and tactics form a simple "proof mode" for pure_wp
    computations. *)

  (* -------------------------------------------------------------------------- *)
  Lemma pure_prove_bind_bind `{Encode X} m (a : A)
    (f : A -> _) (g : val -> _) (φ : X -> Prop) ψ:
    pure ('c ← m;
          f c) (λ x, x = #a) ψ ->
    pure (g #a) φ ψ ->
    pure ('v1 ← m;
          'v2 ← f v1;
          g v2) φ ψ.
  Proof.
    intros Hfm Hga.
    apply invert_pure_wp_bind in Hfm.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros a' Ha'.
    eapply pure_wp_bind_conseq; eauto.
    by intros _v (_a & -> & ->).
  Qed.

  Lemma pure_bind_bind `{Encode E} (m : micro val _) f g φ ψ :
    pure ('x ← m; f x) φ ψ ->
    (forall y, φ y -> pure (g #y) φ ψ) ->
    pure ('v1 ← m;
          v2 ← f v1;
          g v2) φ ψ.
  Proof.
    intros Hm Hga.
    apply invert_pure_wp_bind in Hm.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros v Hv.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros _ (y & -> & Hy).
    apply Hga, Hy.
  Qed.

End pure_rules.

Section pure_rules_variant.

  (* When a [val] is returned, there is no need for [encode]. FIXME *)
  Lemma pure_ret_val `{Encode A} {E} (a : val) (ϕ : A -> Prop) ψ :
    returns ϕ a ->
    pure (E := E) (ret a) ϕ ψ.
  Proof.
    intros. returns_eauto. by eapply pure_ret.
  Qed.

  Lemma pure_ret_eq_val {E} {A} `{EncA: Encode A} (a : A) ψ :
    pure (E := E) (ret #a) (λ a', a' = a) ψ.
  Proof.
    intros; eapply pure_ret; eauto.
  Qed.

  Lemma pure_ret_eq_val' {E} {A} `{EncA: Encode A} (a : A) ψ :
    pure (E := E) (ret #a) (λ a' : val, a' = # a) ψ.
  Proof.
    intros; eapply pure_ret; eauto.
  Qed.

End pure_rules_variant.


(* Rules about [pure] related to effectful computations, i.e. computations
   using [Stop] *)
Section pure_eff.

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

  Lemma pure_stop_eval {Y} `{Encode X} η e k (φ : X -> Prop) ψ :
    pure (try2 (eval η e) k) φ ψ ->
    pure (E := Y) (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros.
    eapply pure_wp_simp; [ apply simplification.SimpEval | assumption ].
  Qed.

  (** [CEval] evaluation *)

  Lemma pure_CEval `{Encode A} {E η e k} (φ : A → Prop) (ψ : E → Prop) :
    pure (try2 (eval η e) k) φ ψ →
    pure (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros. eapply pure_wp_det_may_backward; eauto. repeat constructor.
    by intros m' ->%pure.invert_may_eval.
  Qed.

  Lemma pure_CEval_inject2 `{Encode A} {η e φ ψ} :
    pure (A := A) (eval η e) φ ψ →
    pure (Stop CEval (η, e) inject2) φ ψ.
  Proof.
    intros He. eapply pure_CEval, pure_try2; try done;
    eauto using pure_ret, pure_throw.
  Qed.

  Lemma pure_enter_call_VCloRec `{Encode Y} η rbs g x e v2 (φ : Y → Prop) ψ :
    lookup_rec_bindings rbs g = ret (AnonFun x e) ->
    pure (eval ((x, v2) :: eval_rec_bindings η rbs ++ η) e) φ ψ ->
    pure (call (VCloRec η rbs g) v2) φ ψ.
  Proof.
    intros Hlookup Hpure.
    simpl; rewrite Hlookup.
    cbn.
    eapply pure_CEval; rewrite try2_ret_right.
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

  (** Compatibility with [widen] *)

  Lemma pure_widen `{Encode A} {E} (m : micro val void) φ ψ :
    pure m φ ⊥ → @pure A val _ E (widen m) φ ψ.
  Proof.
    unfold widen.
    intros P. eapply pure_try2. eapply P.
    - intros. cbn. eapply pure_ret; done.
    - by intros.
  Qed.

End pure_eff.
