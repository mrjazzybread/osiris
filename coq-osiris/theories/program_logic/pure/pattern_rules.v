From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar locations.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Import pure_rules.

Open Scope Z_scope.

(* This file defines judgements for Hoare-style reasoning on
   the auxiliary functions in [semantics/eval.v]. *)

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

(* The judgement [pattern η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition cpattern_wp η p o (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (cextend η p o) φ (λ (_ : unit), ψ).

Definition pattern_wp η p v (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extend η p v) φ (λ (_ : unit), ψ).

Definition patterns_wp η ps vs (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extends η ps vs) φ (λ (_ : unit), ψ).

(* -------------------------------------------------------------------------- *)

(* cpattern_wp : env → cpat → outcome.outcome3 val locations.loc val val → (env → Prop) → Prop → Prop *)
(* pattern_wp : env → pat → val → (env → Prop) → Prop → Prop *)
(* patterns_wp : env → list pat → list val → (env → Prop) → Prop → Prop *)

(* Class pattern_wp_template := *)
(*   { pattern_wp_shape : Type; pattern_wp_outcome : Type }. *)

(* Class pat {P : pattern_wp_template} := *)
(*   pat_ : env -> pattern_wp_shape -> pattern_wp_outcome -> (env -> Prop) -> Prop -> Prop. *)

(* -------------------------------------------------------------------------- *)

Section pattern_wp_rules.

  Implicit Type φ : env -> Prop.
  Implicit Type ψ : Prop.

  (* Monotonicity properties for [cpattern_wp], [pattern_wp], and [patterns_wp]. *)

  Lemma cpattern_wp_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    cpattern_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    cpattern_wp η p v φ' ψ'.
  Proof.
    unfold cpattern_wp; eauto using pure_wp_mono.
  Qed.

  Lemma cpattern_wp_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    cpattern_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    cpattern_wp η p v φ' ψ.
  Proof. intros; by eapply cpattern_wp_mono. Qed.

  Lemma cpattern_wp_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    cpattern_wp η p v φ ψ →
    (ψ → ψ') →
    cpattern_wp η p v φ ψ'.
  Proof. intros; by eapply cpattern_wp_mono. Qed.

  Lemma pattern_wp_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    pattern_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    pattern_wp η p v φ' ψ'.
  Proof.
    unfold pattern_wp; eauto using pure_wp_mono.
  Qed.

  Lemma pattern_wp_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    pattern_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    pattern_wp η p v φ' ψ.
  Proof. intros; by eapply pattern_wp_mono. Qed.

  Lemma pattern_wp_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    pattern_wp η p v φ ψ →
    (ψ → ψ') →
    pattern_wp η p v φ ψ'.
  Proof. intros; by eapply pattern_wp_mono. Qed.

  Lemma patterns_wp_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    patterns_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    patterns_wp η p v φ' ψ'.
  Proof.
    unfold patterns_wp; eauto using pure_wp_mono.
  Qed.

  Lemma patterns_wp_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    patterns_wp η p v φ ψ →
    (∀ η, φ η → φ' η) →
    patterns_wp η p v φ' ψ.
  Proof. intros; by eapply patterns_wp_mono. Qed.

  Lemma patterns_wp_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    patterns_wp η p v φ ψ →
    (ψ → ψ') →
    patterns_wp η p v φ ψ'.
  Proof. intros; by eapply patterns_wp_mono. Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the judgement [pattern_wp]. *)

  (* From an operational point of view, the repeated application of these
    lemmas to a pattern_wp [p] and a value [v] have the effect of translating
    the pattern_wp matching operation [p = v] into a positive formula and a
    negative formula. The positive formula, the postcondition [φ],
    accumulates a sequence of universal quantifiers and equations that
    describe what is learnt when pattern_wp matching succeeds. The negative
    formula, the failure postcondition [ψ], describes what is learnt when
    pattern_wp matching fails. *)

  (* When a pattern_wp cannot fail or can fail due to several distinct causes,
    a naive statement of its reasoning rule would have one occurrence of
    [ψ] in its conclusion and no occurrence or multiple occurrences of [ψ]
    in its premises. From an operational point of view, this is
    undesirable, because [ψ] is then unconstrained or duplicated. We avoid
    this phenomenon by using [False] or a disjunction in the conclusion of
    the reasoning rule. Thus, from an operational point of view, applying
    the reasoning rule instantiates the failure postcondition with a
    logical connective. *)

  Lemma pat_PAny η v φ :
    φ η →
    pattern_wp η PAny v φ False.
  Proof.
    unfold pattern_wp. simpl_extend. eauto using pure_wp_ret.
  Qed.

  Lemma pat_PVar η x v φ :
    φ ((x, v) :: η) →
    pattern_wp η (PVar x) v φ False.
  Proof.
    unfold pattern_wp. simpl_extend. eauto using pure_wp_ret.
  Qed.

  (* Given a goal of the form [pattern_wp η (PVar x) v ?φ False],
    applying the lemma [pat_PVar2] solves the goal and
    instantiates the postcondition [?φ]. *)

  Lemma pat_PVar2 η x v :
    pattern_wp η (PVar x) v (λ η', η' = (x, v) :: η) False.
  Proof.
    by apply pat_PVar.
  Qed.

  Ltac pat_PVar :=
    match goal with
    | |- pattern_wp _ (PVar _) _ _ _ =>
        (apply pat_PVar2 || eapply pat_PVar)
    end.

  Lemma pat_PAlias η p x v φ ψ :
    pattern_wp η p v (λ η, φ ((x, v) :: η)) ψ →
    pattern_wp η (PAlias p x) v φ ψ.
  Proof.
    unfold pattern_wp. simpl_extend; intros.
    apply pure_wp_bind.
    eauto using pure_wp_mono, pure_wp_ret.
  Qed.

  (* TODO generalize to [(φ1 η → pattern_wp η p2 v φ ψ2)] and see if it is useful *)
  Lemma pat_POr η p1 p2 v φ ψ1 ψ2 :
    pattern_wp η p1 v φ ψ1 →
    pattern_wp η p2 v φ ψ2 →
    pattern_wp η (POr p1 p2) v φ (ψ1 ∧ ψ2).
      (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
        disjunction pattern_wp to fail, both sides must fail. *)
  Proof.
    unfold pattern_wp. simpl_extend; intros.
    eauto using pure_wp_orelse, pure_wp_mono.
  Qed.

  Lemma pat_PUnit η v φ :
    φ η →
    v = #() →
    pattern_wp η PUnit v φ False.
  Proof.
    unfold pattern_wp. intros ? ->; simpl_extend.
    eauto using pure_wp_ret.
  Qed.

  Lemma pat_PTuple `{Encode A} η ps (a : A) vs φ ψ :
    #a = VTuple vs ->
    patterns_wp η ps vs φ ψ →
    pattern_wp η (PTuple ps) #a φ ψ.
  Proof.
    unfold patterns_wp, pattern_wp.
    intros ->. by simpl_extend.
  Qed.

  Lemma pat_PTuple_val η ps vs φ ψ :
    patterns_wp η ps vs φ ψ ->
    pattern_wp η (PTuple ps) (VTuple vs) φ ψ.
  Proof.
    unfold pattern_wp. by simpl_extend.
  Qed.

  Lemma pat_PPair `{Encode A, Encode B} η p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
    v1 = #x1 ->
    v2 = #x2 ->
    pattern_wp η p1 #x1 (λ η', pattern_wp η' p2 #x2 φ (ψ2)) (ψ1) ->
    pattern_wp η (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
  Proof.
    intros; subst.
    unfold pattern_wp. simpl_extend.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    simpl; intros. rewrite bind_ret_right.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    auto using pure_wp_ret.
  Qed.

  Lemma pat_PData_nil η c c' φ ψ :
    (c = c' -> φ η) ->
    pattern_wp η (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern_wp; intros. simpl_extend.
    destruct_string_eqb;
      eauto using pure_wp_throw, pure_wp_mono, pure_wp_ret.
  Qed.

  Lemma pat_PData η c c' p v φ ψ :
    (c = c' -> patterns_wp η p v φ ψ) ->
    pattern_wp η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern_wp; intros. simpl_extend.
    destruct_string_eqb; eauto using pure_wp_throw.
    eapply pure_wp_mono; first apply H; eauto.
  Qed.

  Lemma pat_PData_eq η c p v φ ψ :
    patterns_wp η p v φ ψ →
    pattern_wp η (PData c p) (VData c v) φ ψ.
      (* This form is useful when [c = c'] is statically known. *)
  Proof.
    unfold pattern_wp; intros. simpl_extend.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PData_neq η c p c' v φ :
    c ≠ c' →
    pattern_wp η (PData c p) (VData c' v) φ True.
      (* This form is useful when [c ≠ c'] is statically known. *)
  Proof.
    unfold pattern_wp; intros. simpl_extend.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PXData_eq η c p c' v φ ψ :
    lookup_path η c = ret (VLoc c') ->
    patterns_wp η p v φ ψ →
    pattern_wp η (PXData c p) (VXData c' v) φ ψ.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern_wp; intros Hlookup Hpat.
    simpl_extend; rewrite Hlookup. cbn; rewrite bind_ret.
    unfold locations.eqb; destruct c'; cbn.
    by rewrite Z.eqb_refl.
  Qed.

  Lemma pat_PXData_neq η π p l1 l2 v φ :
    lookup_path η π = ret (VLoc l1) ->
    (address l1 <> address l2) ->
    pattern_wp η (PXData π p) (VXData l2 v) φ True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern_wp; intros Hlookup Heq; simpl_extend.
    rewrite Hlookup. cbn; rewrite bind_ret.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    replace (address0 =? address) with false;
      last by apply eq_sym; apply Z.eqb_neq.
    by apply pure_wp_throw.
  Qed.

  Lemma pat_PXData_neq' η π p l1 l2 v :
    lookup_path η π = ret (VLoc l1) ->
    (address l1 <> address l2) ->
    pattern_wp η (PXData π p) (VXData l2 v) (λ _, False) True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern_wp; intros Hlookup Heq; simpl_extend.
    rewrite Hlookup. cbn; rewrite bind_ret.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    replace (address0 =? address) with false;
      last by apply eq_sym; apply Z.eqb_neq.
    by apply pure_wp_throw.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the auxiliary judgement [patterns_wp]. *)

  Lemma pats_PNil η φ :
    φ η →
    patterns_wp η [] [] φ False.
  Proof.
    unfold patterns_wp.
    simpl_extends.
    eauto using pure_wp_ret.
  Qed.

  Lemma pats_PCons_unary η p ps v vs φ ψ1 ψ2 :
    pattern_wp η p v (λ η, patterns_wp η ps vs φ ψ2) ψ1 →
    patterns_wp η (p :: ps) (v :: vs) φ (ψ1 \/ ψ2).
  Proof.
    unfold patterns_wp, patterns_wp. intros Hp; simpl_extends.
    eapply pure_wp_bind_conseq.
    { eapply pure_wp_mono.
      - eassumption.
      - simpl; intros. eapply pure_wp_mono; eauto.
      - tauto. }
    simpl; intros. rewrite bind_ret_right.
    eapply pure_wp_mono; eauto.
  Qed.

  Lemma pats_PCons_unary_false η p ps v vs φ :
    pattern_wp η p v (λ η, patterns_wp η ps vs φ False) False ->
    patterns_wp η (p :: ps) (v :: vs) φ False.
  Proof.
    intros.
    assert (False \/ False -> False) as HFalse by tauto.
    eapply patterns_wp_exn_mono; [ clear HFalse | exact HFalse ].
    by apply pats_PCons_unary.
  Qed.

  Lemma pats_PCons η p ps v vs φ' φ ψ1 ψ2 :
    pattern_wp η p v φ' ψ1 →
    (∀ η, φ' η → patterns_wp η ps vs φ ψ2) →
    patterns_wp η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
  Proof.
    intros. eapply pats_PCons_unary.
    eapply pattern_wp_mono; eauto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Local Ltac pats :=
    repeat first [
        eapply pats_PNil; [ eauto ]
      | eapply pats_PCons; [ eauto | simpl; intros ]
      ].

  (* -------------------------------------------------------------------------- *)

  Lemma pat_PConst η c c' φ :
    (c = c' -> φ η) ->
    pattern_wp η (PConstant c) (VConstant c') φ (c <> c').
  Proof.
    intros Hφ.
    eapply pattern_wp_mono.
    { eapply pat_PData.
      intros Hc; specialize (Hφ Hc).
      pats. }
    { tauto. }
    { tauto. }
  Qed.

  Lemma pat_PConst_eq η c φ :
    φ η ->
    pattern_wp η (PConstant c) (VConstant c) φ False.
  Proof.
    intros Hφ.
    eapply pattern_wp_exn_mono; [ eapply pat_PConst; eauto | tauto ].
  Qed.

  Lemma pat_PConst_neq η c c' e ψ :
    c <> c' ->
    ψ ->
    pattern_wp η (PConstant c) (VData c' e) (λ _, False) ψ.
  Proof.
    intros Hneq Hψ.
    unfold pattern_wp. simpl_extend.
    apply String.eqb_neq in Hneq as ->.
    by apply pure_wp_throw.
  Qed.

  Lemma pat_false η v (P : Prop) φ :
    v = #P →
    (¬P → φ η) →
    pattern_wp η (PConstant "false") v φ P.
  Proof.
    intros -> ?; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_wp_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_true_elim].
      done. }

    { eapply pattern_wp_exn_mono.
      eapply pat_PConst_eq;
        auto using truth_false_elim.
      tauto. }
  Qed.

  Lemma pat_true η v (P : Prop) φ :
    v = #P →
    (P → φ η) →
    pattern_wp η (PConstant "true") v φ (¬P).
  Proof.
    intros -> Hφ; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_wp_exn_mono.
      eapply pat_PConst_eq;
        apply Hφ; by apply truth_true_elim.
      tauto. }

    { eapply pattern_wp_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_false_elim].
      intros; tauto. }
  Qed.

  Lemma pat_PInt η v (i j : Z) (φ : env → Prop) :
    int.representable i →
    int.representable j →
    v = #j →
    (i = j → φ η) →
    pattern_wp η (PInt i) v φ (i <> j).
  Proof.
    intros Hi Hj -> Hφ.
    unfold pattern_wp; simpl_extend.
    rewrite int.eq_repr_repr; auto.
    destruct (_ =? _) eqn:E.
    - apply pure_wp_ret. apply Hφ. by apply Z.eqb_eq.
    - apply pure_wp_throw. by apply Z.eqb_neq.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma cpat_CVal η p v φ ψ :
    pattern_wp η p v φ ψ ->
    cpattern_wp η (CVal p) (O2Ret v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_CExc η p v φ ψ :
    pattern_wp η p v φ ψ ->
    cpattern_wp η (CExc p) (O2Throw v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_COr η cp1 cp2 o φ ψ1 ψ2 :
    cpattern_wp η cp1 o φ ψ1 ->
    cpattern_wp η cp2 o φ ψ2 ->
    cpattern_wp η (COr cp1 cp2) o φ (ψ1 /\ ψ2).
  Proof.
    unfold cpattern_wp. intros.
    eapply pure_wp_orelse; [ eassumption | ].
    eauto using pure_wp_mono.
  Qed.

  Lemma cpat_CEff η peff pk v k φ ψ1 ψ2 :
    pattern_wp η peff v (λ δ, pattern_wp δ pk (VCont k) φ ψ2) ψ1 ->
    cpattern_wp η (CEff peff pk) (O3Perform v k) φ (ψ1 \/ ψ2).
  Proof.
    unfold cpattern_wp, pattern_wp; intros. simpl.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    simpl; intros δ ?.
    eauto using pure_wp_mono.
  Qed.

  Fixpoint valid_cpattern_wp_match {A E} cp (o : outcome3 A E) :=
    match cp, o with
    | CVal _, O3Ret _
    | CExc _, O3Throw _
    | CEff _ _, O3Perform _ _ =>
        true
    | COr cp1 cp2, _ =>
        valid_cpattern_wp_match cp1 o || valid_cpattern_wp_match cp2 o
    | _, _ =>
        false
    end.

  Lemma invert_valid_match cp o :
    valid_cpattern_wp_match cp o = false ->
    ∀ η, cextend η cp o = throw ().
  Proof.
    intros Hvalid η.
    induction cp; destruct o; simpl in *; try congruence;
      (* Only the [COr cp1 cp2] case remains. *)
      unfold orelse;
      apply orb_false_elim in Hvalid as [H1 H2];
      apply IHcp1 in H1; apply IHcp2 in H2;
      by rewrite H1, H2, !try_throw.
  Qed.

  Lemma cpat_mismatch η cp o φ (ψ : Prop) :
    valid_cpattern_wp_match cp o = false ->
    ψ ->
    cpattern_wp η cp o φ ψ.
  Proof.
    intros.
    unfold cpattern_wp.
    rewrite invert_valid_match by assumption.
    by apply pure_wp_throw.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning for data *)

  (* The following reasoning rules exemplify a general approach for matching
    against algebraic data types. *)

  Lemma pat_pNil `{Encode A} η v (xs : list A) φ :
    v = #xs →
    (xs = [] -> φ η) →
    (* Enter the branch with knowledge that [xs] is empty *)
    pattern_wp η pNil v φ (xs ≠ []).
    (* If the match is unsuccessful, move to the next branch
      with the knowledge that [xs] is not empty *)
  Proof.
    intros; subst.
    destruct xs; eapply pattern_wp_exn_mono.
    { eapply pat_PConst; eauto. }
    { tauto. }
    { eapply pat_PData_neq; done. }
    { congruence. }
  Qed.

  (* [pat_pCons_cut] exists for pedagogical purposes.
    We use [pat_pCons] in practice to avoid headaches caused
    by evar instantiation scopes. *)

  Lemma pat_pCons_cut `{Encode A} v xs η p1 p2 φ (φ1 : A -> env -> Prop)
    (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern_wp η p1 #x (φ1 x) (ψ1 x)) ->
        (* If [#x] matches [p1], we gain the knowledge [φ1 x η0].
          Otherwise, we gain the knowledge [ψ1 x] *)
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        (forall η', φ1 x η' -> pattern_wp η' p2 #xs' φ (ψ2 xs'))) ->
        (* If [#xs'] does not match [p2], then we gain the knowledge [ψ2 xs'] *)
    pattern_wp η (pCons p1 p2) v φ (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
    (* There are three ways the match can be unsuccessful:
      - the list is empty
      - the list is non-empty, but its head did not match [p1]
      - the list is non-empty, but its tail did not match [p2] *)
  Proof.
    intros; subst.
    destruct xs.
    { eapply pattern_wp_exn_mono.
      { by apply pat_PData_neq. }
      tauto. }
    { eapply pattern_wp_exn_mono.
      { eapply pat_PData_eq; pats.  }
      right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  Lemma pat_pCons `{Encode A} v xs η p1 p2 φ
    (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern_wp η p1 #x
          (λ η',
            pattern_wp η' p2 #xs' φ (ψ2 xs'))
          (ψ1 x)) ->
    pattern_wp η (pCons p1 p2) v φ
      (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
  Proof.
    intros; subst.
    destruct xs; eapply pattern_wp_exn_mono.
    { by apply pat_PData_neq. }
    { tauto. }
    { eapply pat_PData_eq; pats. }
    { clear; right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  Local Ltac pat_pNil :=
    eapply pat_pNil; first solve [ encode ].

  Local Ltac pat_pCons :=
    eapply pat_pCons; first solve [ encode ].

  (* The previous lemmas start to give us a general scheme for reasoning about
    pattern_wp matching on ADTs.

    More experimenting is required.
    As of now (29/02/24), see [examples/splay.v] for more examples. *)

  (* Pattern_Wp proofmode tactics *)


  Definition is_not_O3Throw {A X} (o : outcome3 A X) :=
    match o with
    | O3Throw _ => False
    | _ => True
    end.

  Definition is_not_O3Ret {A X} (o : outcome3 A X) :=
    match o with
    | O3Ret _ => False
    | _ => True
    end.

  Definition is_not_O3Perform {A X} (o : outcome3 A X) :=
    match o with
    | O3Perform _ _ => False
    | _ => True
    end.

  Lemma cpat_CExc_abst η p o φ ψ :
    (forall e, o = O3Throw e -> pattern_wp η p e φ ψ) ->
    cpattern_wp η (CExc p) o φ (is_not_O3Throw o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern_wp.
    destruct o; simpl.
    - apply pure_wp_throw. by left.
    - eapply pure_wp_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - apply pure_wp_throw. by left.
  Qed.

  Lemma cpat_CVal_abst η p o φ ψ :
    (forall v, o = O3Ret v -> pattern_wp η p v φ ψ) ->
    cpattern_wp η (CVal p) o φ (is_not_O3Ret o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern_wp.
    destruct o; simpl.
    - eapply pure_wp_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - apply pure_wp_throw. by left.
    - apply pure_wp_throw. by left.
  Qed.

  Lemma cpat_CEff_abst η peff pk o φ ψ1 ψ2 :
    (forall eff k,
        o = O3Perform eff k ->
        pattern_wp η peff eff (λ δ, pattern_wp δ pk (VCont k) φ ψ2) ψ1) ->
    cpattern_wp η (CEff peff pk) o φ (is_not_O3Perform o ∨ ψ1 ∨ ψ2).
  Proof.
    intros Hpat.
    unfold cpattern_wp.
    destruct o; simpl.
    - apply pure_wp_throw. by left.
    - apply pure_wp_throw. by left.
    - eapply pure_wp_bind.
      eapply pure_wp_mono; [ apply Hpat; reflexivity | | auto ].
      intros δ Hpat2.
      eapply pure_wp_mono; [ apply Hpat2 | auto | auto ].
  Qed.

  Lemma cpat_CEff_impossible η peff pk (o : outcome2 val exn) φ :
    cpattern_wp η (CEff peff pk) o φ True.
  Proof.
    unfold cpattern_wp.
    destruct o; simpl; by apply pure_wp_throw.
  Qed.

End pattern_wp_rules.

Create HintDb pat.

#[global] Hint Immediate pat_PAny pat_PVar pat_PVar2 pat_PAlias pat_POr pat_PUnit pat_PTuple pat_PTuple_val pat_PPair pat_PData pat_PData_eq pat_PData_neq pat_PXData_eq pat_PXData_neq pat_PXData_neq' pats_PNil pats_PCons_unary pats_PCons_unary_false pats_PCons pat_PConst pat_PConst_eq pat_PConst_neq pat_false pat_true pat_PInt cpat_CVal cpat_CExc cpat_COr cpat_CEff pat_pNil pat_pCons pat_pCons_cut : pat.

Section pattern_constructors.

Implicit Type φ : env -> Prop.
Implicit Type ψ : Prop.

Inductive pattern : env -> pat -> val -> (env -> Prop) -> Prop -> Prop :=
  | pattern_PAny φ η v :
      φ η →
      pattern η PAny v φ False
  | pattern_PVar x φ η v :
      φ ((x, v) :: η) →
      pattern η (PVar x) v φ False
  | pattern_PVar2 x η v :
      pattern η (PVar x) v (λ η', η' = (x, v) :: η) False
  | pattern_PAlias p x φ ψ η v :
      pattern η p v (λ η', φ ((x, v) :: η')) ψ →
      pattern η (PAlias p x) v φ ψ
  | pattern_POr p1 p2 φ ψ1 ψ2 η v :
      pattern η p1 v φ ψ1 →
      pattern η p2 v φ ψ2 →
      pattern η (POr p1 p2) v φ (ψ1 ∧ ψ2)
  | pattern_PUnit η v φ :
      φ η →
      v = #() →
      pattern η PUnit v φ False
  | pattern_PTuple {A} `{Encode A} ps vs φ ψ η (a : A) :
      #a = VTuple vs →
      patterns_wp η ps vs φ ψ →
      pattern η (PTuple ps) #a φ ψ
  | pattern_PTuple_val ps vs φ ψ η :
      patterns_wp η ps vs φ ψ →
      pattern η (PTuple ps) (VTuple vs) φ ψ
  | pattern_PPair
      `{Encode A, Encode B}
      p1 p2 ψ1 ψ2 φ φ' η v1 v2
      (x1 : A) (x2 : B) :
      v1 = #x1 →
      v2 = #x2 →
      (forall η', φ' η' -> pattern η' p2 #x2 φ ψ2) ->
      pattern η p1 #x1 φ' ψ1 →
      pattern η (PPair p1 p2) (VPair v1 v2) φ (ψ1 ∨ ψ2)
  | pattern_PData_eq c p v φ ψ η :
      patterns_wp η p v φ ψ →
      pattern η (PData c p) (VData c v) φ ψ
  | pattern_PData_neq c p c' v φ η ψ:
      c ≠ c' →
      ψ ->
      pattern η (PData c p) (VData c' v) φ ψ
  | pattern_PData c p c' v φ ψ η :
      (c = c' → patterns_wp η p v φ ψ) →
      pattern η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c')
  | pattern_PXData_eq π p (c c' : loc) v φ ψ η :
      lookup_path η π = ret (VLoc c') →
      patterns_wp η p v φ ψ →
      pattern η (PXData π p) (VXData c' v) φ ψ
  | pattern_PXData_neq π p l1 l2 v φ η ψ:
      lookup_path η π = ret (VLoc l1) →
      (address l1 ≠ address l2) →
      ψ ->
      pattern η (PXData π p) (VXData l2 v) φ ψ
  | pattern_PXData_neq' π p l1 l2 v η ψ:
      lookup_path η π = ret (VLoc l1) →
      (address l1 ≠ address l2) →
      ψ ->
      pattern η (PXData π p) (VXData l2 v) (λ _, False) ψ
  | pattern_Base φ p η v ψ:
      pattern_wp η p v φ ψ ->
      pattern η p v φ ψ.

Lemma pattern_equals_pat p η v φ ψ:
  pattern η p v φ ψ <->
  pattern_wp η p v φ ψ.
Proof.
  intros; split; [ | by constructor ].
  intros; induction H; eauto with pat.
  eapply pat_PPair; eauto.
  eapply pattern_wp_mono; eauto.
  all: eapply pattern_wp_mono; eauto with pat.
  firstorder.
Qed.

Inductive cpattern : env -> cpat -> outcome.outcome3 val loc val val -> (env -> Prop) -> Prop -> Prop :=
  | cpattern_CVal p v φ ψ η :
      pattern η p v φ ψ →
      cpattern η (CVal p) (O2Ret v) φ ψ
  | cpattern_CExc p v φ ψ η :
      pattern η p v φ ψ →
      cpattern η (CExc p) (O2Throw v) φ ψ
  | cpattern_COr cp1 cp2 o φ ψ1 ψ2 η :
      cpattern η cp1 o φ ψ1 →
      cpattern η cp2 o φ ψ2 →
      cpattern η (COr cp1 cp2) o φ (ψ1 ∧ ψ2)
  | cpattern_CEff peff pk v k φ ψ1 ψ2 η :
      pattern η peff v (λ δ, pattern δ pk (VCont k) φ ψ2) ψ1 →
      cpattern η (CEff peff pk) (O3Perform v k) φ (ψ1 ∨ ψ2)
  | cpattern_Base φ p η v ψ:
      cpattern_wp η p v φ ψ ->
      cpattern η p v φ ψ.

Lemma cpattern_equals_cpat p η v φ ψ:
  cpattern η p v φ ψ <->
  cpattern_wp η p v φ ψ.
Proof.
  intros; split; [ | by constructor ].
  intros; induction H; try apply pattern_equals_pat; eauto with pat.
  apply cpat_CEff; eapply pattern_wp_mono; eauto.
  by apply pattern_equals_pat.
  intros; by apply pattern_equals_pat.
Qed.

Inductive patterns : env -> list pat -> list val -> (env -> Prop) -> Prop -> Prop :=
  | patterns_PNil φ ψ η :
      φ η →
      (ψ -> False) ->
      patterns η [] [] φ ψ
  | patterns_PCons_unary_or p ps v vs φ φ' ψ1 ψ2 η :
      (forall η', φ' η' -> patterns η' ps vs φ ψ2) ->
      pattern η p v φ' ψ1 →
      patterns η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2)
  | patterns_PCons_unary_false p ps v vs φ φ' η :
      (forall η', φ' η' -> patterns η' ps vs φ False) ->
      pattern η p v φ' False →
      patterns η (p :: ps) (v :: vs) φ False
  | patterns_PCons p ps v vs φ' φ ψ1 ψ2 η :
      pattern η p v φ' ψ1 →
      (∀ η', φ' η' → patterns η' ps vs φ ψ2) →
      patterns η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2)
  | patterns_Base φ p η v ψ:
      patterns_wp η p v φ ψ ->
      patterns η p v φ ψ.

Lemma patterns_equals_pats p η v φ ψ:
  patterns η p v φ ψ <->
  patterns_wp η p v φ ψ.
Proof.
  intros; split; [ | by constructor ].
  intros; induction H; eauto with pat.
  - eapply patterns_wp_mono. apply pats_PNil. all: eauto. intros; done.
  - eapply pats_PCons; first by apply pattern_equals_pat; intros; eauto.
    intros; auto.
  - eapply pats_PCons_unary_false.
    eapply pattern_wp_mono; eauto.
    by apply pattern_equals_pat.
  - eapply pats_PCons.
    by apply pattern_equals_pat.
    intros; auto.
Qed.

End pattern_constructors.

Global Hint Resolve pattern_PAny pattern_PVar pattern_PVar2 pattern_PAlias pattern_POr pattern_PUnit pattern_PTuple pattern_PTuple_val pattern_PPair pattern_PData pattern_PData_eq pattern_PData_neq : pat.
Global Hint Resolve cpattern_CVal cpattern_CExc cpattern_COr cpattern_CEff : pat.
Global Hint Resolve patterns_PNil patterns_PCons_unary_or patterns_PCons_unary_false patterns_PCons : pat.


#[global]
  Hint Extern 2 (patterns_wp _ _ _ _ _) => apply patterns_equals_pats; eauto with pat: pat.
#[global]
  Hint Extern 2 (pattern _ _ _ _ _) => econstructor; eauto : pat.

Ltac solve_pattern := by eauto with pat.
