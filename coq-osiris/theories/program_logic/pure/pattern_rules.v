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

Definition cpattern η p o (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (cextend η p o) φ (λ (_ : unit), ψ).

Definition pattern η p v (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extend η p v) φ (λ (_ : unit), ψ).

Definition patterns η ps vs (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extends η ps vs) φ (λ (_ : unit), ψ).

(* -------------------------------------------------------------------------- *)

(* cpattern : env → cpat → outcome.outcome3 val locations.loc val val → (env → Prop) → Prop → Prop *)
(* pattern : env → pat → val → (env → Prop) → Prop → Prop *)
(* patterns : env → list pat → list val → (env → Prop) → Prop → Prop *)

(* Class pattern_template := *)
(*   { pattern_shape : Type; pattern_outcome : Type }. *)

(* Class pat {P : pattern_template} := *)
(*   pat_ : env -> pattern_shape -> pattern_outcome -> (env -> Prop) -> Prop -> Prop. *)

(* -------------------------------------------------------------------------- *)

Section pattern_rules.

  Implicit Type φ : env -> Prop.
  Implicit Type ψ : Prop.

  (* Monotonicity properties for [cpattern], [pattern], and [patterns]. *)

  Lemma cpattern_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    cpattern η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    cpattern η p v φ' ψ'.
  Proof.
    unfold cpattern; eauto using pure_wp_mono.
  Qed.

  Lemma cpattern_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    cpattern η p v φ ψ →
    (∀ η, φ η → φ' η) →
    cpattern η p v φ' ψ.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma cpattern_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    cpattern η p v φ ψ →
    (ψ → ψ') →
    cpattern η p v φ ψ'.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma pattern_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    pattern η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    pattern η p v φ' ψ'.
  Proof.
    unfold pattern; eauto using pure_wp_mono.
  Qed.

  Lemma pattern_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    pattern η p v φ ψ →
    (∀ η, φ η → φ' η) →
    pattern η p v φ' ψ.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma pattern_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    pattern η p v φ ψ →
    (ψ → ψ') →
    pattern η p v φ ψ'.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma patterns_mono η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    patterns η p v φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    patterns η p v φ' ψ'.
  Proof.
    unfold patterns; eauto using pure_wp_mono.
  Qed.

  Lemma patterns_env_mono η p v (φ φ' : env -> Prop) (ψ : Prop) :
    patterns η p v φ ψ →
    (∀ η, φ η → φ' η) →
    patterns η p v φ' ψ.
  Proof. intros; by eapply patterns_mono. Qed.

  Lemma patterns_exn_mono η p v (φ : env -> Prop) (ψ ψ': Prop) :
    patterns η p v φ ψ →
    (ψ → ψ') →
    patterns η p v φ ψ'.
  Proof. intros; by eapply patterns_mono. Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the judgement [pattern]. *)

  (* From an operational point of view, the repeated application of these
    lemmas to a pattern [p] and a value [v] have the effect of translating
    the pattern matching operation [p = v] into a positive formula and a
    negative formula. The positive formula, the postcondition [φ],
    accumulates a sequence of universal quantifiers and equations that
    describe what is learnt when pattern matching succeeds. The negative
    formula, the failure postcondition [ψ], describes what is learnt when
    pattern matching fails. *)

  (* When a pattern cannot fail or can fail due to several distinct causes,
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
    pattern η PAny v φ False.
  Proof.
    unfold pattern. simpl_extend. eauto using pure_wp_ret.
  Qed.

  Lemma pat_PVar η x v φ :
    φ ((x, v) :: η) →
    pattern η (PVar x) v φ False.
  Proof.
    unfold pattern. simpl_extend. eauto using pure_wp_ret.
  Qed.

  (* Given a goal of the form [pattern η (PVar x) v ?φ False],
    applying the lemma [pat_PVar2] solves the goal and
    instantiates the postcondition [?φ]. *)

  Lemma pat_PVar2 η x v :
    pattern η (PVar x) v (λ η', η' = (x, v) :: η) False.
  Proof.
    by apply pat_PVar.
  Qed.

  Ltac pat_PVar :=
    match goal with
    | |- pattern _ (PVar _) _ _ _ =>
        (apply pat_PVar2 || eapply pat_PVar)
    end.

  Lemma pat_PAlias η p x v φ ψ :
    pattern η p v (λ η, φ ((x, v) :: η)) ψ →
    pattern η (PAlias p x) v φ ψ.
  Proof.
    unfold pattern. simpl_extend; intros.
    apply pure_wp_bind.
    eauto using pure_wp_mono, pure_wp_ret.
  Qed.

  (* TODO generalize to [(φ1 η → pattern η p2 v φ ψ2)] and see if it is useful *)
  Lemma pat_POr η p1 p2 v φ ψ1 ψ2 :
    pattern η p1 v φ ψ1 →
    pattern η p2 v φ ψ2 →
    pattern η (POr p1 p2) v φ (ψ1 ∧ ψ2).
      (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
        disjunction pattern to fail, both sides must fail. *)
  Proof.
    unfold pattern. simpl_extend; intros.
    eauto using pure_wp_orelse, pure_wp_mono.
  Qed.

  Lemma pat_PUnit η v φ :
    φ η →
    v = #() →
    pattern η PUnit v φ False.
  Proof.
    unfold pattern. intros ? ->; simpl_extend.
    eauto using pure_wp_ret.
  Qed.

  Lemma pat_PTuple `{Encode A} η ps (a : A) vs φ ψ :
    #a = VTuple vs ->
    patterns η ps vs φ ψ →
    pattern η (PTuple ps) #a φ ψ.
  Proof.
    unfold patterns, pattern.
    intros ->. by simpl_extend.
  Qed.

  Lemma pat_PTuple_val η ps vs φ ψ :
    patterns η ps vs φ ψ ->
    pattern η (PTuple ps) (VTuple vs) φ ψ.
  Proof.
    unfold pattern. by simpl_extend.
  Qed.

  Lemma pat_PPair `{Encode A, Encode B} η p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
    v1 = #x1 ->
    v2 = #x2 ->
    pattern η p1 #x1 (λ η', pattern η' p2 #x2 φ (ψ2)) (ψ1) ->
    pattern η (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
  Proof.
    intros; subst.
    unfold pattern. simpl_extend.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    simpl; intros. rewrite bind_ret_right.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    auto using pure_wp_ret.
  Qed.

  Lemma pat_PData_nil η c c' φ ψ :
    (c = c' -> φ η) ->
    pattern η (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_extend.
    destruct_string_eqb;
      eauto using pure_wp_throw, pure_mono, pure_wp_ret.
  Qed.

  Lemma pat_PData_or η c c' p v φ ψ :
    (c = c' -> patterns η p v φ ψ) ->
    pattern η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_extend.
    destruct_string_eqb; eauto using pure_wp_throw.
    eapply pure_wp_mono; first apply H; eauto.
  Qed.

  Lemma pat_PData_eq η c p v φ ψ :
    patterns η p v φ ψ →
    pattern η (PData c p) (VData c v) φ ψ.
      (* This form is useful when [c = c'] is statically known. *)
  Proof.
    unfold pattern; intros. simpl_extend.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PData_neq η c p c' v φ :
    c ≠ c' →
    pattern η (PData c p) (VData c' v) φ True.
      (* This form is useful when [c ≠ c'] is statically known. *)
  Proof.
    unfold pattern; intros. simpl_extend.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PData η c p c' v v' φ :
    v = VData c' v' ->
    (c = c' -> patterns η p v' φ True) ->
    pattern η (PData c p) v φ True.
  Proof.
    unfold pattern; intros. simpl_extend. subst.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PXData_eq η c p c' v φ ψ :
    lookup_path η c = ret (VLoc c') ->
    patterns η p v φ ψ →
    pattern η (PXData c p) (VXData c' v) φ ψ.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Hpat.
    simpl_extend; rewrite Hlookup. cbn; rewrite bind_ret.
    unfold locations.eqb; destruct c'; cbn.
    by rewrite Z.eqb_refl.
  Qed.

  Lemma pat_PXData_neq η π p l1 l2 v φ :
    lookup_path η π = ret (VLoc l1) ->
    (address l1 <> address l2) ->
    pattern η (PXData π p) (VXData l2 v) φ True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Heq; simpl_extend.
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
    pattern η (PXData π p) (VXData l2 v) (λ _, False) True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Heq; simpl_extend.
    rewrite Hlookup. cbn; rewrite bind_ret.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    replace (address0 =? address) with false;
      last by apply eq_sym; apply Z.eqb_neq.
    by apply pure_wp_throw.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the auxiliary judgement [patterns]. *)

  Lemma pats_PNil η φ :
    φ η →
    patterns η [] [] φ False.
  Proof.
    unfold patterns.
    simpl_extends.
    eauto using pure_wp_ret.
  Qed.

  Lemma pats_PCons_unary η p ps v vs φ ψ1 ψ2 :
    pattern η p v (λ η, patterns η ps vs φ ψ2) ψ1 →
    patterns η (p :: ps) (v :: vs) φ (ψ1 \/ ψ2).
  Proof.
    unfold patterns, patterns. intros Hp; simpl_extends.
    eapply pure_wp_bind_conseq.
    { eapply pure_wp_mono.
      - eassumption.
      - simpl; intros. eapply pure_wp_mono; eauto.
      - tauto. }
    simpl; intros. rewrite bind_ret_right.
    eapply pure_wp_mono; eauto.
  Qed.

  Lemma pats_PCons_unary_false η p ps v vs φ :
    pattern η p v (λ η, patterns η ps vs φ False) False ->
    patterns η (p :: ps) (v :: vs) φ False.
  Proof.
    intros.
    assert (False \/ False -> False) as HFalse by tauto.
    eapply patterns_exn_mono; [ clear HFalse | exact HFalse ].
    by apply pats_PCons_unary.
  Qed.

  Lemma pats_PCons η p ps v vs φ' φ ψ1 ψ2 :
    pattern η p v φ' ψ1 →
    (∀ η, φ' η → patterns η ps vs φ ψ2) →
    patterns η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
  Proof.
    intros. eapply pats_PCons_unary.
    eapply pattern_mono; eauto.
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
    pattern η (PConstant c) (VConstant c') φ (c <> c').
  Proof.
    intros Hφ.
    eapply pattern_mono.
    { eapply pat_PData_or.
      intros Hc; specialize (Hφ Hc).
      pats. }
    { tauto. }
    { tauto. }
  Qed.

  Lemma pat_PConst_eq η c φ :
    φ η ->
    pattern η (PConstant c) (VConstant c) φ False.
  Proof.
    intros Hφ.
    eapply pattern_exn_mono; [ eapply pat_PConst; eauto | tauto ].
  Qed.

  Lemma pat_PConst_neq η c c' e ψ :
    c <> c' ->
    ψ ->
    pattern η (PConstant c) (VData c' e) (λ _, False) ψ.
  Proof.
    intros Hneq Hψ.
    unfold pattern. simpl_extend.
    apply String.eqb_neq in Hneq as ->.
    by apply pure_wp_throw.
  Qed.

  Lemma pat_false η v (P : Prop) φ :
    v = #P →
    (¬P → φ η) →
    pattern η (PConstant "false") v φ P.
  Proof.
    intros -> ?; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_true_elim].
      done. }

    { eapply pattern_exn_mono.
      eapply pat_PConst_eq;
        auto using truth_false_elim.
      tauto. }
  Qed.

  Lemma pat_true η v (P : Prop) φ :
    v = #P →
    (P → φ η) →
    pattern η (PConstant "true") v φ (¬P).
  Proof.
    intros -> Hφ; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_exn_mono.
      eapply pat_PConst_eq;
        apply Hφ; by apply truth_true_elim.
      tauto. }

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_false_elim].
      intros; tauto. }
  Qed.

  Lemma pat_PInt η v (i j : Z) (φ : env → Prop) :
    int.representable i →
    int.representable j →
    v = #j →
    (i = j → φ η) →
    pattern η (PInt i) v φ (i <> j).
  Proof.
    intros Hi Hj -> Hφ.
    unfold pattern; simpl_extend.
    rewrite int.eq_repr_repr; auto.
    destruct (_ =? _) eqn:E.
    - apply pure_wp_ret. apply Hφ. by apply Z.eqb_eq.
    - apply pure_wp_throw. by apply Z.eqb_neq.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma cpat_CVal η p v φ ψ :
    pattern η p v φ ψ ->
    cpattern η (CVal p) (O2Ret v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_CExc η p v φ ψ :
    pattern η p v φ ψ ->
    cpattern η (CExc p) (O2Throw v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_COr η cp1 cp2 o φ ψ1 ψ2 :
    cpattern η cp1 o φ ψ1 ->
    cpattern η cp2 o φ ψ2 ->
    cpattern η (COr cp1 cp2) o φ (ψ1 /\ ψ2).
  Proof.
    unfold cpattern. intros.
    eapply pure_wp_orelse; [ eassumption | ].
    eauto using pure_wp_mono.
  Qed.

  Lemma cpat_CEff η peff pk v k φ ψ1 ψ2 :
    pattern η peff v (λ δ, pattern δ pk (VCont k) φ ψ2) ψ1 ->
    cpattern η (CEff peff pk) (O3Perform v k) φ (ψ1 \/ ψ2).
  Proof.
    unfold cpattern, pattern; intros. simpl.
    eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
    simpl; intros δ ?.
    eauto using pure_wp_mono.
  Qed.

  Fixpoint valid_cpattern_match {A E} cp (o : outcome3 A E) :=
    match cp, o with
    | CVal _, O3Ret _
    | CExc _, O3Throw _
    | CEff _ _, O3Perform _ _ =>
        true
    | COr cp1 cp2, _ =>
        valid_cpattern_match cp1 o || valid_cpattern_match cp2 o
    | _, _ =>
        false
    end.

  Lemma invert_valid_match cp o :
    valid_cpattern_match cp o = false ->
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
    valid_cpattern_match cp o = false ->
    ψ ->
    cpattern η cp o φ ψ.
  Proof.
    intros.
    unfold cpattern.
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
    pattern η pNil v φ (xs ≠ []).
    (* If the match is unsuccessful, move to the next branch
      with the knowledge that [xs] is not empty *)
  Proof.
    intros; subst.
    destruct xs; eapply pattern_exn_mono.
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
        pattern η p1 #x (φ1 x) (ψ1 x)) ->
        (* If [#x] matches [p1], we gain the knowledge [φ1 x η0].
          Otherwise, we gain the knowledge [ψ1 x] *)
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        (forall η', φ1 x η' -> pattern η' p2 #xs' φ (ψ2 xs'))) ->
        (* If [#xs'] does not match [p2], then we gain the knowledge [ψ2 xs'] *)
    pattern η (pCons p1 p2) v φ (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
    (* There are three ways the match can be unsuccessful:
      - the list is empty
      - the list is non-empty, but its head did not match [p1]
      - the list is non-empty, but its tail did not match [p2] *)
  Proof.
    intros; subst.
    destruct xs.
    { eapply pattern_exn_mono.
      { by apply pat_PData_neq. }
      tauto. }
    { eapply pattern_exn_mono.
      { eapply pat_PData_eq; pats.  }
      right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  Lemma pat_pCons `{Encode A} v xs η p1 p2 φ
    (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern η p1 #x
          (λ η',
            pattern η' p2 #xs' φ (ψ2 xs'))
          (ψ1 x)) ->
    pattern η (pCons p1 p2) v φ
      (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
  Proof.
    intros; subst.
    destruct xs; eapply pattern_exn_mono.
    { by apply pat_PData_neq. }
    { tauto. }
    { eapply pat_PData_eq; pats. }
    { clear; right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  (* The previous lemmas start to give us a general scheme for reasoning about
    pattern matching on ADTs.

    More experimenting is required.
    As of now (29/02/24), see [examples/splay.v] for more examples. *)

  (* Pattern proofmode tactics *)


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
    (forall e, o = O3Throw e -> pattern η p e φ ψ) ->
    cpattern η (CExc p) o φ (is_not_O3Throw o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - apply pure_wp_throw. by left.
    - eapply pure_wp_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - apply pure_wp_throw. by left.
  Qed.

  Lemma cpat_CVal_abst η p o φ ψ :
    (forall v, o = O3Ret v -> pattern η p v φ ψ) ->
    cpattern η (CVal p) o φ (is_not_O3Ret o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - eapply pure_wp_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - apply pure_wp_throw. by left.
    - apply pure_wp_throw. by left.
  Qed.

  Lemma cpat_CEff_abst η peff pk o φ ψ1 ψ2 :
    (forall eff k,
        o = O3Perform eff k ->
        pattern η peff eff (λ δ, pattern δ pk (VCont k) φ ψ2) ψ1) ->
    cpattern η (CEff peff pk) o φ (is_not_O3Perform o ∨ ψ1 ∨ ψ2).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - apply pure_wp_throw. by left.
    - apply pure_wp_throw. by left.
    - eapply pure_wp_bind.
      eapply pure_wp_mono; [ apply Hpat; reflexivity | | auto ].
      intros δ Hpat2.
      eapply pure_wp_mono; [ apply Hpat2 | auto | auto ].
  Qed.

  Lemma cpat_CEff_impossible η peff pk (o : outcome2 val exn) φ :
    cpattern η (CEff peff pk) o φ True.
  Proof.
    unfold cpattern.
    destruct o; simpl; by apply pure_wp_throw.
  Qed.

End pattern_rules.
