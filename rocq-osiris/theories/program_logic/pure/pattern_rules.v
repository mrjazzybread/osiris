From osiris Require Import base.
From osiris.lang Require Import syntax encode notations locations.
From osiris.semantics Require Import semantics.

Open Scope Z_scope.

(* This file defines judgements for Hoare-style reasoning on
   the auxiliary functions in [semantics/eval.v]. *)

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

(* The judgement [pattern η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition cpattern η δ p o (φ : env -> Prop) (ζ : Prop) :=
  match eval_cpat η δ p o with
  | Some η => φ η
  | None => ζ
  end.

Definition pattern η δ p v (φ : env -> Prop) (ζ : Prop) :=
  match eval_pat η δ p v with
  | Some η => φ η
  | None => ζ
  end.

Definition patterns η δ ps vs (φ : env -> Prop) (ζ : Prop) :=
  match eval_pats η δ ps vs with
  | Some η => φ η
  | None => ζ
  end.

Lemma union_None_l {A} (o : option A) :
  None ∪ o = o.
Proof. by destruct o. Qed.

(* -------------------------------------------------------------------------- *)

Section pattern_rules.

  Implicit Type φ : env -> Prop.
  Implicit Type ζ : Prop.

  (* Monotonicity properties for [cpattern], [pattern], and [patterns]. *)

  Lemma cpattern_mono η δ p v (φ φ' : env -> Prop) (ζ ζ' : Prop) :
    cpattern η δ p v φ ζ →
    (∀ δ, φ δ → φ' δ) →
    (ζ → ζ') →
    cpattern η δ p v φ' ζ'.
  Proof.
    unfold cpattern.
    destruct (eval_cpat η δ p v); auto.
  Qed.

  Lemma cpattern_env_mono η δ p v (φ φ' : env -> Prop) (ζ : Prop) :
    cpattern η δ p v φ ζ →
    (∀ δ, φ δ → φ' δ) →
    cpattern η δ p v φ' ζ.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma cpattern_mono_exn η δ p v (φ : env -> Prop) (ζ ζ': Prop) :
    cpattern η δ p v φ ζ →
    (ζ → ζ') →
    cpattern η δ p v φ ζ'.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma pattern_mono η δ p v (φ φ' : env -> Prop) (ζ ζ' : Prop) :
    pattern η δ p v φ ζ →
    (∀ δ, φ δ → φ' δ) →
    (ζ → ζ') →
    pattern η δ p v φ' ζ'.
  Proof.
    unfold pattern. destruct (eval_pat η δ p v); auto.
  Qed.

  Lemma pattern_env_mono η δ p v (φ φ' : env -> Prop) (ζ : Prop) :
    pattern η δ p v φ ζ →
    (∀ δ, φ δ → φ' δ) →
    pattern η δ p v φ' ζ.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma pattern_mono_exn η δ p v (φ : env -> Prop) (ζ ζ': Prop) :
    pattern η δ p v φ ζ →
    (ζ → ζ') →
    pattern η δ p v φ ζ'.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma patterns_mono η δ ps vs (φ φ' : env -> Prop) (ζ ζ' : Prop) :
    patterns η δ ps vs φ ζ →
    (∀ η, φ η → φ' η) →
    (ζ → ζ') →
    patterns η δ ps vs φ' ζ'.
  Proof.
    unfold patterns; destruct (eval_pats η δ ps vs); auto.
  Qed.

  Lemma patterns_env_mono η δ ps vs (φ φ' : env -> Prop) (ζ : Prop) :
    patterns η δ ps vs φ ζ →
    (∀ δ, φ δ → φ' δ) →
    patterns η δ ps vs φ' ζ.
  Proof. intros; by eapply patterns_mono. Qed.

  Lemma patterns_mono_exn η δ ps vs (φ : env -> Prop) (ζ ζ': Prop) :
    patterns η δ ps vs φ ζ →
    (ζ → ζ') →
    patterns η δ ps vs φ ζ'.
  Proof. intros; by eapply patterns_mono. Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the judgement [pattern]. *)

  (* From an operational point of view, the repeated application of these
    lemmas to a pattern [p] and a value [v] have the effect of translating
    the pattern matching operation [p = v] into a positive formula and a
    negative formula. The positive formula, the postcondition [φ],
    accumulates a sequence of universal quantifiers and equations that
    describe what is learnt when pattern matching succeeds. The negative
    formula, the failure postcondition [ζ], describes what is learnt when
    pattern matching fails. *)

  (* When a pattern cannot fail or can fail due to several distinct causes,
    a naive statement of its reasoning rule would have one occurrence of
    [ζ] in its conclusion and no occurrence or multiple occurrences of [ζ]
    in its premises. From an operational point of view, this is
    undesirable, because [ζ] is then unconstrained or duplicated. We avoid
    this phenomenon by using [False] or a disjunction in the conclusion of
    the reasoning rule. Thus, from an operational point of view, applying
    the reasoning rule instantiates the failure postcondition with a
    logical connective. *)

  Lemma pat_PAny η δ v φ :
    φ δ →
    pattern η δ PAny v φ False.
  Proof.
    unfold pattern. simpl_eval_pat. auto.
  Qed.

  Lemma pat_PVar η δ x v φ :
    φ ((x, v) :: δ) →
    pattern η δ (PVar x) v φ False.
  Proof.
    unfold pattern. simpl_eval_pat. auto.
  Qed.

  (* Given a goal of the form [pattern η (PVar x) v ?φ False],
    applying the lemma [pat_PVar2] solves the goal and
    instantiates the postcondition [?φ]. *)

  Lemma pat_PVar2 η δ x v :
    pattern η δ (PVar x) v (λ δ', δ' = (x, v) :: δ) False.
  Proof.
    by apply pat_PVar.
  Qed.

  Ltac pat_PVar :=
    match goal with
    | |- pattern _ (PVar _) _ _ _ =>
        (apply pat_PVar2 || eapply pat_PVar)
    end.

  Lemma pat_PAlias η δ p x v φ ζ :
    pattern η δ p v (λ δ, φ ((x, v) :: δ)) ζ →
    pattern η δ (PAlias p x) v φ ζ.
  Proof.
    unfold pattern. simpl_eval_pat; intros.
    destruct (eval_pat η δ p v); auto.
  Qed.

  Lemma pat_POr η δ p1 p2 v φ ζ1 ζ2 :
    pattern η δ p1 v φ ζ1 →
    (ζ1 → pattern η δ p2 v φ ζ2) →
    pattern η δ (POr p1 p2) v φ (ζ1 ∧ ζ2).
      (* The conjunction [ζ1 ∧ ζ2] reflects the fact that, for the
        disjunction pattern to fail, both sides must fail. *)
  Proof.
    unfold pattern. simpl_eval_pat; intros.
    destruct (eval_pat η δ p1 v).
    - by rewrite union_Some_l.
    - destruct (eval_pat η δ p2 v); simpl; auto.
  Qed.

  Lemma pat_PUnit η δ v φ :
    φ δ →
    v = #() →
    pattern η δ PUnit v φ False.
  Proof.
    unfold pattern. intros ? ->; simpl_eval_pat; auto.
  Qed.

  Lemma pat_PTuple `{Encode A} η δ ps (a : A) vs φ ζ :
    #a = VTuple vs ->
    patterns η δ ps vs φ ζ →
    pattern η δ (PTuple ps) #a φ ζ.
  Proof.
    unfold patterns, pattern.
    intros ->. by simpl_eval_pat.
  Qed.

  Lemma pat_PTuple_val δ η ps vs φ ζ :
    patterns δ η ps vs φ ζ ->
    pattern δ η (PTuple ps) (VTuple vs) φ ζ.
  Proof.
    unfold pattern. by simpl_eval_pat.
  Qed.

  Lemma pat_PPair `{Encode A, Encode B} η δ p1 p2 v1 v2 (x1 : A) (x2 : B) φ ζ1 ζ2 :
    v1 = #x1 ->
    v2 = #x2 ->
    pattern η δ p1 #x1 (λ δ', pattern η δ' p2 #x2 φ (ζ2)) (ζ1) ->
    pattern η δ (PPair p1 p2) (VPair v1 v2) φ (ζ1 \/ ζ2).
  Proof.
    intros; subst.
    unfold pattern in H3 |- *. simpl_eval_pat.
    destruct (eval_pat η δ p1 #x1); simpl; last auto.
    destruct (eval_pat η e p2 #x2); simpl; auto.
  Qed.

  Lemma pat_PData_nil η δ c c' φ ζ :
    (c = c' -> φ δ) ->
    pattern η δ (PData c nil) (VData c' nil) φ (ζ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; auto.
  Qed.

  Lemma pat_PData_or η δ c c' ps vs φ ζ :
    (c = c' -> patterns η δ ps vs φ ζ) ->
    pattern η δ (PData c ps) (VData c' vs) φ (ζ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; eauto.
    eapply patterns_mono; first apply H; eauto.
  Qed.

  Lemma pat_PData_eq η δ c ps vs φ ζ :
    patterns η δ ps vs φ ζ →
    pattern η δ (PData c ps) (VData c vs) φ ζ.
      (* This form is useful when [c = c'] is statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; eauto.
    contradiction.
  Qed.

  Lemma pat_PData_neq η δ c ps c' vs φ :
    c ≠ c' →
    pattern η δ (PData c ps) (VData c' vs) φ True.
      (* This form is useful when [c ≠ c'] is statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; eauto.
    contradiction.
  Qed.

  Lemma pat_PData η δ c ps c' v vs φ :
    v = VData c' vs ->
    (c = c' -> patterns η δ ps vs φ True) ->
    pattern η δ (PData c ps) v φ True.
  Proof.
    unfold pattern; intros. simpl_eval_pat. subst.
    destruct_string_eqb; auto.
    apply (H0 Heq).
  Qed.

  (* This more general version is not used in tactics at the moment *)
  Lemma pat_PXData η δ π ps l l' vs φ ζ :
    lookup_path η π = Some #l' →
    (l = l' → patterns η δ ps vs φ ζ) →
    pattern η δ (PXData π ps) (VXData l vs) φ (ζ ∨ l ≠ l').
  Proof.
    unfold pattern. simpl_eval_pat. intros ->.
    simpl.
    destruct (eqb_spec l l').
    - intros. eapply patterns_mono_exn; eauto.
    - tauto.
  Qed.

  Lemma pat_PXData_eq η δ π ps l vs φ ζ :
    lookup_path η π = Some #l ->
    patterns η δ ps vs φ ζ →
    pattern η δ (PXData π ps) (VXData l vs) φ ζ.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Hpat.
    simpl_eval_pat; rewrite Hlookup. simpl.
    unfold locations.eqb; destruct l; cbn.
    by rewrite Z.eqb_refl.
  Qed.

  Lemma pat_PXData_neq η δ π ps l1 l2 vs φ :
    lookup_path η π = Some #l1 ->
    (address l1 <> address l2) ->
    pattern η δ (PXData π ps) (VXData l2 vs) φ True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Heq; simpl_eval_pat.
    rewrite Hlookup. cbn.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    apply Z.eqb_neq in Heq.
    by rewrite Z.eqb_sym, Heq.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the auxiliary judgement [patterns]. *)

  Lemma pats_PNil η δ φ :
    φ δ →
    patterns η δ [] [] φ False.
  Proof.
    unfold patterns. simpl_eval_pats. auto.
  Qed.

  Lemma pats_PCons_unary η δ p ps v vs φ ζ1 ζ2 :
    pattern η δ p v (λ δ, patterns η δ ps vs φ ζ2) ζ1 →
    patterns η δ (p :: ps) (v :: vs) φ (ζ1 \/ ζ2).
  Proof.
    unfold patterns, pattern. intros Hp; simpl_eval_pats.
    destruct (eval_pat η δ p v); simpl.
    - rewrite bind_with_Some.
      eapply patterns_mono_exn; eauto.
    - tauto.
  Qed.

  Lemma pats_PCons_unary_false η δ p ps v vs φ :
    pattern η δ p v (λ δ, patterns η δ ps vs φ False) False ->
    patterns η δ (p :: ps) (v :: vs) φ False.
  Proof.
    intros. eapply patterns_mono_exn.
    { apply pats_PCons_unary, H. }
    tauto.
  Qed.

  Lemma pats_PCons η δ p ps v vs φ' φ ζ1 ζ2 :
    pattern η δ p v φ' ζ1 →
    (∀ δ, φ' δ → patterns η δ ps vs φ ζ2) →
    patterns η δ (p :: ps) (v :: vs) φ (ζ1 ∨ ζ2).
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

  Lemma pat_PConst η δ c c' φ :
    (c = c' -> φ δ) ->
    pattern η δ (PConstant c) (VConstant c') φ (c <> c').
  Proof.
    intros Hφ.
    eapply pattern_mono.
    { eapply pat_PData_or.
      intros Hc; specialize (Hφ Hc).
      pats. }
    { tauto. }
    { tauto. }
  Qed.

  Lemma pat_PConst_eq η δ c φ :
    φ δ ->
    pattern η δ (PConstant c) (VConstant c) φ False.
  Proof.
    intros Hφ.
    eapply pattern_mono_exn; [ eapply pat_PConst; eauto | tauto ].
  Qed.

  Lemma pat_PConst_neq η δ c c' e ζ :
    c <> c' ->
    ζ ->
    pattern η δ (PConstant c) (VData c' e) (λ _, False) ζ.
  Proof.
    intros Hneq Hζ.
    unfold pattern. simpl_eval_pat.
    by apply String.eqb_neq in Hneq as ->.
  Qed.

  Lemma pat_false η δ v (P : Prop) φ :
    v = #P →
    (¬P → φ δ) →
    pattern η δ (PConstant "false") v φ P.
  Proof.
    intros -> ?; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_true_elim].
      done. }

    { eapply pattern_mono_exn.
      eapply pat_PConst_eq;
        auto using truth_false_elim.
      tauto. }
  Qed.

  Lemma pat_true η δ v (P : Prop) φ :
    v = #P →
    (P → φ δ) →
    pattern η δ (PConstant "true") v φ (¬P).
  Proof.
    intros -> Hφ; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_mono_exn.
      eapply pat_PConst_eq;
        apply Hφ; by apply truth_true_elim.
      tauto. }

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_false_elim].
      intros; tauto. }
  Qed.

  Lemma pat_PInt η δ v (i j : Z) (φ : env → Prop) :
    int.representable i →
    int.representable j →
    v = #j →
    (i = j → φ δ) →
    pattern η δ (PInt i) v φ (i <> j).
  Proof.
    intros Hi Hj -> Hφ.
    unfold pattern; simpl_eval_pat.
    rewrite int.eq_repr_repr; auto.
    destruct (_ =? _) eqn:E.
    - apply Hφ. by apply Z.eqb_eq.
    - by apply Z.eqb_neq.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma cpat_CVal η δ p v φ ζ :
    pattern η δ p v φ ζ ->
    cpattern η δ (CVal p) (O2Ret v) φ ζ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_CExc η δ p v φ ζ :
    pattern η δ p v φ ζ ->
    cpattern η δ (CExc p) (O2Throw v) φ ζ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_COr η δ cp1 cp2 o φ ζ1 ζ2 :
    cpattern η δ cp1 o φ ζ1 ->
    (ζ1 → cpattern η δ cp2 o φ ζ2) ->
    cpattern η δ (COr cp1 cp2) o φ (ζ1 /\ ζ2).
  Proof.
    unfold cpattern. intros. simpl eval_cpat.
    destruct (eval_cpat η δ cp1 o).
    - by rewrite union_Some_l.
    - destruct (eval_cpat η δ cp2 o); simpl; tauto.
  Qed.

  Lemma cpat_CEff η δ peff pk v k φ ζ1 ζ2 :
    pattern η δ peff v (λ δ, pattern η δ pk (VCont k) φ ζ2) ζ1 ->
    cpattern η δ (CEff peff pk) (O3Perform v k) φ (ζ1 \/ ζ2).
  Proof.
    unfold cpattern, pattern; intros. simpl.
    destruct (eval_pat η δ peff v); simpl.
    - eapply pattern_mono_exn; eauto.
    - tauto.
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
    ∀ η δ, eval_cpat η δ cp o = None.
  Proof.
    intros Hvalid η δ.
    induction cp; destruct o; simpl in *; try congruence;
      (* Only the [COr cp1 cp2] case remains. *)
      apply orb_false_elim in Hvalid as [H1 H2];
      apply IHcp1 in H1; apply IHcp2 in H2;
      apply union_None; auto.
  Qed.

  Lemma cpat_mismatch η δ cp o φ (ζ : Prop) :
    valid_cpattern_match cp o = false ->
    ζ ->
    cpattern η δ cp o φ ζ.
  Proof.
    intros.
    unfold cpattern.
    by rewrite invert_valid_match.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning for data *)

  (* The following reasoning rules exemplify a general approach for matching
    against algebraic data types. *)

  Lemma pat_pNil `{Encode A} η δ v (xs : list A) φ :
    v = #xs →
    (xs = [] -> φ δ) →
    (* Enter the branch with knowledge that [xs] is empty *)
    pattern η δ pNil v φ (xs ≠ []).
    (* If the match is unsuccessful, move to the next branch
      with the knowledge that [xs] is not empty *)
  Proof.
    intros; subst.
    destruct xs; eapply pattern_mono_exn.
    { eapply pat_PConst; eauto. }
    { tauto. }
    { eapply pat_PData_neq; done. }
    { congruence. }
  Qed.

  (* [pat_pCons_cut] exists for pedagogical purposes.
    We use [pat_pCons] in practice to avoid headaches caused
    by evar instantiation scopes. *)

  Lemma pat_pCons_cut `{Encode A} v xs η δ p1 p2 φ (φ1 : A -> env -> Prop)
    (ζ1 : A -> Prop) (ζ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern η δ p1 #x (φ1 x) (ζ1 x)) ->
        (* If [#x] matches [p1], we gain the knowledge [φ1 x η0].
          Otherwise, we gain the knowledge [ζ1 x] *)
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        (forall δ', φ1 x δ' -> pattern η δ' p2 #xs' φ (ζ2 xs'))) ->
        (* If [#xs'] does not match [p2], then we gain the knowledge [ζ2 xs'] *)
    pattern η δ (pCons p1 p2) v φ (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ζ1 x \/ ζ2 xs'))).
    (* There are three ways the match can be unsuccessful:
      - the list is empty
      - the list is non-empty, but its head did not match [p1]
      - the list is non-empty, but its tail did not match [p2] *)
  Proof.
    intros; subst.
    destruct xs.
    { eapply pattern_mono_exn.
      { by apply pat_PData_neq. }
      tauto. }
    { eapply pattern_mono_exn.
      { eapply pat_PData_eq; pats.  }
      right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  Lemma pat_pCons `{Encode A} v xs η δ p1 p2 φ
    (ζ1 : A -> Prop) (ζ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern η δ p1 #x
          (λ δ',
            pattern η δ' p2 #xs' φ (ζ2 xs'))
          (ζ1 x)) ->
    pattern η δ (pCons p1 p2) v φ
      (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ζ1 x \/ ζ2 xs'))).
  Proof.
    intros; subst.
    destruct xs; eapply pattern_mono_exn.
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

  Lemma cpat_CExc_abst η δ p o φ ζ :
    (forall e, o = O3Throw e -> pattern η δ p e φ ζ) ->
    cpattern η δ (CExc p) o φ (is_not_O3Throw o ∨ ζ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - tauto.
    - eapply pattern_mono_exn.
      apply Hpat. reflexivity.
      tauto.
    - tauto.
  Qed.

  Lemma cpat_CVal_abst η δ p o φ ζ :
    (forall v, o = O3Ret v -> pattern η δ p v φ ζ) ->
    cpattern η δ (CVal p) o φ (is_not_O3Ret o ∨ ζ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - eapply pattern_mono_exn. apply Hpat. reflexivity.
      tauto.
    - tauto.
    - tauto.
  Qed.

  Lemma cpat_CEff_abst η δ peff pk o φ ζ1 ζ2 :
    (forall eff k,
        o = O3Perform eff k ->
        pattern η δ peff eff (λ δ, pattern η δ pk (VCont k) φ ζ2) ζ1) ->
    cpattern η δ (CEff peff pk) o φ (is_not_O3Perform o ∨ ζ1 ∨ ζ2).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - tauto.
    - tauto.
    - unfold pattern in Hpat.
      specialize (Hpat e k eq_refl).
      destruct (eval_pat η δ peff ); simpl.
      + eapply pattern_mono_exn; eauto.
      + tauto.
  Qed.

  Lemma cpat_CEff_impossible η δ peff pk (o : outcome2 val exn) φ :
    cpattern η δ (CEff peff pk) o φ True.
  Proof.
    unfold cpattern.
    by destruct o.
  Qed.

End pattern_rules.
