From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.

Implicit Type φ : env -> Prop.
Implicit Type ψ : Prop.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [patterns]. *)

Lemma pats_PNil η φ :
  φ η →
  patterns η [] [] φ False.
Proof.
  unfold patterns.
  simpl_extends.
  eauto using total_ret.
Qed.

Lemma pats_PCons_unary η p ps v vs φ ψ1 ψ2 :
  pattern η p v (λ η, patterns η ps vs φ ψ2) ψ1 →
  patterns η (p :: ps) (v :: vs) φ (ψ1 \/ ψ2).
Proof.
  unfold patterns, patterns. intros Hp; simpl_extends.
  eapply total_bind.
  { eapply total_consequence.
    - eassumption.
    - simpl; intros. eapply total_consequence; eauto.
    - tauto. }
  simpl; intros. rewrite bind_ret_right.
  eapply total_consequence; eauto.
Qed.

Lemma pats_PCons η p ps v vs φ' φ ψ1 ψ2 :
  pattern η p v φ' ψ1 →
  (∀ η, φ' η → patterns η ps vs φ ψ2) →
  patterns η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
Proof.
  intros. eapply pats_PCons_unary.
  eapply pat_consequence; eauto.
Qed.

(* [pats_unary] expects a goal of the form [patterns η ps vs φ ψ]. It is
   used during pattern matching because the [patterns] judgement can be
   introduced by applying [pat_PTuple]. *)

(* We use the unary version in automation tactics to avoid creating
   evars accross different subgoals and scopes. *)

Ltac pats_unary :=
  first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons_unary; [ eauto ]
    ].

(* The binary variant is more natural to use in interactive proofs. *)

Ltac pats :=
  repeat first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons; [ eauto | simpl; intros ]
    ].

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
  unfold pattern. simpl_extend. eauto using total_ret.
Qed.

Lemma pat_PVar η x v φ :
  φ ((x, v) :: η) →
  pattern η (PVar x) v φ False.
Proof.
  unfold pattern. simpl_extend. eauto using total_ret.
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
  apply total_bind_unary.
  eauto using total_consequence, total_ret.
Qed.

Lemma pat_POr η p1 p2 v φ ψ1 ψ2 :
  pattern η p1 v φ ψ1 →
  pattern η p2 v φ ψ2 →
  pattern η (POr p1 p2) v φ (ψ1 ∧ ψ2).
    (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
       disjunction pattern to fail, both sides must fail. *)
Proof.
  unfold pattern. simpl_extend; intros.
  eauto using total_orelse, total_consequence.
Qed.

Lemma pat_PUnit η v φ :
  φ η →
  v = #() →
  pattern η PUnit v φ False.
Proof.
  unfold pattern. intros ? ->; simpl_extend.
  eauto using total_ret.
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

Ltac pat_PTuple :=
  first [
      eapply pat_PTuple; first solve [ encode ]
    | rewrite 1 ?encode_encode'; simpl; eapply pat_PTuple_val ].

Lemma pat_PPair `{Encode A, Encode B} η p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
  v1 = #x1 ->
  v2 = #x2 ->
  pattern η p1 #x1 (λ η', pattern η' p2 #x2 φ (ψ2)) (ψ1) ->
  pattern η (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
Proof.
  intros; subst.
  unfold pattern. simpl_extend.
  eapply total_bind; [ eapply total_consequence; eauto | ].
  simpl; intros. rewrite bind_ret_right.
  eapply total_bind; [ eapply total_consequence; eauto | ].
  auto using total_ret.
Qed.

Lemma pat_PData η c p c' v φ ψ :
  (c = c' → pattern η p v φ ψ) →
  pattern η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
    (* This form is useful when the truth of the equality [c = c']
       is not statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; eauto using total_throw, total_consequence.
Qed.

Lemma pat_PData_eq η c p v φ ψ :
  pattern η p v φ ψ →
  pattern η (PData c p) (VData c v) φ ψ.
    (* This form is useful when [c = c'] is statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; solve [ eauto using total_throw | tauto ].
Qed.

Lemma pat_PData_neq η c p c' v φ :
  c ≠ c' →
  pattern η (PData c p) (VData c' v) φ True.
    (* This form is useful when [c ≠ c'] is statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; solve [ eauto using total_throw | tauto ].
Qed.

Lemma pat_PXData_eq η c p c' v φ ψ :
  lookup_path η c = ret (VLoc c') ->
  pattern η p v φ ψ →
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
  by apply total_throw.
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
  by apply total_throw.
Qed.

Lemma pat_PConst η c c' φ :
  (c = c' -> φ η) ->
  pattern η (PConstant c) (VConstant c') φ (c <> c').
Proof.
  intros Hφ.
  eapply pat_consequence.
  { eapply pat_PData.
    intros Hc; specialize (Hφ Hc).
    pat_PTuple; pats. }
  { tauto. }
  { tauto. }
Qed.

Lemma pat_PConst_eq η c φ :
  φ η ->
  pattern η (PConstant c) (VConstant c) φ False.
Proof.
  intros Hφ.
  eapply pat_consequence_psi; [ eapply pat_PConst; eauto | tauto ].
Qed.

Lemma pat_PConst_neq η c c' ψ :
  c <> c' ->
  ψ ->
  pattern η (PConstant c) (VConstant c') (λ _, False) ψ.
Proof.
  intros.
  eapply pat_consequence_psi; [ apply pat_PConst | ]; tauto.
Qed.

Lemma pat_false η v (P : Prop) φ :
  v = #P →
  (¬P → φ η) →
  pattern η (PConstant "false") v φ P.
Proof.
  intros -> ?; simpl.
  destruct (truth P) eqn:?.

  { eapply pat_consequence_phi.
    eapply pat_PConst_neq;
      [ by simpl | by apply truth_true_elim].
    done. }

  { eapply pat_consequence_psi.
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

  { eapply pat_consequence_psi.
    eapply pat_PConst_eq;
      apply Hφ; by apply truth_true_elim.
    tauto. }

  { eapply pat_consequence_phi.
    eapply pat_PConst_neq;
      [ by simpl | by apply truth_false_elim].
    intros; tauto. }
Qed.

Lemma pat_PInt η v (i j : Z) (φ : env → Prop) :
  representable i →
  representable j →
  v = #j →
  (i = j → φ η) →
  pattern η (PInt i) v φ (i <> j).
Proof.
  intros Hi Hj -> Hφ.
  unfold pattern; simpl_extend.
  rewrite eq_repr_repr; auto.
  destruct (_ =? _) eqn:E.
  - apply total_ret. apply Hφ. by apply Z.eqb_eq.
  - apply total_throw. by apply Z.eqb_neq.
Qed.

Ltac pat_PInt :=
  eapply pat_PInt; [ | | encode | ]; representable; intros.

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
  destruct xs; eapply pat_consequence_psi.
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
  { eapply pat_consequence_psi.
    { by apply pat_PData_neq. }
    tauto. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_eq; pat_PTuple.
      pats.  }
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
  destruct xs; eapply pat_consequence_psi.
  { by apply pat_PData_neq. }
  { tauto. }
  { eapply pat_PData_eq; pat_PTuple.
    pats. }
  { clear; right; do 2 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNil :=
  eapply pat_pNil; first solve [ encode ].

Ltac pat_pCons :=
  eapply pat_pCons; first solve [ encode ].

(* The previous lemmas start to give us a general scheme for reasoning about
   pattern matching on ADTs.

   More experimenting is required.
   As of now (29/02/24), see [examples/splay.v] for more examples. *)

(* -------------------------------------------------------------------------- *)

(* [pure_match η v bs φ] is sugar for [pure (eval_match η v bs) φ].

   [eval_match] is used by [eval] when evaluating an [EMatch]. *)

Definition pure_match `{Encode A} (η : env) bs (o : outcome3 val exn) (φ : A -> Prop) :=
  pure (deep_eval_match η bs o) φ.

Arguments pure_match {A} {H} _ _ _ _.

Lemma pure_eval_match `{Encode A, Encode B} η e bs (a : A) (φ : B -> Prop) :
  pure (eval η e) (λ x, x = a) ->
  pure_match η bs (O3Ret #a) φ ->
  pure (eval η (EMatch e bs)) φ.
Proof.
  unfold pure_match; intros Heval Hmatch.
  destruct Heval as (? & ? & ->).
  eapply pure_simp; [ simpl_eval; eapply SimpHandleRet; eassumption |  ].
  unfold continue. by simpl_install_deep_eval_match.
Qed.

Lemma pure_eval_match' `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) :
  pure (eval η e) φ' ->
  (∀ (a : A), φ' a -> pure_match η bs (O3Ret #a) φ) ->
  pure (eval η (EMatch e bs)) φ.
Proof.
  unfold pure_match; intros Heval Hmatch.
  destruct Heval as (? & ? & ?).
  eapply pure_simp; [ simpl_eval; eapply SimpHandleRet; eassumption | ].
  unfold continue. simpl_install_deep_eval_match. auto.
Qed.

(* Currently unused *)

Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) :
  cpattern η p v (λ η', pure (eval η' e) φ) (pure_match η bs v φ) ->
  pure_match η ((Branch p e) :: bs) v φ.
Proof.
  unfold pure_match; unfold pattern.
  intros; simpl_deep_eval_match.
  by apply total_pure.
Qed.

Lemma pure_match_cons `{Encode A} η v p e bs (φ : A -> Prop) ψ :
  cpattern η p v (λ η', pure (eval η' e) φ) ψ ->
  (ψ -> (pure_match η bs v φ)) ->
  pure_match η ((Branch p e) :: bs) v φ.
Proof.
  intros.
  apply pure_match_cons_unary.
  unfold cpattern in *; eauto using total_consequence.
Qed.

(* Not matching is an error. *)

Lemma pure_match_nil `{Encode A} η v (φ : A -> Prop) :
  False -> pure_match η [] v φ.
Proof. contradiction. Qed.

Lemma pure_match_single `{Encode A} η v p e (φ : A -> Prop) ψ :
  cpattern η p v (λ η' : env, pure (eval η' e) φ) ψ →
  (ψ -> False) ->
  pure_match η [Branch p e] v φ.
Proof.
  intros.
  eapply pure_match_cons; eauto.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Pattern proofmode tactics *)

Ltac specify_cpattern :=
  first [
      apply cpat_CVal
    | apply cpat_CExc
    | eapply cpat_COr; specify_cpattern
    | eapply cpat_CEff
    | eapply cpat_mismatch; [ cbn; reflexivity | ]
    ].

Local Ltac strip_disjunction :=
  match goal with
  | H : _ \/ _ |- _ =>
      destruct H as [ H | H ]; try contradiction
  end.
Local Ltac remove_tauto :=
  lazymatch goal with
  | H : ?x = ?x |- _ => clear H
  | _ => idtac
  end.
Local Ltac subst_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ => subst x
  | _ => idtac
  end.
Local Ltac inject_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ =>
      (injection H; repeat (intros ->) || clear dependent x)
  | _ => idtac
  end.
Local Ltac elim_exists :=
  lazymatch goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  end.
Local Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

(* [resolve_no_match] attempts to prove by contradiction that
   not matching on any branch of a pattern match is impossible. Its
   tactics target the "no_match" hypotheses that are generated by
   [pure_match_branches] and instantiated by [pattern_match]. *)

Ltac resolve_no_match :=
  repeat first
    [ strip_disjunction
    | elim_exists
    | destruct_hyp
    | congruence
    | remove_tauto
    | subst_eq
    | inject_eq ].

Ltac pattern_hook := fail.

(* [pattern_match] expects a goal in the form of a [pattern] or [patterns] judgement.
   It tries to apply all know pattern matching rules. We use [pattern_hook] to
   make this tactic extensible (see its redefinition in examples/splay.v). *)

Ltac pattern_match :=
  repeat first
    [ pats_unary
    | pattern_hook
    | pat_PVar
    | pat_PInt
    | pat_pNil; intros
    | pat_pCons; intros
    | eapply pat_PXData_eq; [ reflexivity || by eauto | ]
    | eapply pat_PXData_neq; [ reflexivity || by eauto | auto ]
    | eapply pat_PConst_eq; by apply eq_refl
    | apply pat_POr
    | pat_PTuple
    | apply pat_PAlias
    | apply pat_PAny ].

(* [post_process_pats] is expected to be used on multiple goals of the
   form [pattern η p v ?φ ?ψ] and one goal of the form [False]. It performs
   pattern matching on the pat goals and then tries to prove the
   non-matching (False) goal. *)

Ltac post_process_pats :=
  (* First try to resolve the pattern matching, instantiating all
     postcondition evars in the process *)
  match goal with
  | |- False => idtac
  | _ => pattern_match
  end;
  (* Only after finishing our matches do we substitute our newly
     learnt equalities *)
  subst;
  (* Afterwards, use [resolve_no_match] to perform congruence on the
     remaining False goal *)
  match goal with
  | |- False => resolve_no_match
  | _ => idtac
  end.

(* [pure_match_branches] expects a goal of the form
   [pure_match _ _ bs _] where [bs] is a list of n branches. It
   successively applies [pure_match_cons], creating n subgoals of the
   form [pattern _ _ _ (λ n', pure (eval η' _) _ _) _] and one subgoal of
   the form [False]. *)

Ltac pure_match_branches :=
  lazymatch goal with
  | |- pure_match _ [?b] _ _ =>
      eapply pure_match_single;
      [ specify_cpattern
      | let no_match := fresh "no_match" in
        intros no_match ]
  | |- pure_match _ (?b :: ?bs) _ _ =>
      eapply pure_match_cons;
      [ specify_cpattern
      | (let no_match := fresh "no_match" in
         intros no_match; pure_match_branches) ]
  | |- pure_match _ ?b _ _ =>
      progress (unfold b);
      pure_match_branches
  end.

(* [pure_match] expects a goal of the form [pure_match _ _ _ _], and
   produces subgoals corresponding to the successful match and entry
   of each branch. *)

Ltac pure_match := pure_match_branches; post_process_pats.
