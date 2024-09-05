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
  eauto using pure_ret.
Qed.

Lemma pats_PCons_unary η p ps v vs φ ψ1 ψ2 :
  pattern η p v (λ η, patterns η ps vs φ ψ2) ψ1 →
  patterns η (p :: ps) (v :: vs) φ (ψ1 \/ ψ2).
Proof.
  unfold patterns, patterns. intros Hp; simpl_extends.
  eapply pure_bind_conseq.
  { eapply pure_mono.
    - eassumption.
    - simpl; intros. eapply pure_mono; eauto.
    - tauto. }
  simpl; intros. rewrite bind_ret_right.
  eapply pure_mono; eauto.
Qed.

Lemma pats_PCons_unary_false η p ps v vs φ :
  pattern η p v (λ η, patterns η ps vs φ False) False ->
  patterns η (p :: ps) (v :: vs) φ False.
Proof.
  intros.
  assert (False \/ False -> False) as HFalse by tauto.
  eapply pats_consequence_psi; [ clear HFalse | exact HFalse ].
  by apply pats_PCons_unary.
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
  unfold pattern. simpl_extend. eauto using pure_ret.
Qed.

Lemma pat_PVar η x v φ :
  φ ((x, v) :: η) →
  pattern η (PVar x) v φ False.
Proof.
  unfold pattern. simpl_extend. eauto using pure_ret.
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
  apply pure_bind.
  eauto using pure_mono, pure_ret.
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
  eauto using pure_orelse, pure_mono.
Qed.

Lemma pat_PUnit η v φ :
  φ η →
  v = #() →
  pattern η PUnit v φ False.
Proof.
  unfold pattern. intros ? ->; simpl_extend.
  eauto using pure_ret.
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
  eapply pure_bind_conseq; [ eapply pure_mono; eauto | ].
  simpl; intros. rewrite bind_ret_right.
  eapply pure_bind_conseq; [ eapply pure_mono; eauto | ].
  auto using pure_ret.
Qed.

Lemma pat_PData η c p c' v φ ψ :
  (c = c' → pattern η p v φ ψ) →
  pattern η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
    (* This form is useful when the truth of the equality [c = c']
       is not statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; eauto using pure_throw, pure_mono.
Qed.

Lemma pat_PData_eq η c p v φ ψ :
  pattern η p v φ ψ →
  pattern η (PData c p) (VData c v) φ ψ.
    (* This form is useful when [c = c'] is statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
Qed.

Lemma pat_PData_neq η c p c' v φ :
  c ≠ c' →
  pattern η (PData c p) (VData c' v) φ True.
    (* This form is useful when [c ≠ c'] is statically known. *)
Proof.
  unfold pattern; intros. simpl_extend.
  destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
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
  by apply pure_throw.
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
  by apply pure_throw.
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

Lemma pat_PConst_neq η c c' e ψ :
  c <> c' ->
  ψ ->
  pattern η (PConstant c) (VData c' e) (λ _, False) ψ.
Proof.
  intros Hneq Hψ.
  unfold pattern. simpl_extend.
  apply String.eqb_neq in Hneq as ->.
  by apply pure_throw.
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
  - apply pure_ret. apply Hφ. by apply Z.eqb_eq.
  - apply pure_throw. by apply Z.eqb_neq.
Qed.

Ltac pat_PInt :=
  eapply pat_PInt; [ | | solve [ encode ] | ]; [ representable | representable | ]; intros.


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

(* [pure_match η v bs φ] is sugar for [pure (eval_match η v bs) ##φ ⊥].

   [eval_match] is used by [eval] when evaluating an [EMatch]. *)

Definition pure_match `{Encode A} (η : env) bs (o : outcome3 val exn) (φ : A -> Prop) :=
  pure (deep_eval_match η bs o) ##φ ⊥.

Arguments pure_match {A} {H} _ _ _ _.

Lemma pure_eval_match `{Encode A, Encode B} η e bs (a : A) (φ : B -> Prop) :
  pure (eval η e) ##(λ x, x = a) ⊥ ->
  pure_match η bs (O3Ret #a) φ ->
  pure (eval η (EMatch e bs)) ##φ ⊥.
Proof.
  unfold pure_match; intros Heval Hmatch. simpl.
  simpl_eval.
  apply pure_handle.
  apply (pure_mono _ Heval). 2: intros _ [].
  intros ? (? & -> & ->).
  simpl_install_deep_eval_match.
  apply (pure_mono _ Hmatch); eauto.
Qed.

Lemma pure_eval_match' `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) :
  pure (eval η e) ##φ' ⊥ ->
  (∀ (a : A), φ' a -> pure_match η bs (O3Ret #a) φ) ->
  pure (eval η (EMatch e bs)) ##φ ⊥.
Proof.
  unfold pure_match; intros Heval Hmatch. simpl.
  simpl_eval.
  apply pure_handle.
  apply (pure_mono _ Heval). 2: intros _ [].
  intros ? (a & -> & Ha).
  simpl_install_deep_eval_match.
  apply (pure_mono _ (Hmatch _ Ha)); eauto.
Qed.

(* Currently unused *)

Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) :
  cpattern η p v (λ η', pure (eval η' e) ##φ ⊥) (pure_match η bs v φ) ->
  pure_match η ((Branch p e) :: bs) v φ.
Proof.
  unfold pure_match; unfold pattern.
  intros; simpl_deep_eval_match.
  apply pure_try; auto.
Qed.

Lemma pure_match_cons `{Encode A} η v p e bs (φ : A -> Prop) ψ :
  cpattern η p v (λ η', pure (eval η' e) ##φ ⊥) ψ ->
  (ψ -> (pure_match η bs v φ)) ->
  pure_match η ((Branch p e) :: bs) v φ.
Proof.
  intros.
  apply pure_match_cons_unary.
  unfold cpattern in *; eauto using pure_mono.
Qed.

(* Not matching is an error. *)

Lemma pure_match_nil `{Encode A} η v (φ : A -> Prop) :
  False -> pure_match η [] v φ.
Proof. contradiction. Qed.

Lemma pure_match_single `{Encode A} η v p e (φ : A -> Prop) ψ :
  cpattern η p v (λ η' : env, pure (eval η' e) ##φ ⊥) ψ →
  (ψ -> False) ->
  pure_match η [Branch p e] v φ.
Proof.
  intros.
  eapply pure_match_cons; eauto.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

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
  - apply pure_throw. by left.
    (* right. exists tt. split; [ apply SimpReflexive | auto ]. *)
  - eapply pure_mono; [ apply Hpat | auto | auto ].
    reflexivity.
  - apply pure_throw. by left.
Qed.

Lemma cpat_CVal_abst η p o φ ψ :
  (forall v, o = O3Ret v -> pattern η p v φ ψ) ->
  cpattern η (CVal p) o φ (is_not_O3Ret o ∨ ψ).
Proof.
  intros Hpat.
  unfold cpattern.
  destruct o; simpl.
  - eapply pure_mono; [ apply Hpat | auto | auto ].
    reflexivity.
  - apply pure_throw. by left.
  - apply pure_throw. by left.
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
  - apply pure_throw. by left.
  - apply pure_throw. by left.
  - eapply pure_bind.
    eapply pure_mono; [ apply Hpat; reflexivity | | auto ].
    intros δ Hpat2.
    eapply pure_mono; [ apply Hpat2 | auto | auto ].
Qed.

Lemma cpat_CEff_impossible η peff pk (o : outcome2 val exn) φ :
  cpattern η (CEff peff pk) o φ True.
Proof.
  unfold cpattern.
  destruct o; simpl; by apply pure_throw.
Qed.


(* -------------------------------------------------------------------------- *)

From Ltac2 Require Import Ltac2.

(* [specify_cpattern] takes a goal of the form [cpattern η cp o3 φ ψ]
   and turns it into [n] goals of the form [pattern η p v φ ψ],
   returning [n]. *)

Ltac2 rec specify_cpattern () : int :=
  lazy_match! goal with
  | [ |- cpattern _ ?cp ?o _ _ ] =>
      (* We simplify terms because of things like coercions. *)
      let cp := Std.eval_hnf cp in
      let o := Std.eval_hnf o in
      match Constr.Unsafe.kind o with
      | Constr.Unsafe.App _ _ =>
          (* If we know what kind of outcome [o] is. *)
          lazy_match! '($cp, $o) with
          | (CVal _, O3Ret _) =>
              apply cpat_CVal; 1
          | (CExc _, O3Throw _) =>
              apply cpat_CExc; 1
          | (CEff _ _, O3Perform _ _) =>
              apply cpat_CEff; 1
          | (COr _ _, _) =>
              eapply cpat_COr;
              let n := Control.focus 1 1 specify_cpattern in
              let m := Control.focus (Int.add n 1) (Int.add n 1) specify_cpattern in
              Int.add n m
          | _ =>
              eapply cpat_mismatch > [ cbn; reflexivity | ]; 0
          end
      | _ =>
          (* If [o] is not a concrete outcome. *)
          lazy_match! cp with
          | CVal _ => eapply cpat_CVal_abst; intros ??; 1
          | CExc _ => eapply cpat_CExc_abst; intros ??; 1
          | CEff _ _ => Control.plus
                         (fun _ => apply cpat_CEff_impossible; 0)
                         (fun _ => eapply cpat_CEff_abst; intros ???; 1)
          | COr _ _ =>
              eapply cpat_COr;
              let n := Control.focus 1 1 specify_cpattern in
              let m := Control.focus (Int.add n 1) (Int.add n 1) specify_cpattern in
              Int.add n m
          end

      end
  end.

Tactic Notation "specify_cpattern" := ltac2:(let _ := specify_cpattern () in ()).

(* -------------------------------------------------------------------------- *)

Ltac2 tauto0 () := ltac1:(tauto).
Ltac2 Notation tauto := tauto0 ().

(* Lemmas to help prune pattern no_match hypotheses. *)

Lemma false_or_r P :
  P ∨ False <-> P.
Proof. tauto. Qed.

Lemma false_or_l P :
  False ∨ P <-> P.
Proof. tauto. Qed.

Lemma true_or_r P :
  P ∨ True <-> True.
Proof. tauto. Qed.

Lemma true_or_l P :
  True ∨ P <-> True.
Proof. tauto. Qed.

Lemma false_and_r P :
  P ∧ False <-> False.
Proof. tauto. Qed.

Lemma false_and_l P :
  False ∧ P <-> False.
Proof. tauto. Qed.

Lemma true_and_r P :
  P ∧ True <-> P.
Proof. tauto. Qed.

Lemma true_and_l P :
  True ∧ P <-> P.
Proof. tauto. Qed.

Ltac2 rewrite_in_hyps (rw : constr) (hyps : ident list) :=
  let hyp_clauses :=
    List.map (fun id => (id, Std.AllOccurrences, Std.InHyp)) hyps
  in
  let clause :=
    { Std.on_hyps := Some hyp_clauses;
      Std.on_concl := Std.NoOccurrences }
  in
  let rw :=
    { Std.rew_orient := Some Std.LTR;
      Std.rew_repeat := Std.RepeatPlus;
      Std.rew_equatn := fun _ => (rw, Std.NoBindings) }
  in
  Std.rewrite false [rw] clause None.

Ltac2 normalize_hyps (hyps : ident list) :=
  let lemma_list :=
    [ 'false_or_r;
      'false_or_l;
      'true_or_r;
      'true_or_l;
      'false_and_r;
      'false_and_l;
      'true_and_r;
      'true_and_l ]
  in
  let thunk_list :=
    List.map (fun l => (fun () => rewrite_in_hyps l hyps)) lemma_list
  in
  repeat (first0 thunk_list).

Ltac2 normalize_hyp (h : ident) :=
  normalize_hyps [h].

Ltac pattern_hook := fail.

(* [pattern_match] expects a goal in the form of a [pattern] or [patterns] judgement.
   It tries to apply all know pattern matching rules. We use [pattern_hook] to
   make this tactic extensible (see its redefinition in examples/splay.v). *)

Ltac2 rec solve_lookup_name () :=
  lazy_match! goal with
  (* If a hypothesis matches the lookup we are trying to do, use it. *)
  | [ h_ident : lookup_name ?η ?c = _ |- lookup_name ?η ?c = _ ] =>
      let h := Control.hyp h_ident in
      rewrite -> $h
  (* Otherwise just try and compute the lookup. *)
  | [ |- lookup_name _ _ = _ ] =>
      progress simpl
  end;
  (* We now have two cases:
     - Using a hypothesis or simplification has produced a goal of
       the form [ret v = ret v].
     - Using a hypothesis has led us to a new lookup *)
  match! goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  end.

Lemma rewrite_bind {A B E} (m : micro A E) (f : A -> micro B E) a :
  m = ret a ->
  bind m f = f a.
Proof. intros ->; reflexivity. Qed.

Ltac2 rec solve_lookup_path () :=
  simpl;
  lazy_match! goal with
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  | [ |- bind (lookup_name ?η ?c) _ = _ ] =>
      erewrite -> (rewrite_bind (lookup_name $η $c)) >
        [ solve_lookup_name () | solve_lookup_path () ]
  | [ |- ret _ = ret _ ] => reflexivity
  end.

Ltac2 rec is_pattern (c : constr) :=
  lazy_match! c with
  | pattern _ _ _ _ _  => true
  | patterns _ _ _ _ _ => true
  | _ => false
  end.


Ltac2 constr_at_ident (h : ident) : constr :=
  let (_, _, x) :=
    List.find (fun (id, _, _) => Ident.equal h id) (Control.hyps ())
  in
  x.

Ltac2 destruct_as (h : ident) (p : Std.or_and_intro_pattern) :=
  let cl :=
        { Std.indcl_arg := Std.ElimOnIdent h;
          Std.indcl_eqn := None;
          Std.indcl_as := Some p;
          Std.indcl_in := None }
  in
  Std.destruct false [cl] None.

Ltac2 rec get_arity (c : constr) :=
  match! c with
  | ?a _ => (Int.add 1 (get_arity a))
  | _ => 0
  end.

Ltac2 rec get_constructor (c : constr) :=
  match! c with
  | ?a _ => get_constructor a
  | _ => match Constr.Unsafe.kind c with
        | Constr.Unsafe.Constructor _ _ => Some c
        | _ => None
        end
  end.

Ltac2 rec destruct_hyp (h : ident) : unit :=
  normalize_hyp h;
  let x := constr_at_ident h in
  lazy_match! x with
  | exists x, _ =>
      (* pat := [ ? h ] *)
      let pat :=
        Std.IntroAndPattern
          [Std.IntroNaming Std.IntroAnonymous;
           Std.IntroNaming (Std.IntroIdentifier h)]
      in
      destruct_as h pat;
      (* Recursive call in case [h] is a nested existential. *)
      destruct_hyp h
  | _ ∧ _ =>
      let h2 := Fresh.in_goal h in
      (* pat := [ h h2 ] *)
      let pat :=
        Std.IntroAndPattern
          [ Std.IntroNaming (Std.IntroIdentifier h);
            Std.IntroNaming (Std.IntroIdentifier h2) ]
      in
      destruct_as h pat;
      destruct_hyp h;
      (* We need [Control.enter] in case [destruct_hyp h] solves the goal. *)
      Control.enter (fun _ => destruct_hyp h2)
  | False =>
      destruct_as h (Std.IntroOrPattern [])
  | _ ∨ _ =>
      (* We only destruct an [or] pattern if we are able to solve one
         of the two generated subgoals. *)
      Control.plus
        (fun _ =>
           (* pat := [ h | h ] *)
           let pat :=
             Std.IntroOrPattern
               [ [ Std.IntroNaming (Std.IntroIdentifier h) ];
                 [ Std.IntroNaming (Std.IntroIdentifier h) ] ]
           in
           destruct_as h pat;
           (* Solve one of the two subgoals. *)
           Control.plus
             (fun _ => Control.focus 1 1 (fun _ => complete (fun _ => destruct_hyp h)))
             (fun _ => Control.focus 2 2 (fun _ => complete (fun _ => destruct_hyp h)));
           destruct_hyp h)
        (fun _ => ())
  | ?a = ?b =>
      (* If the hypothesis is a tautology, remove it. *)
      if Constr.equal a b then clear h else
        (* If the equality is of the form [c ... = ...] *)
      (if (Int.gt (get_arity a) 0) then
         let hyp := Control.hyp h in
         inversion $hyp
       else ());
      subst;
      try ltac1:(congruence)
  | ?a <> ?b =>
      (* An inequality between two terms with different constructors
         is trivial, so we clear such a hypothesis if we find one. *)
      match get_constructor a, get_constructor b with
      | Some c1, Some c2 =>
          if Bool.neg (Constr.equal c1 c2) then Std.clear [h] else ()
      | _, _ => ()
      end
  | _ => try ltac1:(congruence)
  end.

(* We build our own recursor instead of [List.iter] because we don't
   want to keep iterating after solving the goal. *)

Ltac2 destruct_hyps (hs : ident list) :=
  let rec iter :=
    fun f ls =>
      match ls with
      | [] => ()
      | h :: hs =>
          f h; (Control.enter (fun _ => iter f hs))
      end
  in
  iter destruct_hyp hs.

Tactic Notation "destruct_hyp" ident(hyp) :=
  let destr_hyp := ltac2:(hyp |-
                            let hyp := Option.get (Ltac1.to_ident hyp) in
                            destruct_hyp hyp)
  in
  destr_hyp hyp.

Tactic Notation "destruct_hyps" ident_list(hyps) :=
  let destr_hyps := ltac2:(hyps |-
                             let hyps := Option.get (Ltac1.to_list hyps) in
                             let hyps := List.map (fun hyp => Option.get (Ltac1.to_ident hyp)) hyps in
                             destruct_hyps hyps)
  in
  destr_hyps hyps.

(* -------------------------------------------------------------------------- *)

Ltac2 rec do_intros () :=
  lazy_match! goal with
  | [ |- ?h -> ?g ] =>
      (* If [h] is a proposition. *)
      (if Constr.equal (Constr.type h) constr:(Prop) then
         (* Give [h] a nice name. *)
         let match_hyp := Fresh.in_goal ident:(match_hyp) in
         intros $match_hyp;
         (* Try and use the information in [h]. *)
         destruct_hyp match_hyp
       (* If [h] is not a proposition then it is presumably a variable. *)
       else
         intros ?);
      Control.enter do_intros
  | [ |- forall x, _ ] =>
      intros ?; do_intros ()
  | [ |- _ ] => ()
  end.

Ltac2 set_postcondition_to_false () :=
  lazy_match! goal with
  | [ |- pattern _ _ _ _ (?ψ ?arg) ] =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        unify $ψ (fun (_ : $t) => False)
      else ()
  | [ |- pattern _ _ _ _ ?ψ ] =>
      if Constr.is_evar ψ then unify $ψ False else ()
  end.

Ltac2 massage_term (c : constr) :=
  lazy_match! c with
  | ?ψ ?arg  =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        let u := open_constr:(fun x => _) in
        unify $ψ $u
      else ()
  | _ => ()
  end.

(* [patterns] expects a goal of the form [patterns ...] and either
   - reduces to a [pattern ...] with [pats_PCons_unary],
   - solves the goal with [pats_PNil]. *)

Ltac2 patterns () :=
  lazy_match! goal with
  | [ |- patterns _ (_ :: _) _ _ ?ψ ] =>
      (* If [Ψ] is an evar, [pats_PCons_unary] instantiates it as
         [Ψ := ?Ψ1 ∨ ?Ψ2]. Currently (09/2024), the only other case
         is that [Ψ] is already instantiated to [False]. *)
      if (Constr.equal ψ constr:(False)) then
        eapply pats_PCons_unary_false
      else
        eapply pats_PCons_unary
  | [ |- patterns _ [] _ _ ?ψ ] =>
      (* If [Ψ] is an evar then we instantiate it to [False], otherwise we
         use [pats_consequence_psi] and the fact that [∀ P, ⊥ -> P]. *)
      if (Constr.is_evar ψ) then
        eapply pats_PNil
      else
        eapply pats_consequence_psi > [ eapply pats_PNil | intros [] ]
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [patterns η ps vs φ ψ]")))
  end.

(* [pattern_match_aux] expects a goal of the form [patterns ...] or
   [pattern ...] and progresses by matching the pattern(s) to the
   variable(s). This is done by applying the appropriate lemma for
   each pattern, for example [pat_PInt] if the pattern is a [PInt]. *)

(* If we don't match on any known pattern, we try to use an extensible
   Ltac1 tactic called [pattern_hook].
   This allows users to extend pattern matching to new data structures. *)

Ltac2 rec pattern_match_aux () :=
  (* [continue_matching] is used after solving one pattern. It
     introduces new information before deciding whether to continue
     pattern-matching or whether we are done. *)
  let continue_matching :=
    fun _ => do_intros ();
          (* Use [Control.enter] here because [do_intros] may solve the goal. *)
          Control.enter (fun _ =>
          if is_pattern (Control.goal ()) then pattern_match_aux () else ())
  in
  lazy_match! goal with
  | [ |- patterns _ _ _ _ _ ] => patterns (); continue_matching ()
  | [ |- pattern _ ?p _ _ ?ψ ] =>
      (* [massage_term] is black magic to help Rocq's unification engine. *)
      massage_term ψ;
      match! p with
      | PVar _ =>
          (* We assume that a [PVar] pattern never fails. *)
          set_postcondition_to_false ();
          (* It may be the case that [pat_PVar2] can entirely solve the goal. *)
          Control.plus
            (fun _ => eapply pat_PVar2)
            (fun _ => eapply pat_PVar;
                   continue_matching ())
      | PInt _ =>
          eapply pat_PInt;
          (* First solve the encoding to ensure that all values are instantiated. *)
          Control.focus 3 3 (fun _ => solve [ ltac1:(encode) ]);
          Control.extend [] (fun _ => ltac1:(representable)) [continue_matching]
      | pNil =>
          eapply pat_pNil > [ solve [ ltac1:(encode) ]
                            | continue_matching () ]
      | PConstant "[]" =>
          eapply pat_pNil > [ solve [ ltac1:(encode) ]
                            | continue_matching () ]
      | pCons _ _ =>
          eapply pat_pCons > [ solve [ ltac1:(encode) ]
                             | continue_matching () ]
      | PData "::" _ =>
          eapply pat_pCons > [ solve [ ltac1:(encode) ]
                             | continue_matching () ]
      | PXData _ _ =>
          Control.plus
            (fun _ => eapply pat_PXData_eq > [ solve_lookup_path () | pattern_match_aux () ])
            (fun _ => eapply pat_PXData_neq > [ solve_lookup_path () | auto ])
      | PConstant _ =>
          Control.plus
            (fun _ => eapply pat_PConst_eq; continue_matching ())
            (fun _ => eapply pat_PConst_neq > [ ltac1:(congruence) | try ltac1:(tauto) ])
      | POr _ _ =>
          apply pat_POr > [ pattern_match_aux () | pattern_match_aux () ]
      | PTuple _ =>
          ltac1:(pat_PTuple); continue_matching ()
      | PAlias _ _ =>
          apply pat_PAlias; pattern_match_aux ()
      | PAny =>
          apply pat_PAny; continue_matching ()
      (* If we haven't matched any known pattern, try and use the hook. *)
      | _ =>
          ltac1:(pattern_hook); continue_matching ()
      end
  end.

(* Assuming a goal of the form [⊢ pattern(s) η p v ?φ ?ψ], the
   [pattern_match] tactic tries to reduce the goal to [⊢ φ] while
   elaborating the failure postcondition [Ψ]. *)

Ltac2 pattern_match0 () :=
  Control.enter (fun _ =>
  lazy_match! goal with
  | [ |- pattern _ ?p _ _ ?ψ ] => pattern_match_aux ()
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pattern η p v φ ψ]")))
  end).

Ltac2 Notation "pattern_match" := pattern_match0 ().
Tactic Notation "pattern_match" := ltac2:(pattern_match).

(* -------------------------------------------------------------------------- *)

(* [resolve_no_match] attempts to prove by contradiction that
   not matching on any branch of a pattern match is impossible.e Its
   tactics implicitly target the "no_match" hypotheses that are
   generated by [pure_match_branches] and instantiated by [pattern_match]. *)

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
Local Ltac elim_conj :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac resolve_no_match :=
  repeat first
    [ strip_disjunction
    | elim_exists
    | elim_conj
    | congruence
    | remove_tauto
    | subst_eq
    | inject_eq ].

Ltac2 first tac := Control.extend [tac] (fun _ => ()) [].
Ltac2 last tac := Control.extend [] (fun _ => ()) [tac].

(* -------------------------------------------------------------------------- *)

(* [pure_match_branches] expects a goal of the form
   [pure_match _ _ bs _] where [bs] is a list of n branches. It
   successively applies [pure_match_cons], creating n subgoals of the
   form [pattern _ _ _ (λ n', pure (eval η' _) ##_ ⊥) _] and one subgoal of
   the form [False]. *)

Ltac2 rec pure_match_branches0 (hyps : ident list) :=
  lazy_match! goal with
  | [ |- pure_match _ ?bs _ _ ] =>
      (* Match on [bs] to decide whether to apply [pure_match_cons]
         or [pure_match_nil]. *)
      lazy_match! (Std.eval_hnf bs) with
      | _ :: _ =>
          (* [pure_match_cons] produces two subgoals :
             - one of the form [cpattern ...]
             - one of the form [Ψ -> pure_match ...] *)
          eapply pure_match_cons;
          (* In the first subgoal, apply the [specify_cpattern] tactic
             followed by the [pattern_match] tactic. *)
          Control.focus 1 1
            (fun _ =>
               (* [specify_cpattern ()] introduces m subgoals. *)
               let m := specify_cpattern () in
               if (Int.gt m 0) then
                 Control.focus 1 m pattern_match0
               else ());
          (* In the second subgoal, introduce the new hypothesis [ψ]
             and recursively apply [pure_match_branches0]. *)
          last
            (fun _ =>
               let no_match := Fresh.in_goal @no_match in
               intros $no_match;
               (* Simplify the hypotheses we've generated so far. *)
               destruct_hyps (no_match :: hyps);
               (* Filter to only keep the hypotheses which still exist
                  after simplification. *)
               let remaining_hyps :=
                 List.filter (fun id => Control.plus
                                       (fun _ => let _ := Control.hyp id in true)
                                       (fun _ => false)) (no_match :: hyps)
               in
               (* We use [Control.enter] so the tactic doesn't fail in
                  the case where the goal was solved by the hypothesis
                  simplification. *)
               Control.enter (fun _ => pure_match_branches0 (remaining_hyps)))
      | [] =>
          (* We have to show that every pattern match is exhaustive.
             If we reach this point, then we can assume that an early
             use of [destruct_hyps] was not powerful enough to solve
             this goal. We thus use the more brute-force
             [resolve_no_match] tactic. *)
          eapply pure_match_nil; ltac1:(resolve_no_match)
      end
  | [ |- ?g ] =>
      let () := Message.print (Message.of_constr g) in
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pure_match η bs o φ]")))
  end.

Ltac2 pure_match0 () := pure_match_branches0 [].

Ltac2 Notation "pure_match" := pure_match0 ().
Tactic Notation "pure_match" := ltac2:(pure_match).
