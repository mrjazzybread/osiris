From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp.

(* -------------------------------------------------------------------------- *)

(* The judgement [simp m (ret a)] means that the computation [m] is pure,
   therefore terminates, and produces the result [a]. *)

(* We do not give a Notation or a Definition for this judgement; we
   prefer to keep it in this form. *)

(* [simp m (ret a)] is equivalent to a Hoare logic judgement [totalv m _]
   whose postcondition is an equality [λ a', a = a']. *)

Lemma simp_totalv {A} m (a : A) :
  simp m (ret a) ↔
  totalv m (λ a', a = a').
Proof.
  split.
  { eauto using totalv_simp, totalv_ret. }
  { intros. destruct_total a'. congruence. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The judgement [simp m (ret #a)] means that the computation [m] is pure,
   therefore terminates, and produces the OCaml value [#a], that is, the
   encoding of the logical value [a]. It requires a type class instance
   `{Encode A}. *)

(* We do not give a Notation or a Definition for this judgement; we
   prefer to keep it in this form. *)

(* [simp m (ret #a)] is equivalent to a Hoare logic judgement [pure m _]
   whose postcondition is an equality [λ a', a = a']. *)

Lemma simp_pure `{Encode A} m (a : A) :
  simp m (ret #a) ↔
  pure m (λ a', a = a').
Proof.
  rewrite simp_totalv. rewrite pure_totalv.
  split; intro; (eapply totalv_consequence; [ eassumption | simpl ]).
  { eauto. }
  { intros a' (? & ? & ?). subst. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* If [z] is representable and [z ≠ 0] then the runtime check
   performed by [check_div_by_zero (repr z)] must succeed. *)

Lemma simp_check_div_by_zero z :
  representable z →
  z ≠ 0 →
  simp (check_div_by_zero (repr z)) (ret ()).
Proof.
  intros.
  unfold check_div_by_zero.
  change int.zero with (repr 0).
  rewrite eq_repr_repr by representable.
  case_eq (z =? 0); [ rewrite Z.eqb_eq | rewrite Z.eqb_neq ]; intro.
  { tauto. }
  { simp. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Reasoning rules for [simp (eval _ _) (ret _)], that is,
   for pure expressions with a deterministic postcondition. *)

(* A consequence rule. *)

Lemma simp_consequence A (m : micro A) a' a :
  simp m (ret a') →
  a = a' →
  simp m (ret a).
Proof.
  intros. subst. eauto.
Qed.

(* Paths. *)

Lemma simp_eval_path η π v :
  lookup_path η π = ret v →
  simp (eval η (EPath π)) (ret v).
Proof.
  intros Hlookup. simpl. rewrite Hlookup. simp.
Qed.

(* Tuples. *)

(* This lemma is general. *)

(* TODO avoid [ForallEV] just by showing nil and cons lemmas;
   offer tactic analogous to [pats]. *)

Lemma simp_evals η :
  ∀ es vs,
  ForallEV (λ e v, simp (eval η e) (ret v)) es vs →
  simp (evals η es) (ret vs).
Proof.
  induction 1; simpl; simp. (* nice and sweet! *)
Qed.

(* This lemma is general but does not mention the encoding function,
   because we do not currently have a general definition of the
   encoding of n-tuples. *)

(* TODO can we give a generic definition of the encoding of n-tuples? *)

Lemma simp_eval_tuple η es vs :
  ForallEV (λ e v, simp (eval η e) (ret v)) es vs →
  simp (eval η (ETuple es)) (ret (VTuple vs)).
Proof.
  intros H. apply simp_evals in H. simp.
Qed.

(* This special case at arity 2 does mention the encoding function. *)

(* TODO can we give a similar lemma at arity [n]? *)

Lemma simp_eval_pair `{Encode A1, Encode A2} η e1 e2 (a1 : A1) (a2 : A2) :
  simp (eval η e1) (ret #a1) →
  simp (eval η e2) (ret #a2) →
  simp (eval η (EPair e1 e2)) (ret #(a1, a2)).
Proof.
  intros. simp. (* wow *)
Qed.

(* Integer literals. *)

Lemma simp_eval_int η (z : Z) :
  simp (eval η (EInt z)) (ret #z).
Proof.
  simp.
Qed.

Lemma simp_eval_max_int η :
  simp (eval η EMaxInt) (ret #max_signed).
Proof.
  simp.
Qed.

Lemma simp_eval_min_int η :
  simp (eval η EMinInt) (ret #min_signed).
Proof.
  simp.
Qed.

(* Primitive arithmetic operations. *)

Lemma simp_eval_add η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntAdd e1 e2)) (ret #(z1 + z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_sub η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntSub e1 e2)) (ret #(z1 - z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_mul η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntMul e1 e2)) (ret #(z1 * z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_div η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  representable z1 →
  representable z2 →
  z2 ≠ 0 →
  simp (eval η (EIntDiv e1 e2)) (ret #(z1 ÷ z2)).
Proof.
  intros ? ? Hrz1 Hrz2 Hnnz2. simpl. unfold as_int. simp.
  specialize (simp_check_div_by_zero _ Hrz2 Hnnz2); intro.
  simp.
Qed.

(* Primitive operations on Booleans. *)

(* The logical model of an OCaml Boolean value can be a Coq Boolean or
   a Coq proposition, so we give two specifications to each operation. *)

Lemma simp_eval_negb η e (b : bool) :
  simp (eval η e) (ret #b) →
  simp (eval η (EBoolNeg e)) (ret #(negb b)).
Proof.
  intros. simpl. unfold as_bool. simp.
Qed.

Lemma simp_eval_not η e (P : Prop) :
  simp (eval η e) (ret #P) →
  simp (eval η (EBoolNeg e)) (ret #(¬P)).
Proof.
  intros. simpl. unfold as_bool. rewrite truth_neg. simp.
Qed.

(* Local definitions. *)

(* TODO one binding only, for now *)

Lemma simp_eval_let η x e1 e2 v1 m :
  simp (eval η e1) (ret v1) →
  (let η' := EnvCons x v1 η in simp (eval η' e2) m) →
  simp (eval η (ELet1Var x e1 e2)) m.
Proof.
  intros. simp.
Qed.

(* Conditionals. *)

(* This statement uses the encoding of Coq propositions as Booleans. *)

Lemma simp_eval_ifthenelse η e e1 e2 (P : Prop) v :
  simp (eval η e) (ret #P) →
  ( P → simp (eval η e1) (ret v)) →
  (¬P → simp (eval η e2) (ret v)) →
  simp (eval η (EIfThenElse e e1 e2)) (ret v).
Proof.
  simpl. unfold as_bool. (* [simp] cannot deal with [as_bool] *)
  intros He He1 He2.
  generalize (truth_elim P). generalize dependent (truth P).
  intros [|] He.
  { intros HP. specialize (He1 HP). simp. }
  { intros HP. specialize (He2 HP). simp. }
Qed.

Lemma simp_eval_ifthenelse_pure
  `{Encode A} η e e1 e2 (P : Prop) (ψ : A → Prop)
:
  simp (eval η e) (ret #P) →
  ( P → pure (eval η e1) ψ) →
  (¬P → pure (eval η e2) ψ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ.
Proof.
  simpl. unfold as_bool. (* [simp] cannot deal with [as_bool] *)
  intros.
  generalize (truth_elim P). generalize dependent (truth P).
  intros [|] ? ?; solve [ eapply pure_simp; [ simp | eauto ]].
Qed.

(* Runtime assertions. *)

Lemma simp_eval_assert η e :
  simp (eval η e) (ret #True) →
  simp (eval η (EAssert e)) (ret #()).
Proof.
  simpl encode. rewrite truth_True. eauto using advance_SimpEvalEAssert.
Qed.

(* -------------------------------------------------------------------------- *)

(* Reasoning rules for [pure (eval _ _) _], that is,
   for pure expressions with an arbitrary postcondition. *)

(* The following lemmas are obtained as consequences of the previous
   lemmas, so [eval] and its auxiliary functions can be made opaque. *)

Local Opaque eval as_bool.

(* This hint is used in the proofs that follow. *)

Local Hint Unfold pure : core.

(* Tuples. *)

(* A special case at arity 2. *)

(* TODO can we give a similar lemma at arity [n]? *)

Lemma pure_eval_pair `{Encode A1, Encode A2} η e1 e2
  (φ1 : A1 → Prop) (φ2 : A2 → Prop) (ψ : A1 * A2 → Prop)
:
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → ψ (a1, a2)) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. destruct_pure a2. destruct_pure a1.
  eapply pure_simp; [ simp |].
  eauto using pure_ret with encode.
Qed.

(* Function applications. *)

Lemma pure_eval_app `{Encode A, Encode B} η e1 e2
  (φ1 : val → Prop) (φ2 : A → Prop) (ψ : B → Prop)
:
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ v1 v2, φ1 v1 → φ2 v2 → pure (call v1 #v2) ψ) →
  pure (eval η (EApp e1 e2)) ψ.
Proof.
  intros. destruct_pure a2. destruct_pure v1.
  eapply pure_simp; [ simp | eauto ].
Qed.

(* Primitive arithmetic operations. *)

Lemma pure_eval_add η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 + z2)) →
  pure (eval η (EIntAdd e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_add.
Qed.

Lemma pure_eval_sub η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 - z2)) →
  pure (eval η (EIntSub e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_sub.
Qed.

Lemma pure_eval_mul η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 * z2)) →
  pure (eval η (EIntMul e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_mul.
Qed.

Lemma pure_eval_div η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → representable z2) →
  (∀ z2, φ2 z2 → z2 ≠ 0) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 ÷ z2)) →
  pure (eval η (EIntDiv e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 10 using simp_eval_div.
Qed.

(* Primitive operations on Booleans. *)

Lemma pure_eval_negb η e (φ ψ : bool → Prop) :
  pure (eval η e) φ →
  (∀ b, φ b → ψ (negb b)) →
  pure (eval η (EBoolNeg e)) ψ.
Proof.
  intros. destruct_pure b. eauto 8 using simp_eval_negb.
Qed.

Lemma pure_eval_not η e (φ ψ : Prop → Prop) :
  pure (eval η e) φ →
  (∀ P, φ P → ψ (¬P)) →
  pure (eval η (EBoolNeg e)) ψ.
Proof.
  intros. destruct_pure b. eauto 8 using simp_eval_not.
Qed.

(* Local definitions. *)

(* TODO one binding only, for now *)

Lemma pure_eval_let' `{Encode A1, Encode B} η x e1 e
  (a1 : A1) (ψ : B → Prop)
:
  simp (eval η e1) (ret #a1) →
  pure (eval (EnvCons x #a1 η) e) ψ →
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros. destruct_pure b. eauto using simp_eval_let.
Qed.

Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop)
:
  pure (eval η e1) φ1 →
  (∀ a1, φ1 a1 → pure (eval (EnvCons x #a1 η) e) ψ) →
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros. destruct_pure a1. eauto using pure_eval_let'.
Qed.

(* Conditionals. *)

Lemma pure_eval_ifthenelse `{Encode A} η e e1 e2 φ (ψ : A → Prop) :
  pure (eval η e) φ →
  (φ true  → pure (eval η e1) ψ) →
  (φ false → pure (eval η e2) ψ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ.
Proof.
  intros. destruct_pure b.
  eapply simp_eval_ifthenelse_pure with (P := Is_true b).
  + simpl encode in *. rewrite truth_Is_true. assumption.
  + intros hb. destruct b; simpl in hb; tauto.
  + intros hb. destruct b; simpl in hb; tauto.
Qed.

(* Runtime assertions. *)

Lemma pure_eval_assert η e :
  simp (eval η e) (ret #True) →
  pure (eval η (EAssert e)) (λ (_ : unit), True).
Proof.
  eauto using simp_eval_assert.
Qed.

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

Implicit Type φ : env → Prop.
Implicit Type ψ : Prop.

(* The judgement [pat η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by raising [Next]) and guarantees [ψ]. *)

Definition pat η p v φ ψ :=
  total (extend η p v) φ ψ.

Definition pats η ps vs φ ψ :=
  total (extends η ps vs) φ ψ.

(* A consequence rule. *)

Lemma pat_consequence η p v φ φ' ψ ψ' :
  pat η p v φ ψ →
  (∀ η, φ η → φ' η) →
  (ψ → ψ') →
  pat η p v φ' ψ'.
Proof.
  unfold pat. eauto using total_consequence.
Qed.

Lemma pat_consequence_psi η p v φ ψ ψ' :
  pat η p v φ ψ →
  (ψ → ψ') →
  pat η p v φ ψ'.
Proof.
  unfold pat. eauto using total_consequence.
Qed.

(* Syntax-directed reasoning rules for the auxiliary judgement [pats]. *)

Lemma pats_PNil η φ :
  φ η →
  pats η PNil VNil φ False.
Proof.
  unfold pats. simpl. eauto using total_ret.
Qed.

Lemma pats_PCons_unary η p ps v vs φ ψ :
  pat η p v (λ η, pats η ps vs φ ψ) ψ →
  pats η (PCons p ps) (VCons v vs) φ ψ.
    (* a simple statement (unused) *)
Proof.
  unfold pats, pat. intro Hp. simpl.
  eapply total_bind; [ eapply Hp | simpl ]. intros η' Hps.
  rewrite bind_ret_right. eauto.
Qed.

Lemma pats_PCons η p ps v vs φ' φ ψ1 ψ2 :
  pat η p v φ' ψ1 →
  (∀ η, φ' η → pats η ps vs φ ψ2) →
  pats η (PCons p ps) (VCons v vs) φ (ψ1 ∨ ψ2).
    (* a more elaborate statement, where [ψ1] and [ψ2] are unconstrained,
       and where a disjunction is explicitly constructed -- see below. *)
Proof.
  unfold pats, pat. intros. simpl.
  eapply total_bind; [ eauto using total_consequence | simpl ].
  intros η' ?.
  rewrite bind_ret_right.
  eauto using total_consequence.
Qed.

Ltac pats :=
  repeat first [
    eapply pats_PNil; [ eauto ]
  | eapply pats_PCons; [ eauto | simpl; intros ]
  ].

(* Syntax-directed reasoning rules for the judgement [pat]. *)

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
  pat η PAny v φ False.
Proof.
  unfold pat. simpl. eauto using total_ret.
Qed.

Lemma pat_PVar η x v φ :
  (let η := EnvCons x v η in φ η) →
  pat η (PVar x) v φ False.
Proof.
  unfold pat. simpl. eauto using total_ret.
Qed.

Lemma pat_PAlias η p x v φ ψ :
  pat η p v (λ η, let η := EnvCons x v η in φ η) ψ →
  pat η (PAlias p x) v φ ψ.
Proof.
  unfold pat. simpl. intros Hp.
  eapply total_bind; [ eapply Hp | simpl ]. intros η' ?.
  eauto using total_ret.
Qed.

Lemma pat_POr η p1 p2 v φ ψ1 ψ2 :
  pat η p1 v φ ψ1 →
  pat η p2 v φ ψ2 →
  pat η (POr p1 p2) v φ (ψ1 ∧ ψ2).
    (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
       disjunction pattern to fail, both sides must fail. *)
Proof.
  unfold pat; intros Hp1 Hp2. simpl.
  eauto using total_orelse, total_consequence.
Qed.

Lemma pat_PUnit η v φ :
  φ η →
  v = #() →
  pat η PUnit v φ False.
Proof.
  unfold pat. intros. subst. simpl. eauto using total_ret.
Qed.

Lemma pat_PTuple η ps vs φ ψ :
  pats η ps vs φ ψ →
  pat η (PTuple ps) (VTuple vs) φ ψ.
Proof.
  unfold pats, pat. simpl. eauto.
Qed.

Lemma pat_PData η c p c' v φ ψ :
  (c = c' → pat η p v φ ψ) →
  pat η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
    (* This form is useful when the truth of the equality [c = c']
       is not statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; eauto using total_next, total_consequence.
Qed.

Lemma pat_PData_eq η c p v φ ψ :
  pat η p v φ ψ →
  pat η (PData c p) (VData c v) φ ψ.
    (* This form is useful when [c = c'] is statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; solve [ eauto using total_next | tauto ].
Qed.

Lemma pat_PData_neq η c p c' v φ :
  c ≠ c' →
  pat η (PData c p) (VData c' v) φ True.
    (* This form is useful when [c ≠ c'] is statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; solve [ eauto using total_next | tauto ].
Qed.

Lemma pat_pNil `{Encode A} η v (xs : list A) φ :
  v = #xs →
  (xs = [] → φ η) →
  pat η pNil v φ (xs ≠ []).
Proof.
  intros; subst.
  destruct xs as [| x xs ]; eapply pat_consequence_psi.
  { eapply pat_PData_eq. eapply pat_PTuple. pats. }
  { eauto. }
  { eapply pat_PData_neq. eauto. }
  { eauto. }
Qed.

Lemma pat_pCons `{Encode A} η p1 p2 v (xs : list A) φ ψ :
  v = #xs →
  (∀ x xs',
     xs = x :: xs' →
     pats η (PCons p1 (PCons p2 PNil)) (VCons #x (VCons #xs' VNil)) φ ψ
  ) →
  pat η (pCons p1 p2) v φ (xs = [] ∨ ψ).
Proof.
  intros ? Hpp; subst.
  destruct xs as [| x xs ]; eapply pat_consequence_psi.
  { eapply pat_PData_neq. eauto. }
  { tauto. }
  { specialize (Hpp x xs eq_refl).
    eapply pat_PData_eq.
    rewrite ?encode_list_is_encode. (* optional, but helpful *)
    eapply pat_PTuple. eauto. }
  { eauto. }
Qed.

Lemma pat_false η v (P : Prop) φ :
  v = #P →
  (¬P → φ η) →
  pat η (PConstant "false") v φ P.
Proof.
  intros; subst.
  eapply pat_consequence_psi.
  { (* The definition of [#] at type [Prop] involves [VBool], which
       itself involves [BoolConstructor]. *)
    change "false" with (BoolConstructor false).
    eapply pat_PData.
    intro Heq. symmetry in Heq.
    apply BoolConstructor_injective, truth_false_elim in Heq.
    pats. }
  { intros [| Hneq ]; [ tauto |]. apply not_eq_sym in Hneq.
    apply BoolConstructor_congruent_contrapositive in Hneq.
    apply bool_neq in Hneq.
    apply truth_true_elim in Hneq.
    tauto. }
Qed.

Lemma pat_true η v (P : Prop) φ :
  v = #P →
  (P → φ η) →
  pat η (PConstant "true") v φ (¬P).
Proof.
  intros; subst.
  eapply pat_consequence_psi.
  { change "true" with (BoolConstructor true).
    eapply pat_PData.
    intro Heq. symmetry in Heq.
    apply BoolConstructor_injective, truth_true_elim in Heq.
    pats. }
  { intros [| Hneq ]; [ tauto |]. apply not_eq_sym in Hneq.
    apply BoolConstructor_congruent_contrapositive in Hneq.
    apply bool_neq in Hneq.
    apply truth_false_elim in Hneq.
    tauto. }
Qed.
