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

Lemma simp_eval_tuple' η es vs :
  simp (evals η es) (ret vs) →
  simp (eval η (ETuple es)) (ret (VTuple vs)).
Proof.
  intros. simp.
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

(* Sequence *)

Lemma simp_eval_seq η e1 e2 v :
  (exists a, simp (eval η e1) (ret a)) ->
  simp (eval η e2) (ret v) ->
  simp (eval η (ESeq e1 e2)) (ret v).
Proof.
  intros [??] ?.
  eauto using prove_simp_bind.
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

Lemma pure_eval_pair `{Encode A1, Encode A2} η e1 e2 (ψ : A1 * A2 → Prop) :
  pure (eval η e1) (λ a1 : A1, pure (eval η e2) (λ a2 : A2, ψ (a1, a2))) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. destruct_pure a1. destruct_pure a2.
  eapply pure_simp; [ simp |].
  eauto using pure_ret with encode.
Qed.

Lemma pure_eval_pair_val η e1 e2 (ψ : val → Prop) :
  pure (eval η e1) (λ a1 : val, pure (eval η e2) (λ a2 : val, ψ (VPair a1 a2))) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. destruct_pure a1. destruct_pure a2.
  eapply pure_simp; [ simp |].
  eauto using pure_ret with encode.
Qed.


Lemma pure_eval_pair_conseq `{Encode A1, Encode A2} η e1 e2
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

Lemma pure_eval_tuple η es vs (ψ : val -> Prop) :
  simp (evals η es) (ret vs) ->
  ψ (VTuple vs) ->
  pure (eval η (ETuple es)) ψ.
Proof.
  intros.
  eapply pure_simp. simp.
  eapply pure_ret; eauto.
Qed.

(* Function applications. *)

Lemma pure_eval_app `{Encode A} η e1 e2 (ψ : A → Prop) :
  pure (eval η e1) (λ f : val, pure (eval η e2) (λ e : val, pure (call f e) ψ)) →
  pure (eval η (EApp e1 e2)) ψ.
Proof.
  intros. destruct_pure a2. destruct_pure v1.
  eapply pure_simp; [ simp | eauto ].
Qed.

Lemma pure_eval_app_conseq `{Encode A, Encode B} η e1 e2
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
  
Lemma simp_eval_let_pair' p1 p2 e1 e2 m v1 v2 η θ :
  simp (eval η e1) (ret (VPair v1 v2)) ->
  simp (δ ← extend EnvNil p1 v1;
        extend δ p2 v2) (ret θ) ->
  simp (eval (concat θ η) e2) m ->
  simp (eval η (ELet1 (PPair p1 p2) e1 e2)) m.
Proof.
  intros. simp.
  eapply prove_simp_try; last eassumption.
  apply invert_simp_bind_ret in H0 as (δ & Hnil & Hext).
  eapply prove_simp_bind; first eassumption.
  rewrite bind_bind.
  simpl. by rewrite bind_ret_right.
Qed.  

Lemma pure_eval_let_pair' `{Encode X} p1 p2 e1 e2 v1 v2 η θ (ψ : X -> Prop) :
  simp (eval η e1) (ret (VPair v1 v2)) ->
  simp (δ ← extend EnvNil p1 v1;
        extend δ p2 v2) (ret θ) ->
  pure (eval (concat θ η) e2) ψ ->
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ.
Proof.
  intros. destruct_pure y. eauto using simp_eval_let_pair'.
Qed.

Lemma pure_eval_let_pair `{Encode X} p1 p2 e1 e2 η (ψ : X -> Prop) :
  pure (eval η e1) (λ v : val,
        match v with
        | VTuple (VCons v1 (VCons v2 VNil)) =>
            pure (
                δ ← extend EnvNil p1 v1;
                θ ← extend δ p2 v2;
                eval (concat θ η) e2) ψ
        | _ => False
        end) ->
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ.
Proof.
  intros (v & Hv & Hpure).
  destruct v; try done.
  do 3 (destruct vs; try done). simpl in Hv.
  destruct Hpure as (x & Hsimp & Hpost).
  eapply invert_simp_bind_ret in Hsimp as (δ & Hv1 & Hsimp).
  eapply invert_simp_bind_ret in Hsimp as (θ & Hv2 & Hx).
  eapply pure_eval_let_pair'; eauto.
  eapply prove_simp_bind; eauto.
Qed.
  
Lemma pure_eval_let' `{Encode A1, Encode B} η x e1 e
  (a1 : A1) (ψ : B → Prop) :
  simp (eval η e1) (ret #a1) ->
  pure (eval (EnvCons x #a1 η) e) ψ ->
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros. destruct_pure b. eauto using simp_eval_let.
Qed.

Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop) :
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

(* Sequencing of pure computations. *)

Lemma pure_eval_seq' `{Encode A} η e1 e2 a (ψ : A -> Prop) :
  simp (eval η e1) (ret a) ->
  pure (eval η e2) ψ ->
  pure (eval η (ESeq e1 e2)) ψ.
Proof.
  intros.
  destruct_pure b.
  eapply pure_simp. { apply simp_eval_seq; eauto. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_seq `{Encode A} `{Encode B} η e1 e2 (ψ : A -> Prop) :
  pure (eval η e1) (λ _ : B, True) ->
  pure (eval η e2) ψ ->
  pure (eval η (ESeq e1 e2)) ψ.
Proof.
  intros. destruct_pure a. destruct_pure b.
  eapply pure_simp. { apply simp_eval_seq; eauto. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_mexpr_struct (η δ whatenv : env) items (ψ : val -> Prop) :
  simp (eval_sitems (η, EnvNil) items) (ret (whatenv, δ)) ->
  ψ (VStruct δ) ->
  pure (eval_mexpr η (MStruct items)) ψ.
Proof.
  intros.  
  eapply pure_simp.
  { eapply prove_simp_bind; [eauto | apply SimpReflexive]. } 
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_mexpr_coerc η me c v (ψ : val -> Prop):
  simp (eval_mexpr η me) (ret v) ->
  pure (coerce c v) ψ ->
  pure (eval_mexpr η (MCoercion me c)) ψ.
Proof.
  intros.
  destruct_pure cv.
  eapply pure_simp.
  { eapply prove_simp_bind; eauto. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_path `{Encode A} η π (ψ : A -> Prop) :
  pure (lookup_path η π) ψ ->
  pure (eval η (EPath π)) ψ.
Proof.
  intros. destruct_pure v.
  eapply pure_simp.
  rewrite eval_eval'; eauto.
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_ret_concat `{Encode A} e δ η (ψ : A -> Prop) :
  pure (eval (concat δ η) e) ψ ->
  pure (θ ← ret_concat δ η;
        eval θ e) ψ.
Proof.
  tauto.
Qed.

Lemma simp_eval_const η c :
  simp (eval η (EConstant c)) (ret (VConstant c)).
Proof.
  do 2 (rewrite eval_eval'; simpl).
  done.
Qed.

Lemma pure_eval_const `{Encode X} η c x (ψ : X -> Prop) :
  VConstant c = #x ->
  ψ x ->
  pure (eval η (EConstant c)) ψ.
Proof.
  intros.
  eapply pure_simp; first apply simp_eval_const.
  eauto using pure_ret.
Qed.

Lemma simp_eval_data η c e v :
  simp (eval η e) (ret v) ->
  simp (eval η (EData c e)) (ret (VData c v)).
Proof.
  intros.
  rewrite eval_eval'; simpl.
  eapply prove_simp_bind; first eassumption.
  apply SimpReflexive.
Qed.

Lemma pure_eval_data `{Encode X} η c e (ψ : X -> Prop) :
  pure (eval η e) (λ y : val, pure (ret (VData c y)) ψ) ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros. destruct_pure v. destruct_pure x.
  eapply pure_simp; [eauto using simp_eval_data |].
  eapply pure_ret; eauto.
  rewrite <- solve_encode_val.
  by apply simp_ret_ret.
Qed.

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

Section Pattern.
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

Lemma pats_consequence_psi η p v φ ψ ψ' :
  pats η p v φ ψ →
  (ψ → ψ') →
  pats η p v φ ψ'.
Proof.
  unfold pats. eauto using total_consequence.
Qed.

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

Lemma pats_PCons η p ps v vs φ' φ ψ ψ1 ψ2 :
  pat η p v φ' ψ1 →
  (∀ η, φ' η → pats η ps vs φ ψ2) →
  (ψ1 \/ ψ2 -> ψ) ->
  pats η (PCons p ps) (VCons v vs) φ ψ.
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
  pat η (pCons p1 p2) v φ (xs = [] \/ ψ).
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

End Pattern.

Definition pure_match `{Encode A} (η : env) (v : val) bs (ψ : A -> Prop) :=
  pure (eval_match η v bs) ψ.
Arguments pure_match {A} {H} _ _ _ _.

Lemma pure_eval_match' `{Encode A, Encode B} η e bs (ψ : A -> Prop) :
  pure (eval η e) (λ v : B, pure_match η #v bs ψ) ->
  pure (eval η (EMatch e bs)) ψ.
Proof.
  intros. unfold pure_match in *.
  destruct_pure v. destruct_pure x.
  eapply pure_simp.
  { rewrite eval_eval'; simpl.
    eapply prove_simp_bind; eauto. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_match `{Encode A, Encode B} η e bs (φ : A -> Prop) (ψ : B -> Prop) :
  pure (eval η e) φ ->
  (forall a, φ a -> pure_match η #a bs ψ) ->
  pure (eval η (EMatch e bs)) ψ.
Proof.
  intros.
  eapply pure_eval_match'.
  eapply pure_consequence; eauto.
Qed.

Lemma destruct_bind_ret {A B} (m : micro A) (f : A -> micro B) b :
  bind m f = ret b ->
  exists c, m = ret c /\ f c = ret b.
Proof.
  destruct m; simpl; try discriminate 1.
  eauto.
Qed.

Lemma destruct_bind_next {A B} (m : micro A) (f : A -> micro B) :
  bind m f = next ->
  m = next \/ exists c, m = ret c /\ f c = next.
Proof.
  destruct m; simpl; try discriminate 1.
  right; eauto.
  left; done.
Qed.

Ltac elim_existT :=
  match goal with
  | H : existT _ _ = existT _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H
  end.

Lemma destruct_bind_stop {A X Y} (m : micro A) (f : A -> micro A)
  c (x : X) (k : Y -> micro A) ko :
  bind m f = Stop c x k ko ->
  (exists km kom, m = Stop c x km kom) \/
  exists a, m = ret a /\ f a = Stop c x k ko.
Proof.
  destruct m; simpl; try discriminate 1. { eauto. }
  intros H. injection H; intros.
  left.
  subst Y0; subst X0. repeat (elim_existT). subst c0; subst x0.
  eauto.
Qed.

Lemma destruct_bind_par {A A1 A2} m (m1 : micro A1) (m2 : micro A2) (f : A -> micro A)
   (k : A1 * A2 -> micro A) ko :
  bind m f = Par m1 m2 k ko ->
  (exists k ko, m = Par m1 m2 k ko) \/
  exists a, m = ret a /\ f a = Par m1 m2 k ko.
Proof.
  destruct m; simpl; try discriminate 1. { eauto. }
  intros H. injection H; intros.
  left.
  subst A1; subst A2. repeat (elim_existT). subst m1; subst m2.
  eauto.
Qed.

Lemma destruct_bind_choose {A B} m (m1 m2 : micro B) (f : A -> micro A) k ko :
  bind m f = Choose m1 m2 k ko ->
  (exists k ko, m = Choose m1 m2 k ko) \/
    exists a, m = ret a /\ f a = Choose m1 m2 k ko.
Proof.
  destruct m; simpl; try discriminate 1. { eauto. }
  intros H. injection H; intros.
  left.
  subst B. repeat (elim_existT). subst m1; subst m2.
  eauto.
Qed.

Lemma destruct_orelse_ret {A : Type} (m1 m2 : micro A) a :
  orelse m1 m2 = ret a ->
  m1 = ret a \/ m1 = next /\ m2 = ret a.
Proof.
  destruct m1; try discriminate; eauto.
Qed.

Ltac inject H x := injection H; intros; subst x.

Ltac discriminate_simp :=
  match goal with
  | H : simp (ret _) _ |- _ =>
      apply invert_simp_ret in H; discriminate H
  | H : simp crash _ |- _ =>
      apply destruct_simp_crash in H; discriminate H
  | H : simp next _ |- _ =>
      apply destruct_simp_next in H; discriminate H
  end.

Lemma concat_assoc e1 e2 e3 :
  concat e1 (concat e2 e3) = concat (concat e1 e2) e3.
Proof.
  induction e1 as [|??? IH]; first reflexivity.
  simpl. by rewrite IH.
Qed.

Lemma extend_next η δ p v :
  extend η p v = next ->
  extend δ p v = next
  with
  extends_next η δ ps vs :
    extends η ps vs = next ->
    extends δ ps vs = next
  with
  extendfs_next η δ fps fvs :
    extendfs η fps fvs = next ->
    extendfs δ fps fvs = next
  with
  extend_ret η p v δ :
    extend η p v = ret δ ->
    exists ε, forall δ0, extend δ0 p v = ret (concat ε δ0)
  with
  extends_ret η δ ps vs :
    extends η ps vs = ret δ ->
    exists ε, forall δ0, extends δ0 ps vs = ret (concat ε δ0)
  with
  extendfs_ret η δ fps fvs :
    extendfs η fps fvs = ret δ ->
    ∃ ε : env, ∀ δ0 : env, extendfs δ0 fps fvs = ret (concat ε δ0).
Proof.
  { clear extend_next.
    generalize dependent v.
    induction p; intros v; eauto; try discriminate; simpl; try discriminate 1.
    - specialize (IHp v).
      destruct (extend η p v); simpl in *; try discriminate 1.
      rewrite IHp by reflexivity; done.
    - specialize (IHp1 v). specialize (IHp2 v).
      destruct (extend η p1 v); simpl; try discriminate 1.
      rewrite IHp1 by reflexivity.
      unfold orelse; simpl; tauto.
    - destruct v; auto. apply extends_next.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct v; auto. apply extendfs_next; auto.
    - destruct v; auto. destruct (eq (repr _) _); [discriminate 1 | auto].
    - destruct v; auto. destruct (_ =? _)%char; [discriminate 1 | auto].
    - destruct v; auto. destruct (_ =? _)%string; [discriminate 1 | auto]. }
  { clear extends_next.
    generalize dependent η.
    generalize dependent δ.
    generalize dependent ps.
    induction vs; destruct ps; try discriminate; simpl.
    intros δ η Hb.
    apply destruct_bind_next in Hb as [Hb| (? & ? & Hb)].
    - eapply extend_next in Hb. by rewrite Hb.
    - apply destruct_bind_next in Hb as [Hb|(? & ? & F)].
      + specialize (extend_ret _ _ _ _ H) as (? & extend_envnil).
        rewrite extend_envnil. simpl.
        erewrite IHvs; eauto.
      + discriminate F. }
  { clear extendfs_next.
    generalize dependent η.
    generalize dependent δ.
    generalize dependent fvs.
    induction fps; destruct fvs; try discriminate; simpl.
    intros δ η Hb.
    destruct (if (f =? x)%string then _ else lookup_name fvs _);
      try discriminate Hb; [simpl in Hb|-* |done].
    apply destruct_bind_next in Hb as [Hb|(ηe & Hb & Hb2)].
    { eapply extend_next in Hb; by rewrite Hb. }
    apply extend_ret in Hb as [ε Hb].
    rewrite Hb; simpl.
    apply destruct_bind_next in Hb2 as [Hb2 | (? & ? & F)].
    { eapply IHfps in Hb2; by rewrite Hb2. }
    discriminate F. }
  { clear extend_ret.
    generalize dependent η.
    generalize dependent δ.
    generalize dependent v.
    induction p; intros v δ η Hη; try discriminate; simpl in *.
    - exists EnvNil; by simpl.
    - exists (EnvCons x v EnvNil). by simpl.
    - apply destruct_bind_ret in Hη as (ε & Hε & Hδ).
      apply IHp in Hε as (ι & Hι).
      exists (EnvCons x v ι). intros θ.
      by rewrite Hι; simpl.
    - eapply destruct_orelse_ret in Hη as [Hη|[Hη1 Hη2] ].
      + apply IHp1 in Hη as (ε & Hall).
        exists ε. intros ?. by rewrite Hall.
      + apply IHp2 in Hη2 as (ε & Hall).
        exists ε. intros ?.
        eapply extend_next in Hη1; rewrite Hη1.
        by apply Hall.
    - destruct v; try discriminate.
      eapply extends_ret; eassumption.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; last discriminate.
      apply IHp in Hη as (ε & Hall).
      exists ε. intros ?. by apply Hall.
    - destruct v; try discriminate.
      eapply extendfs_ret; eassumption.
    - destruct v; try discriminate.
      destruct (eq (repr _) _); last discriminate. 
      inject Hη η. by exists EnvNil.
    - destruct v; try discriminate.
      destruct (_ =? _)%char; last discriminate.
      inject Hη η. by exists EnvNil.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; last discriminate.
      inject Hη η. by exists EnvNil. }
  { clear extends_ret.
    generalize dependent η.
    generalize dependent δ.
    generalize dependent ps.
    induction vs; destruct ps; try discriminate; simpl.
    { intros δ η Heq. inject Heq η. exists EnvNil. eauto. }
    intros δ η Hb.
    apply destruct_bind_ret in Hb as (ηe & Hη & Hb).
    apply extend_ret in Hη as (ε & Hall).
    apply destruct_bind_ret in Hb as (ηee & Hηe & Hδ).
    apply IHvs in Hηe as (ε2 & Hall2).
    exists (concat ε2 ε). intros ?. rewrite Hall. simpl. rewrite Hall2. simpl.
    rewrite concat_assoc. reflexivity. }
  { clear extendfs_ret.
    generalize dependent η.
    generalize dependent δ.
    generalize dependent fvs.
    induction fps; destruct fvs; try discriminate; simpl.
    { intros δ η Heq. inject Heq η. exists EnvNil. eauto. }
    { intros δ η Heq. inject Heq η. exists EnvNil. eauto. }
    intros δ η Hb.
    destruct (if (f =? x)%string then _ else lookup_name fvs _);
      try discriminate Hb; simpl in Hb|-*.
    apply destruct_bind_ret in Hb as (ηe & Hη & Hb).
    apply extend_ret in Hη as (ε & Hall).
    apply destruct_bind_ret in Hb as (ηee & Hηe & ?).
    apply IHfps in Hηe as (ε2 & Hall2).
    exists (concat ε2 ε). intros ?.
    rewrite Hall. simpl. rewrite Hall2. simpl.
    rewrite concat_assoc. reflexivity. }
Admitted.

Lemma pure_total {B} `{Encode A} (m : micro B) k ko (ψ : A -> Prop) :
  total m (fun a => pure (k a) ψ) (pure (ko ()) ψ) <->
  pure (try m k ko) ψ.
Proof.
  unfold pure; unfold total.
  split; [intros Ht | intros (a & Hsimp & Hψ)].
  { destruct Ht as [Hterm | Hcont].
    { destruct Hterm as (b & Hsimp & a & Ha & Hψ).
      exists a. split; last assumption.
      eapply prove_simp_try; eauto. }
    { destruct Hcont as (Hnext & a & Hcont & Hψ).
      exists a. split; last assumption.
      eapply prove_simp_try_next; eauto. } }
  { apply invert_simp_try_ret in Hsimp as [(? & ? & ?) | (? & ?)].
    - left; eauto.
    - right; eauto. }
Qed.

Lemma destruct_lookup_name η v :
  lookup_name η v = missing_variable_or_field v \/
    exists v', lookup_name η v = ret v'.
Proof.
  induction η; first eauto.
  simpl.
  destruct (_ =? _)%string; first eauto.
  destruct IHη as [|[v' Hv']].
  - eauto.
  - eauto.
Qed.

Lemma destruct_extend_stop η p v :
  forall X Y c (x :X) (k : Y -> micro env) z,
    extend η p v = Stop c x k z -> False
with
destruct_extends_stop η ps vs :
  forall X Y c (x : X) (k : Y -> micro env) z,
    extends η ps vs = Stop c x k z -> False
with
destruct_extendfs_stop η fps fvs :
  forall X Y c (x : X) (k : Y -> micro env) z,
  extendfs η fps fvs = Stop c x k z -> False.
Proof.
  { clear destruct_extend_stop.
    generalize dependent v.
    induction p; try discriminate; simpl; intros.
    - specialize (IHp v).
      destruct (extend η p v); try discriminate.
      eapply IHp. reflexivity. 
    - specialize (IHp1 v).
      specialize (IHp2 v).
      destruct (extend η p1 v); try discriminate.
      + unfold orelse in H; simpl in H.
        eapply IHp2; eassumption.
      + eapply IHp1. reflexivity.
    - destruct v; try discriminate.
      by apply destruct_extends_stop in H.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; last discriminate.
      eapply IHp; eassumption.
    - destruct v; try discriminate.
      by apply destruct_extendfs_stop in H.
    - destruct v; try discriminate.
      destruct (eq (repr _) _); discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%char; discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; discriminate. }
  { clear destruct_extends_stop.
    generalize dependent η.
    generalize dependent vs.
    induction ps; simpl; destruct vs; try discriminate.
    intros.
    apply destruct_bind_stop in H as [|].
    { destruct H as (?&?&F).
      by apply destruct_extend_stop in F. }
    destruct H as (ηe & Hext & Hb).
    apply destruct_bind_stop in Hb as [Hb|(?&?&?)]; last discriminate.
    destruct Hb as (? & ? & F).
    by apply IHps in F. }
  { clear destruct_extendfs_stop.
    generalize dependent η.
    generalize dependent fvs.
    induction fps; destruct fvs; try discriminate; simpl.
    intros.
    destruct (_ =? _)%string. simpl in H.
    { apply destruct_bind_stop in H as [(?&?&F)|(ηe&Hη&Hb)].
      { by apply destruct_extend_stop in F. }
      apply destruct_bind_stop in Hb as [(?&?&F)|(?&?&F)].
      { by apply IHfps in F. }
      discriminate F. }
    destruct (destruct_lookup_name fvs f) as [Hl|[v' Hv']].
    { rewrite Hl in H. discriminate H. }
    rewrite Hv' in H. simpl in H.
    apply destruct_bind_stop in H as [(?&?&F)|(ηe&Hη&Hb)].
      { by apply destruct_extend_stop in F. }
      apply destruct_bind_stop in Hb as [(?&?&F)|(?&?&F)].
      { by apply IHfps in F. }
      discriminate F. }
Admitted.

Lemma destruct_extend_par η p v :
  forall A1 A2 (m1 : micro A1) (m2 : micro A2) k ko,
    extend η p v = Par m1 m2 k ko -> False
with
destruct_extends_par η ps vs :
  forall A1 A2 (m1 : micro A1) (m2 : micro A2) k ko,
    extends η ps vs = Par m1 m2 k ko -> False
with
destruct_extendfs_par η fps fvs :
  forall A1 A2 (m1 : micro A1) (m2 : micro A2) k ko,
    extendfs η fps fvs = Par m1 m2 k ko -> False.
Proof.
  { clear destruct_extend_par.
    generalize dependent v.
    induction p; try discriminate; simpl; intros.
    - specialize (IHp v).
      destruct (extend η p v); try discriminate.
      eapply IHp. reflexivity. 
    - specialize (IHp1 v).
      specialize (IHp2 v).
      destruct (extend η p1 v); try discriminate.
      + unfold orelse in H; simpl in H.
        eapply IHp2; eassumption.
      + eapply IHp1. reflexivity.
    - destruct v; try discriminate.
      by apply destruct_extends_par in H.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; last discriminate.
      eapply IHp; eassumption.
    - destruct v; try discriminate.
      by apply destruct_extendfs_par in H.
    - destruct v; try discriminate.
      destruct (eq (repr _) _); discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%char; discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; discriminate. }
  { clear destruct_extends_par.
    generalize dependent η.
    generalize dependent vs.
    induction ps; simpl; destruct vs; try discriminate.
    intros.
    apply destruct_bind_par in H as [|].
    { destruct H as (?&?&F).
      by apply destruct_extend_par in F. }
    destruct H as (ηe & Hext & Hb).
    apply destruct_bind_par in Hb as [Hb|(?&?&?)]; last discriminate.
    destruct Hb as (? & ? & F).
    by apply IHps in F. }
  { clear destruct_extendfs_par.
    generalize dependent η.
    generalize dependent fvs.
    induction fps; destruct fvs; try discriminate; simpl.
    intros.
    destruct (_ =? _)%string. simpl in H.
    { apply destruct_bind_par in H as [(?&?&F)|(ηe&Hη&Hb)].
      { by apply destruct_extend_par in F. }
      apply destruct_bind_par in Hb as [(?&?&F)|(?&?&F)].
      { by apply IHfps in F. }
      discriminate F. }
    destruct (destruct_lookup_name fvs f) as [Hl|[v' Hv']].
    { rewrite Hl in H. discriminate H. }
    rewrite Hv' in H. simpl in H.
    apply destruct_bind_par in H as [(?&?&F)|(ηe&Hη&Hb)].
    { by apply destruct_extend_par in F. }
    apply destruct_bind_par in Hb as [(?&?&F)|(?&?&F)].
    { by apply IHfps in F. }
    discriminate F. }
Admitted.

Lemma destruct_extend_choose η p v :
  forall A (m1 m2 : micro A) k ko,
    extend η p v = Choose m1 m2 k ko -> False
with
destruct_extends_choose η ps vs :
  forall A (m1 m2 : micro A) k ko,
    extends η ps vs = Choose m1 m2 k ko -> False
with
destruct_extendfs_choose η fps fvs :
  forall A (m1 m2 : micro A) k ko,
    extendfs η fps fvs = Choose m1 m2 k ko -> False.
Proof.
  { clear destruct_extend_choose.
    generalize dependent v.
    induction p; try discriminate; simpl; intros.
    - specialize (IHp v).
      destruct (extend η p v); try discriminate.
      eapply IHp. reflexivity. 
    - specialize (IHp1 v).
      specialize (IHp2 v).
      destruct (extend η p1 v); try discriminate.
      + unfold orelse in H; simpl in H.
        eapply IHp2; eassumption.
      + eapply IHp1. reflexivity.
    - destruct v; try discriminate.
      by apply destruct_extends_choose in H.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; last discriminate.
      eapply IHp; eassumption.
    - destruct v; try discriminate.
      by apply destruct_extendfs_choose in H.
    - destruct v; try discriminate.
      destruct (eq (repr _) _); discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%char; discriminate.
    - destruct v; try discriminate.
      destruct (_ =? _)%string; discriminate. }
  { clear destruct_extends_choose.
    generalize dependent η.
    generalize dependent vs.
    induction ps; simpl; destruct vs; try discriminate.
    intros.
    apply destruct_bind_choose in H as [|].
    { destruct H as (?&?&F).
      by apply destruct_extend_choose in F. }
    destruct H as (ηe & Hext & Hb).
    apply destruct_bind_choose in Hb as [Hb|(?&?&?)]; last discriminate.
    destruct Hb as (? & ? & F).
    by apply IHps in F. }
  { clear destruct_extendfs_choose.
    generalize dependent η.
    generalize dependent fvs.
    induction fps; destruct fvs; try discriminate; simpl.
    intros.
    destruct (_ =? _)%string. simpl in H.
    { apply destruct_bind_choose in H as [(?&?&F)|(ηe&Hη&Hb)].
      { by apply destruct_extend_choose in F. }
      apply destruct_bind_choose in Hb as [(?&?&F)|(?&?&F)].
      { by apply IHfps in F. }
      discriminate F. }
    destruct (destruct_lookup_name fvs f) as [Hl|[v' Hv']].
    { rewrite Hl in H. discriminate H. }
    rewrite Hv' in H. simpl in H.
    apply destruct_bind_choose in H as [(?&?&F)|(ηe&Hη&Hb)].
    { by apply destruct_extend_choose in F. }
    apply destruct_bind_choose in Hb as [(?&?&F)|(?&?&F)].
    { by apply IHfps in F. }
    discriminate F. }
Admitted.

Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) :
  pat η p v (λ η', pure (eval η' e) φ) (pure_match η v bs φ) ->
  pure_match η v (BrCons (Branch p e) bs) φ.
Proof.
  unfold pure_match; unfold pat.
  intros Hpat. simpl.
  apply pure_total.
  destruct Hpat as [(ηe & Hsimp & Hpure)|(Hsimp & Hpure)].
  { left. destruct (extend η p v) eqn:ext; try discriminate_simp.
    - apply simp_ret_ret in Hsimp. subst a.
      pose proof (temp := ext). apply extend_ret in temp as (ε & Hall).
      exists ε. rewrite Hall. split.
      { apply prove_simp_ret.
        clear. induction ε; first done.
        simpl. by rewrite IHε. }
      rewrite Hall in ext. by inject ext ηe.
    - by apply destruct_extend_stop in ext. 
    - by apply destruct_extend_par in ext.
    - by apply destruct_extend_choose in ext. }
  { right. destruct (extend η p v) eqn:ext; try discriminate_simp.
    - eapply extend_next in ext. rewrite ext. eauto.
    - by apply destruct_extend_stop in ext.
    - by apply destruct_extend_par in ext.
    - by apply destruct_extend_choose in ext. }
Qed.

Lemma pure_match_cons `{Encode A} η v p e bs (ψ : A -> Prop) (φ : Prop) :
  pat η p v (λ η', pure (eval η' e) ψ) φ ->
  (φ -> (pure_match η v bs ψ)) ->
  pure_match η v (BrCons (Branch p e) bs) ψ.
Proof.
  intros.
  apply pure_match_cons_unary.
  eauto using pat_consequence.
Qed.
