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

Lemma simp_totalv {A E} m (a : A) :
  simp m (ret a : micro A E) ↔
  totalv m (λ a', a = a').
Proof.
  split.
  { eauto using totalv_simp, totalv_ret. }
  { intros. destruct_total a' e'. congruence. }
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

Lemma simp_consequence {A E} (m : micro A E) a' a :
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
  Forall2 (λ e v, simp (eval η e) (ret v)) es vs →
  simp (evals η es) (ret vs).
Proof.
  induction 1; simpl; simp. (* nice and sweet! *)
Qed.

(* This lemma is general but does not mention the encoding function,
   because we do not currently have a general definition of the
   encoding of n-tuples. *)

(* TODO can we give a generic definition of the encoding of n-tuples? *)

Lemma simp_eval_tuple η es vs :
  Forall2 (λ e v, simp (eval η e) (ret v)) es vs →
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

(* Primitive logical operations on machine integers. *)

Lemma simp_eval_lnot η e (z : Z) :
  simp (eval η e) (ret #z) →
  simp (eval η (EIntLnot e)) (ret #(Z.lnot z)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_land η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntLand e1 e2)) (ret #(Z.land z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_lor η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntLor e1 e2)) (ret #(Z.lor z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_eval_lxor η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  simp (eval η (EIntLxor e1 e2)) (ret #(Z.lxor z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
Qed.

Lemma simp_if_in_shift_range {A E} z (m : micro A E) :
  in_shift_range z →
  simp (if_in_shift_range (repr z) m) m.
Proof.
  intros.
  unfold if_in_shift_range, in_shift_range_b.
  rewrite signed_repr by eauto using in_shift_range_representable.
  rewrite in_shift_range_b_spec by assumption.
  simp.
Qed.

Lemma simp_eval_lsl η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  in_shift_range z2 →
  simp (eval η (EIntLsl e1 e2)) (ret #(Z.shiftl z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
  rewrite lsl_repr_repr by assumption.
  eauto using simp_if_in_shift_range.
Qed.

Lemma simp_eval_lsr η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  urepresentable z1 →
  in_shift_range z2 →
  simp (eval η (EIntLsr e1 e2)) (ret #(Z.shiftr z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
  rewrite lsr_repr_repr by assumption.
  eauto using simp_if_in_shift_range.
Qed.

Lemma simp_eval_asr η e1 e2 (z1 z2 : Z) :
  simp (eval η e1) (ret #z1) →
  simp (eval η e2) (ret #z2) →
  representable z1 →
  in_shift_range z2 →
  simp (eval η (EIntAsr e1 e2)) (ret #(Z.shiftr z1 z2)).
Proof.
  intros. simpl. unfold as_int. simp.
  rewrite asr_repr_repr by assumption.
  eauto using simp_if_in_shift_range.
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
  (let η' := (x, v1) :: η in simp (eval η' e2) m) →
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
  pure (eval η e1)
    (λ f : val,
        pure (eval η e2)
          (λ e : val,
              pure (call f e) ψ)) →
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

Definition pure_call2 `{Encode X} vf arg1 arg2 (φ : X -> Prop) :=
  pure (call vf arg1)
    (λ c, pure (call c arg2) φ).

Lemma pure_eval_app2 `{Encode A, Encode B, Encode C} η e1 e2 e3 vf
  (arg1 : A) (arg2 : B) (ψ : C → Prop)
  :
  pure (eval η e1) (λ vf', vf' = vf) ->
  pure (eval η e2) (λ arg1', arg1' = arg1) ->
  pure (eval η e3) (λ arg2', arg2' = arg2) ->
  pure_call2 vf #arg1 #arg2 ψ ->
  pure (eval η (EApp (EApp e1 e2) e3)) ψ.
Proof.
  intros.
  destruct_pure v2; destruct_pure v1; destruct_pure vf'; subst.
  eapply pure_simp; [ simp | eauto ].
  eapply pure_bind_unary with (A:=val).
  assumption.
Qed.

Lemma pure_eval_app2_conseq `{Encode A, Encode B, Encode C} η e1 e2 e3 vf
  (arg1 : A) (arg2 : B) (φ ψ : C → Prop)
  :
  pure (eval η e1) (λ vf', vf' = vf) ->
  pure (eval η e2) (λ arg1', arg1' = arg1) ->
  pure (eval η e3) (λ arg2', arg2' = arg2) ->
  pure_call2 vf #arg1 #arg2 φ ->
  (∀ a, φ a → ψ a) →
  pure (eval η (EApp (EApp e1 e2) e3)) ψ.
Proof.
  intros.
  eapply pure_eval_app2; eauto.
  eapply pure_consequence; first eassumption.
  simpl; intros.
  eapply pure_consequence; eauto.
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

(* Primitive logical operations on machine integers. *)

Lemma pure_eval_lnot η e1 (φ1 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  (∀ z1, φ1 z1 → φ (Z.lnot z1)) →
  pure (eval η (EIntLnot e1)) φ.
Proof.
  intros. destruct_pure z1. eauto 6 using simp_eval_lnot.
Qed.

Lemma pure_eval_land η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.land z1 z2)) →
  pure (eval η (EIntLand e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_land.
Qed.

Lemma pure_eval_lor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lor z1 z2)) →
  pure (eval η (EIntLor e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_lor.
Qed.

Lemma pure_eval_lxor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lxor z1 z2)) →
  pure (eval η (EIntLxor e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 6 using simp_eval_lxor.
Qed.

Lemma pure_eval_lsl η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftl z1 z2)) →
  pure (eval η (EIntLsl e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 7 using simp_eval_lsl.
Qed.

Lemma pure_eval_lsr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → urepresentable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntLsr e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 8 using simp_eval_lsr.
Qed.

Lemma pure_eval_asr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntAsr e1 e2)) φ.
Proof.
  intros. destruct_pure z2. destruct_pure z1. eauto 8 using simp_eval_asr.
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

(* TODO only one or two bindings, for now *)

Lemma simp_wrap {A E E'} (m : micro A E) (a : A) :
  simp (try m ret (λ (_ : E), @Crash A E')) (ret a) -> simp m (ret a).
Proof.
  intros H.
  apply invert_simp_try_ret in H as [(a' & ? & simp_ret_ret) | (? & ? & simp_crash_ret)].
  { apply destruct_simp_ret in simp_ret_ret.
    by (injection simp_ret_ret; intros ->). }
  { apply destruct_simp_crash in simp_crash_ret. (* TODO: rename to invert_simp_crash *)
    congruence. }
Qed.

Lemma simp_eval_let_pair `{Encode A1, Encode A2} p1 p2 e1 e2 m
  (v1 : A1) (v2 : A2) η θ :
  simp (eval η e1) (ret #(v1, v2)) ->
  simp (δ ← irrefutably_extend [] p1 #v1;
        irrefutably_extend δ p2 #v2) (ret θ) ->
  simp (eval (θ ++ η) e2) m ->
  simp (eval η (ELet1 (PPair p1 p2) e1 e2)) m.
Proof.
  intros. simp.
  eapply prove_simp_try; last eassumption.
  apply invert_simp_bind_ret in H2 as (δ & Hnil & Hext).
  unfold irrefutably_extend in *.
  eapply prove_simp_bind. { eauto using simp_wrap. }
  rewrite bind_bind.
  simpl. rewrite bind_ret_right. eauto using simp_wrap.
Qed.

Lemma pure_eval_let_pair `{Encode A1, Encode A2} `{Encode X}
  p1 p2 e1 e2 η (ψ : X -> Prop) :
  pure (eval η e1) (λ '((v1, v2) : A1 * A2),
      pure (
          δ ← irrefutably_extend [] p1 #v1;
          θ ← irrefutably_extend δ p2 #v2;
          eval (θ ++ η) e2
        ) ψ) ->
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ.
Proof.
  intros ([v1 v2] & Hv & Hpure).
  destruct Hpure as (x & Hsimp & Hψ).
  eapply invert_simp_bind_ret in Hsimp as (δ & Hv1 & Hsimp).
  eapply invert_simp_bind_ret in Hsimp as (θ & Hv2 & Hx).
  eapply pure_simp.
  { eapply simp_eval_let_pair; eauto using prove_simp_bind. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_let' `{Encode A1, Encode B} η x e1 e
  (a1 : A1) (ψ : B → Prop)
:
  simp (eval η e1) (ret #a1) →
  pure (eval ((x, #a1) :: η) e) ψ →
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros. destruct_pure b. eauto using simp_eval_let.
Qed.

Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop) :
  pure (eval η e1) φ1 →
  (∀ a1, φ1 a1 → pure (eval ((x, #a1) :: η) e) ψ) →
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


Lemma pure_eval_ifthenelse_prop `{Encode A} η e e1 e2 (P : Prop) (ψ : A → Prop) :
  pure (eval η e) (λ P', P' <-> P) →
  (P → pure (eval η e1) ψ) →
  (~ P → pure (eval η e2) ψ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ.
Proof.
  intros. destruct_pure P'.
  eapply simp_eval_ifthenelse_pure;
    first eassumption;
    rewrite H3; auto.
Qed.

(* Boolean operations *)

Lemma pure_eval_EOpLe_pure η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ P, P <-> (x1 <= x2)%Z).
Proof.
  intros. destruct_pure a; destruct_pure b; subst.
  eapply pure_simp.
  rewrite eval_eval'; simpl.
  eapply advance_SimpPar; eauto.
  apply SimpParRetRet. simpl.
  eapply pure_ret.
  { unfold encode, Encode_Prop.
    f_equal. f_equal.
    rewrite lt_repr_repr; try assumption.
    rewrite truth_Is_true.
    reflexivity. }
  apply Zle_spec.
Qed.

Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ b, (x1 <=? x2)%Z = b).
Proof.
  intros. destruct_pure a; destruct_pure b; subst.
  eapply pure_simp.
  rewrite eval_eval'; simpl.
  eapply advance_SimpPar; eauto.
  apply SimpParRetRet.
  eapply pure_ret; [ solve [encode] | ].
  rewrite lt_repr_repr; try assumption.
  apply Z.leb_antisym.
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
  simp (eval_sitems items (η, [])) (ret (whatenv, δ)) ->
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
  pure (eval (δ ++ η) e) ψ ->
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

Lemma pure_eval_data `{Encode Y} η c e y (ψ : Y -> Prop) :
  pure (eval η e) (λ v', VData c v' = #y) ->
  ψ y ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros. destruct_pure x; subst.
  eapply pure_simp; [eauto using simp_eval_data |].
  eapply pure_ret; eauto.
Qed.
