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

(* TODO unused, for now *)
Lemma simp_consequence A (m : micro A) a' a :
  simp m (ret a') →
  a = a' →
  simp m (ret a).
Proof.
  intros. subst. eauto.
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
  simp (eval (EnvCons x v1 η) e2) m →
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
