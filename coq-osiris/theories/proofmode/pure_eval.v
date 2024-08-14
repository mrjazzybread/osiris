From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp_tactics.

(* Paths. *)

Lemma pure_wp_eval_path η π v :
  lookup_path η π = ret v →
  pure_wpv (eval η (EPath π)) (λ x, x = v).
Proof.
  intros Hlookup. simpl_eval. rewrite Hlookup. by constructor.
Qed.

(* Tuples. *)

(* TODO can we give a generic definition of the encoding of n-tuples? *)

(* This special case at arity 2 does mention the encoding function. *)
(* TODO can we give a similar lemma at arity [n]? *)

Lemma pure_wp_eval_pair `{Encode A1, Encode A2} η e1 e2 (a1 : A1) (a2 : A2) :
  pure_wpv (eval η e1) (λ x, x = #a1) →
  pure_wpv (eval η e2) (λ x, x = #a2) →
  pure_wpv (eval η (EPair e1 e2)) (λ x, x = #(a1, a2)).
Proof.
  intros He1 He2. simpl.
  simpl_eval.
  eapply pure_wp_par_compat_ret; eauto.
  eapply pure_wp_par_compat_ret; eauto.
  apply pure_wp_val.
  intros _ _ -> ->. apply pure_wp_val.
  intros _ _ -> ->. apply pure_wp_val.
Qed.

Lemma pure_wp_tuple' η es vs :
  pure_wpv (evals η es) (λ x, x = vs) →
  pure_wpv (eval η (ETuple es)) (λ x, x = VTuple vs).
Proof.
  intros. simpl_eval. apply pure_wp_bind. apply (pure_wp_mono_ret _ H).
  by constructor; congruence.
Qed.

(* Tuples. *)

(* A special case at arity 2. *)

(* TODO can we give a similar lemma at arity [n]? *)

Lemma pure_eval_pair `{Encode A1, Encode A2} η e1 e2 (ψ : A1 * A2 → Prop) :
  pure (eval η e1) (λ a1 : A1, pure (eval η e2) (λ a2 : A2, ψ (a1, a2))) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto with encode.
Qed.

Lemma pure_eval_triple `{Encode A1, Encode A2, Encode A3} η e1 e2 e3 (ψ : A1 * A2 * A3 -> Prop) :
  pure (eval η e1) (λ a1 : A1,
        pure (eval η e2) (λ a2 : A2,
              pure (eval η e3) (λ a3 : A3,
                    ψ (a1, a2, a3)))) ->
  pure (eval η (ETuple [e1; e2; e3])) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto with encode.
Qed.

Lemma pure_eval_quadruple `{Encode A1, Encode A2, Encode A3, Encode A4} (η : env) (e1 e2 e3 e4 : expr)
  (ψ : A1 * A2 * A3 * A4 → Prop) :
  pure (eval η e1) (λ a1 : A1,
        pure (eval η e2) (λ a2 : A2,
              pure (eval η e3) (λ a3 : A3,
                    pure (eval η e4) (λ a4 : A4,
                          ψ (a1, a2, a3, a4))))) ->
  pure (eval η (ETuple [e1; e2; e3; e4])) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto with encode.
Qed.

Lemma pure_eval_pair_val η e1 e2 (ψ : val → Prop) :
  pure (eval η e1) (λ a1 : val, pure (eval η e2) (λ a2 : val, ψ (VPair a1 a2))) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto.
Qed.

Lemma pure_eval_pair_conseq `{Encode A1, Encode A2} η e1 e2
  (φ1 : A1 → Prop) (φ2 : A2 → Prop) (ψ : A1 * A2 → Prop)
:
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → ψ (a1, a2)) →
  pure (eval η (EPair e1 e2)) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_compat; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret. eauto with encode.
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

(* TODO: comment *)

Lemma pure_eval_int η i (ψ : Z -> Prop) :
  ψ i ->
  pure (eval η (EInt i)) ψ.
Proof.
  intros.
  eapply pure_simp. simp.
  eapply pure_ret; eauto.
Qed.

(* Function applications. *)

Lemma pure_eval_anonfun `{Encode A, Encode A1} η v e (φ : A1 -> Prop) (ψ : val -> Prop) :
  (∀ (x : A), pure (eval ((v, #x) :: η) e) φ) ->
  (∀ (vf : val), (∀ (x : A), pure (call vf #x) φ) -> ψ vf) ->
  pure (eval η (EAnonFun (AnonFun v e))) ψ.
Proof.
  intros Hcall Hcov. specialize (Hcov (VClo η (AnonFun v e))).
  eapply pure_simp; [ simp | eauto ].
  eapply pure_ret; first solve [encode].
  apply Hcov.
  intros. eapply pure_simp; [ simp | eauto ].
Qed.

Lemma pure_eval_anonfun' `{Encode A, Encode A1} η a φ (ψ : val -> Prop) :
  (∀ (x : A), φ (VClo η a) #x) ->
  (∀ (vf : val), (∀ (x : A), φ vf #x) -> ψ vf) ->
  pure (eval η (EAnonFun a)) ψ.
Proof.
  intros Hcall Hcov. specialize (Hcov (VClo η a)).
  eapply pure_simp; [ simp | eauto ].
  eapply pure_ret; first solve [encode].
  eauto.
Qed.

Lemma pure_eval_anonfunction `{Encode A, Encode A1} η bs (φ : A1 -> Prop) (ψ : val -> Prop) :
  (∀ (x : A),
      pure
        (deep_eval_match (("__osiris_anonymous_arg", #x) :: η) bs (O2Ret #x))
        φ) ->
  (∀ (vf : val), (∀ (x : A), pure (call vf #x) φ) -> ψ vf) ->
  pure (eval η (EAnonFun (AnonFunction bs))) ψ.
Proof.
  intros Hcall Hcov.
  eapply pure_simp; [ simp | eauto ].
  eapply pure_ret; first solve [encode].
  apply Hcov.
  intros. eapply pure_simp; [ simp  |  ].
  specialize (Hcall x); generalize Hcall; by simpl_deep_eval_match.
Qed.

Lemma pure_eval_app `{Encode A1, Encode A} η e1 e2 (ψ : A → Prop) :
  pure (eval η e1)
    (λ f : val,
        pure (eval η e2)
          (λ arg : A1,
              pure (call f #arg) ψ)) →
  pure (eval η (EApp e1 e2)) ψ.
Proof.
  intros He1. simpl_eval.
  apply pure_wp_par_vals_left.
  eapply (pure_wp_mono_ret _ He1). intros ? (v & -> & He2).
  eapply (pure_wp_mono_ret _ He2). intros ? (a2 & -> & Hcall).
  apply Hcall.
Qed.

Lemma pure_eval_app_conseq `{Encode A, Encode B} η e1 e2
  (φ1 : val → Prop) (φ2 : A → Prop) (ψ : B → Prop)
:
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ v1 v2, φ1 v1 → φ2 v2 → pure (call v1 #v2) ψ) →
  pure (eval η (EApp e1 e2)) ψ.
Proof.
  intros He1 He2 Hp. simpl_eval.
  apply pure_wp_par_vals_left.
  eapply (pure_wp_mono_ret _ He1). intros ? (v1 & -> & Hv1).
  eapply (pure_wp_mono_ret _ He2). intros ? (a & -> & Ha).
  apply Hp; eauto with encode.
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
  intros He1 He2 He3 Hcall.
  eapply pure_simp; [ simp | eauto ].
  apply pure_wp_par_vals_left.
  apply pure_wp_par_vals_left.
  apply (pure_wp_mono_ret _ He1). intros ? (? & -> & <-).
  apply (pure_wp_mono_ret _ He2). intros ? (? & -> & ->).
  apply (pure_wp_mono_ret _ Hcall). intros ? (c & -> & Hc).
  apply (pure_wp_mono_ret _ He3). intros ? (? & -> & ->).
  auto.
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

(* Helper lemmas for arithmetic operations. *)

Lemma pure_as_int m (φ : Z → Prop) :
  pure m φ →
  pure_wp (as_int m) (λ i, ∃ z, i = repr z ∧ φ z) (λ _, False).
Proof.
  intros Hm. apply pure_wp_bind.
  apply (pure_wp_mono_ret _ Hm). intros ? (z & -> & Hz).
  apply pure_wp_ret. eauto.
Qed.

Lemma pure_par_as_int m1 m2 (φ1 φ2 φ : Z → Prop) k :
  pure m1 φ1 →
  pure m2 φ2 →
  (∀ z1 z2 : Z, φ1 z1 → φ2 z2 → pure (k (repr z1, repr z2)) φ) →
  pure (Par (as_int m1) (as_int m2) (pfbind inject2 k)) φ.
Proof.
  intros Hm1 Hm2 Hk.
  unfold as_int.
  eapply pure_wp_par_compat. 1,2: eapply pure_as_int; eauto. 2: tauto.
  intros ? ? (z1 & -> & Hz1) (z2 & -> & Hz2).
  eapply pure_simp; [ simp | ].
  eauto.
Qed.

(* Primitive arithmetic operations. *)

Lemma pure_eval_add η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 + z2)) →
  pure (eval η (EIntAdd e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_sub η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 - z2)) →
  pure (eval η (EIntSub e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_mul η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 * z2)) →
  pure (eval η (EIntMul e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
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
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_wp_bind, pure_wp_mono_ret.
  apply pure_wp_check_div_by_zero; eauto.
  intros [] _.
  apply pure_wp_ret.
  eauto 10 with encode.
Qed.

(* Primitive logical operations on machine integers. *)

Lemma pure_eval_lnot η e1 (φ1 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  (∀ z1, φ1 z1 → φ (Z.lnot z1)) →
  pure (eval η (EIntLnot e1)) φ.
Proof.
  intros He1%pure_as_int Hp. simpl_eval.
  eapply pure_wp_bind_compat; eauto. intros ? (z & -> & Hz).
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_land η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.land z1 z2)) →
  pure (eval η (EIntLand e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_lor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lor z1 z2)) →
  pure (eval η (EIntLor e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_lxor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lxor z1 z2)) →
  pure (eval η (EIntLxor e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_lsl η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftl z1 z2)) →
  pure (eval η (EIntLsl e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_wp_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_lsr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → urepresentable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntLsr e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_wp_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_asr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 →
  pure (eval η e2) φ2 →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntAsr e1 e2)) φ.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_wp_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* Helper lemmas for operations on Booleans. *)

Lemma pure_as_bool m (φ : bool → Prop) :
  pure m φ →
  pure_wp (as_bool m) φ (λ _, False).
Proof.
  intros Hm. force_unfold as_bool. apply pure_wp_bind.
  apply (pure_wp_mono_ret _ Hm). intros ? (b & -> & Hb).
  destruct b; force_unfold val_as_bool; apply pure_wp_ret; eauto.
Qed.

Lemma pure_bind_as_bool {A} m (φ : bool → Prop) (ψ : A → Prop) (k : bool → micro A exn) :
  pure m φ →
  (∀ b : bool, φ b → pure_wp (k b) ψ (λ _, False)) →
  pure_wp (bind (as_bool m) k) ψ (λ _, False).
Proof.
  intros Hm Hp. apply pure_wp_bind, pure_as_bool.
  apply (pure_wp_mono_ret _ Hm). intros ? (b & -> & Hb).
  destruct b; force_unfold val_as_bool; eauto.
Qed.

(* Primitive operations on Booleans. *)

Lemma pure_eval_negb η e (φ ψ : bool → Prop) :
  pure (eval η e) φ →
  (∀ b, φ b → ψ (negb b)) →
  pure (eval η (EBoolNeg e)) ψ.
Proof.
  intros He Hp. simpl_eval.
  eapply pure_bind_as_bool; eauto. intros b Hb. apply pure_wp_ret. eauto with encode.
Qed.

Lemma pure_eval_not η e (φ ψ : Prop → Prop) :
  pure (eval η e) φ →
  (∀ P, φ P → ψ (¬P)) →
  pure (eval η (EBoolNeg e)) ψ.
Proof.
  intros He Hp. simpl_eval.
  eapply pure_wp_bind.
  eapply pure_as_bool.
  eapply pure_wp_mono_ret. apply He. intros ? (P & -> & HP).
  exists (truth P). split; auto. apply pure_wp_ret. eexists. split; eauto with encode.
  unfold encode, Encode_Prop. rewrite truth_neg. auto.
Qed.

(* Local definitions. *)

(* TODO only one or two bindings, for now *)

(* TODO: lemmas starting with "_" are unused: remove? *)

Lemma pure_eval_let_pair `{Encode A1, Encode A2} `{Encode X}
  p1 p2 e1 e2 η (ψ : X -> Prop) :
  pure (eval η e1) (λ '((v1, v2) : A1 * A2),
      pure (
          δ ← widen (irrefutably_extend [] p1 #v1);
          θ ← widen (irrefutably_extend δ p2 #v2);
          eval (θ ++ η) e2
        ) ψ) ->
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ.
Proof.
  (* This proof is a long rewriting sequence, which makes some sense as it is
  not the standard method to prove a let binding, but rather a way to reduce the
  wp of a parallel pair to ordered wps of two binds with error handling *)
  intros He1.
  simpl_eval. apply pure_wp_par_vals_left.
  apply (pure_wp_mono_ret _ He1). clear He1.
  intros ? ([v1 v2] & -> & Hpure). apply pure_wp_ret.
  apply pure_wp_bind.
  apply pure_wp_bind.
  apply pure_wp_ret.
  unfold widen, irrefutably_extend in *.
  rewrite !try_try in *. simpl_extend.
  rewrite !bind_as_try, !try_try in *.
  apply pure_wp_try2.
  apply invert_pure_wp_try2 in Hpure.
  apply (pure_wp_mono _ Hpure); clear Hpure.
  - intros δ Hpure.
    unfold continue in *.
    unfold glue2 in *.
    repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *.
    apply invert_pure_wp_try2 in Hpure.
    apply pure_wp_try2.
    apply (pure_wp_mono _ Hpure); clear Hpure.
    + intros θ Hpure.
      unfold continue, glue2 in *.
      repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *.
      apply pure_wp_ret. eauto.
    + unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_wp_crash; eauto.
  - unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_wp_crash; eauto.
Qed.

Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop) :
  pure (eval η e1) φ1 →
  (∀ a1, φ1 a1 → pure (eval ((x, #a1) :: η) e) ψ) →
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros He1 He.
  simpl_eval.
  eapply pure_wp_par_compat_ret.
  - eauto.
  - eapply pure_wp_simp. simp. apply pure_wp_ret_eq.
  - intros _v _η (a1 & -> & Ha1) ->.
    apply pure_wp_bind, pure_wp_bind, pure_wp_ret.
    unfold irrefutably_extend.
    apply pure_wp_widen.
    simpl_extend.
    apply pure_wp_try, pure_wp_ret, pure_wp_ret, He, Ha1.
Qed.

Lemma pure_eval_let' `{Encode A1, Encode B} η x e1 e
  (a1 : A1) (ψ : B → Prop) :
  pure (eval η e1) (λ x, x = a1) →
  pure (eval ((x, #a1) :: η) e) ψ →
  pure (eval η (ELet1Var x e1 e)) ψ.
Proof.
  intros He1 He2.
  eapply pure_eval_let; eauto.
  congruence.
Qed.

(* Conditionals. *)

Lemma pure_eval_ifthenelse_bool `{Encode A} η e e1 e2 (φ : bool → Prop) (ψ : A → Prop) :
  pure (eval η e) φ →
  (φ true  → pure (eval η e1) ψ) →
  (φ false → pure (eval η e2) ψ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ.
Proof.
  intros. eapply pure_wp_ifthenelse_bool; eauto.
Qed.

Lemma pure_eval_ifthenelse `{Encode A} η e e1 e2 (P : Prop) (ψ : A → Prop) :
  pure (eval η e) (λ P', P' <-> P) →
  (P → pure (eval η e1) ψ) →
  (~ P → pure (eval η e2) ψ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ.
Proof.
  intros He He1 He2.
  eapply pure_wp_ifthenelse.
  eapply (pure_wp_mono_ret _ He).
  intros _v (_ & -> & ->%iff_encode). exists (truth P).
  rewrite encode_truth. split; auto.
  generalize (truth_elim P).
  destruct (truth P); auto.
Qed.

(* Helper lemma for Boolean operations *)

Lemma pure_eval_comparison_operator `{Encode A} η e1 e2 (x1 x2 : Z) (f : val → val → micro bool exn) b a (φ : A → Prop) :
  pure (eval η e1) (λ x1' : Z, x1' = x1) →
  pure (eval η e2) (λ x2' : Z, x2' = x2) →
  f #x1 #x2 = ret b →
  #a = #b →
  φ a →
  pure (Par (eval η e1) (eval η e2) (pfbind inject2 (λ '(v1, v2), 'b ← f v1 v2; ret (VBool b)))) φ.
Proof.
  intros He1 He2 Ef Ea Ha.
  eapply pure_wp_par_compat_ret; eauto.
  intros _ _ (_ & -> & ->) (_ & -> & ->).
  apply pure_wp_bind, pure_wp_ret, pure_wp_bind.
  rewrite Ef.
  apply pure_wp_ret, pure_wp_ret.
  eauto with encode.
Qed.

(* Boolean operations *)

Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ P, P <-> (x1 <= x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpLe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ (b : bool), b <-> (x1 <= x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpLe; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

Lemma pure_eval_EOpLt η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLt e1 e2)) (λ P, P <-> (x1 < x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpLt_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLt e1 e2)) (λ (b : bool), b <-> (x1 < x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpLt; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

Lemma pure_eval_EOpGt η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGt e1 e2)) (λ P, P <-> (x1 > x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpGt_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGt e1 e2)) (λ (b : bool), b <-> (x1 > x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpGt; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

Lemma pure_eval_EOpGe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGe e1 e2)) (λ P, P <-> (x1 >= x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpGe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGe e1 e2)) (λ (b : bool), b <-> (x1 >= x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpGe; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

Lemma pure_eval_EOpEq η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpEq e1 e2)) (λ P, P <-> (x1 = x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpEq_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpEq e1 e2)) (λ (b : bool), b <-> (x1 = x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpEq; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

Lemma pure_eval_EOpNe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpNe e1 e2)) (λ P, P <-> (x1 <> x2)%Z).
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpNe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpNe e1 e2)) (λ (b : bool), b <-> (x1 <> x2)).
Proof.
  intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpNe; eauto.
  intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
Qed.

(* Runtime assertions. *)

Lemma pure_eval_assert_bool η e :
  pure (eval η e) (λ b, b = true) →
  pure (eval η (EAssert e)) (λ (_ : unit), True).
Proof.
  intros He.
  eapply pure_wp_mono_ret.
  eapply pure_wp_assert.
  eapply pure_wp_mono_ret.
  eapply He.
  - by intros _ (V & -> & ->).
  - intros _ ->. eauto.
Qed.

Lemma pure_eval_assert_Prop η e :
  pure (eval η e) (λ P : Prop, P) →
  pure (eval η (EAssert e)) (λ (_ : unit), True).
Proof.
  intros He.
  eapply pure_wp_mono_ret.
  eapply pure_wp_assert.
  eapply pure_wp_mono_ret.
  eapply He.
  - intros _ (P & -> & HP).
    unfold encode, Encode_bool, Encode_Prop. by rewrite truth_true.
  - intros _ ->. eauto.
Qed.

(* Sequencing of pure computations. *)

Lemma pure_eval_seq' `{Encode A} η e1 e2 (ψ : A -> Prop) :
  pure_wp (eval η e1) (λ _, True) (λ _, False) ->
  pure (eval η e2) ψ ->
  pure (eval η (ESeq e1 e2)) ψ.
Proof.
  intros He1 He2.
  apply pure_wp_seq.
  apply (pure_wp_mono_ret _ He1). intros _ _.
  apply (pure_wp_mono_ret _ He2). intuition.
Qed.

Lemma pure_eval_seq `{Encode A} `{Encode B} η e1 e2 (ψ : A -> Prop) :
  pure (eval η e1) (λ _ : B, True) ->
  pure (eval η e2) ψ ->
  pure (eval η (ESeq e1 e2)) ψ.
Proof.
  intros He1 He2.
  apply pure_wp_seq.
  apply (pure_wp_mono_ret _ He1). intros _ _.
  apply (pure_wp_mono_ret _ He2). intuition.
Qed.

Lemma pure_eval_mexpr_struct (η δ whatenv : env) items (ψ : val -> Prop) :
  simp (eval_sitems (η, []) items) (ret (whatenv, δ)) ->
  ψ (VStruct δ) ->
  pure (eval_mexpr η (MStruct items)) ψ.
Proof.
  intros. simpl_eval_mexpr.
  eapply pure_simp; [ simp | eauto using pure_ret ].
Qed.

Lemma pure_eval_mexpr_coerc η me c v (ψ : val -> Prop):
  simp (eval_mexpr η me) (ret v) ->
  pure (coerce c v) ψ ->
  pure (eval_mexpr η (MCoercion me c)) ψ.
Proof.
  intros Hme Hc. simpl_eval_mexpr. eapply pure_wp_bind.
  eapply pure_wp_simp; eauto.
  eapply pure_wp_mono_ret. eapply pure_wp_ret_eq.
  intros _ ->.
  rewrite pure_wp_widen'.
  apply Hc.
Qed.

Lemma pure_eval_path `{Encode A} η π (ψ : A -> Prop) :
  pure (lookup_path η π) ψ ->
  pure (eval η (EPath π)) ψ.
Proof.
  simpl_eval.
  apply pure_wp_widen.
Qed.

Lemma pure_eval_ret_concat `{Encode A} e δ η (ψ : A -> Prop) :
  pure (eval (δ ++ η) e) ψ ->
  pure (θ ← ret (δ ++ η);
        eval θ e) ψ.
Proof.
  tauto.
Qed.

Lemma pure_eval_const `{Encode X} η c x (ψ : X -> Prop) :
  VConstant c = #x ->
  ψ x ->
  pure (eval η (EConstant c)) ψ.
Proof.
  intros.
  eapply pure_simp. simp.
  eauto using pure_ret.
Qed.

Lemma pure_eval_data `{Encode Y} η c e y (ψ : Y -> Prop) :
  pure (eval η e) (λ v', VData c v' = #y) ->
  ψ y ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros He Hy.
  simpl_eval.
  eapply pure_bind_unary; eauto.
  eapply pure_consequence; eauto.
  intros ? A.
  eapply pure_ret; eauto; auto.
Qed.

Class CRel1 {A : Type} (X : Type) `{Encode A, Encode X}
  (c : string) (C : A -> X) := { }.

Lemma pure_eval_data1 `{CRel1 A1 X c C} (η : env) (e : expr) (ψ : X → Prop) :
  pure (eval η e)
    (λ x,
      VData c (VTuple1 #x) = #(C x) /\ ψ (C x)) ->
  pure (eval η (EData c (ETuple [e]))) ψ.
Proof.
  intros He.
  simpl_eval.
  apply pure_wp_par_vals_left.
  eapply (pure_wp_mono_ret _ He).
  intros _ (? & -> & ? & ?).
  repeat apply pure_wp_ret || apply pure_wp_bind.
  eauto.
Qed.

Class CRel2 (A1 A2 X : Type) `{Encode A1, Encode A2, Encode X}
  (c : string) (C : A1 -> A2 -> X) := { }.

(* We write "[encode x; #y]" instead of "[#x; #y]" because stdpp imports the
   notation "[# _; _; _]" for vectors. Unfortunately, using "Disable Notation"
   does not to remove the vector notation from Coq's parser. *)

Lemma pure_eval_data2 `{CRel2 A1 A2 X c C} (η : env) (e : expr) (ψ : X → Prop) :
  pure (eval η e)
    (λ '(x, y),
      VData c (VTuple [encode x; #y]) = #(C x y) /\ ψ (C x y)) ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros He.
  simpl_eval. apply pure_wp_bind.
  eapply (pure_wp_mono_ret _ He).
  intros _ ((?, ?) & -> & ? & ?).
  repeat apply pure_wp_ret || apply pure_wp_bind.
  eauto.
Qed.

(* Example usage of the CRel typeclasses:

   Global Instance CRel2Cons `{Encode A} :
     CRel2 A (list A) (list A) "::" cons := {}. *)

Class CRel3 {A1 A2 A3 : Type} (X : Type) `{Encode A1, Encode A2, Encode A3, Encode X}
  (c : string) (C : A1 -> A2 -> A3 -> X) := { }.

Lemma pure_eval_data3 `{CRel3 A1 A2 A3 X c C} (η : env) (e : expr) (ψ : X → Prop) :
  pure (eval η e)
    (λ '(x, y, z),
      VData c (VTuple ([encode x; #y; #z])) = #(C x y z) /\ ψ (C x y z)) ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros He.
  simpl_eval. apply pure_wp_bind.
  eapply (pure_wp_mono_ret _ He).
  intros ? (((?, ?), ?) & -> & ? & ?).
  repeat apply pure_wp_ret || apply pure_wp_bind.
  eauto.
Qed.

Class CRel4 (A1 A2 A3 A4 X : Type) `{Encode A1, Encode A2, Encode A3, Encode A4, Encode X}
  (c : string) (C : A1 -> A2 -> A3 -> A4 -> X) := { }.

Lemma pure_eval_data4 `{CRel4 A1 A2 A3 A4 X c C} (η : env) (e : expr) (ψ : X → Prop) :
  pure (eval η e)
    (λ '(x, y, z, w),
      VData c (VTuple ([encode x; #y; #z; #w])) = #(C x y z w) /\ ψ (C x y z w)) ->
  pure (eval η (EData c e)) ψ.
Proof.
  intros He.
  simpl_eval. apply pure_wp_bind.
  eapply (pure_wp_mono_ret _ He).
  intros ? ((((?, ?), ?), ?) & -> & ? & ?).
  repeat apply pure_wp_ret || apply pure_wp_bind.
  eauto.
Qed.
