(* The runtime check performed by [as_bool] is consistent with our
   definition of [encode] at type [bool]. *)

Lemma simp_as_bool m (b : bool) :
  simp m (ret #b) →
  simp (as_bool m) (ret b).
Proof.
  unfold as_bool. simpl encode. intros. simp.
Qed.

(* Ditto for [as_int]. *)

Lemma simp_as_int m (z : Z) :
  simp m (ret #z) →
  simp (as_int m) (ret (repr z)).
Proof.
  unfold as_int. simpl encode. intros. simp.
Qed.

(* The following lemma is where we verify that the runtime check performed by
   [as_bool] is consistent with our definition of [encode] at type [bool]. *)

Lemma prove_totalv_as_bool m (φ : bool → Prop) :
  pure m φ →
  totalv (as_bool m) φ.
Proof.
  rewrite pure_totalv. intros. unfold as_bool.
  eapply totalv_bind; [ eauto | simpl ].
  intros ? (b & ? & ?); subst.
  rewrite val_as_bool_VBool.
  eauto using totalv_ret.
Qed.

Lemma prove_totalv_as_int m (φ : Z → Prop) :
  pure m φ →
  totalv (as_int m) (λ (i : int), ∃ z, i = repr z ∧ φ z).
Proof.
  rewrite pure_totalv. intros. unfold as_int.
  eapply totalv_bind; [ eauto | simpl ].
  intros ? (z & ? & ?); subst.
  simpl. eauto using totalv_ret.
Qed.

Lemma totalv_Par {A1 A2 A}
  m1 m2 (k : A1 * A2 → micro A) z φ1 φ2 (φ : A → Prop)
:
  totalv m1 φ1 →
  totalv m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → totalv (k (a1, a2)) φ) →
  totalv (Par m1 m2 k z) φ.
Proof.
  intros. rewrite <- try_par.
  eapply totalv_try with (φ' := λ a, totalv (k a) φ).
  { eauto using totalv_par. }
  { eauto. }
Qed.
