From iris.base_logic Require Export iprop.


(** The standard notion of satisfiable for Iris with natural numbers as step-indicies. *)
Definition sat_standard {M: ucmra} (P: uPred M) : Prop :=
  ∀ n: nat, ∃ r: M, ✓{n} r ∧ uPred_holds P n r.

Global Arguments sat_standard {_} _%_I.

Section satisfiable_basic_properties.
  Context {M: ucmra}.
  Local Arguments uPred_holds {_} !_ _ _ /.

  Lemma sat_standard_intro: sat_standard (M:=M) True.
  Proof.
    intros n. exists ε. split; first apply ucmra_unit_validN. by uPred.unseal.
  Qed.

  Lemma sat_standard_mono (P Q: uPred M) : (P ⊢ Q) → sat_standard P → sat_standard Q.
  Proof.
    intros HPQ HQ n. destruct (HQ n) as (r & ? & ?). exists r. split; first done.
    destruct HPQ as [HPQ]. by eapply HPQ.
  Qed.

  Lemma sat_standard_elim (φ: Prop): sat_standard (M:=M) ⌜φ⌝ → φ.
  Proof.
    intros H. destruct (H 0) as (r & ? & Hpure). revert Hpure. by uPred.unseal.
  Qed.

  Lemma sat_standard_upd (P: uPred M) : sat_standard (|==> P) → sat_standard P.
  Proof.
    intros Hsat n. destruct (Hsat n) as (r & ? & HP).
    revert HP. uPred.unseal. intros HP.
    destruct (HP n ε) as (r' & Hv' & HP'); first done.
    { by rewrite right_id. }
    exists r'. rewrite right_id in Hv'. split; done.
  Qed.

  Lemma sat_standard_later (P: uPred M) : sat_standard (▷ P) → sat_standard P.
  Proof.
    intros Hsat n. destruct (Hsat (S n)) as (r & ? & HP).
    exists r. split; first by eapply cmra_validN_S.
    revert HP. by uPred.unseal.
  Qed.

  (** disjunction holds only classically *)
  Lemma sat_standard_or (P Q: uPred M) :
    (∀ P, P ∨ ¬ P) →
    sat_standard (P ∨ Q) → sat_standard P ∨ sat_standard Q.
  Proof.
    intros xm Hsat.
    destruct (xm (∃ n, ∀ r, ✓{n} r → ¬ uPred_holds P n r)) as [HP|HP].
    - right. intros n. destruct HP as [m HP].
      destruct (Hsat (max n m)) as [r [Hr HPQ]].
      revert HPQ. uPred.unseal. intros [HP'|HQ].
      + exfalso. eapply HP; eauto using uPred_mono, cmra_validN_le with lia.
      + exists r. eauto using uPred_mono, cmra_validN_le with lia.
    - left. intros n. destruct (xm (∃ r : M, ✓{n} r ∧ uPred_holds P n r)) as [|HNP]; first done.
      exfalso. eapply HP. exists n. intros r Hr HP'. eapply HNP.
      exists r. split; done.
  Qed.

  (** resources *)
  Lemma sat_standard_valid_own (r: M) : ✓ r → sat_standard (uPred_ownM r).
  Proof.
    intros Hr n. exists r. split; first by eapply cmra_valid_validN.
    by uPred.unseal.
  Qed.

  Lemma sat_standard_own_valid (r: M) : sat_standard (uPred_ownM r) → ✓ r.
  Proof.
    intros Hsat. eapply cmra_valid_validN. intros n.
    destruct (Hsat n) as (r' & ? & Hown). revert Hown. uPred.unseal.
    intros Hown. by eapply cmra_validN_includedN.
  Qed.

End satisfiable_basic_properties.
