From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.

From osiris.program_logic.pure Require Import pure_judgement pure_notation.


(** Evaluating tuples, or several expressions in parallel *)

(* TODO avoid [Forall2] just by showing nil and cons lemmas; offer tactic
   analogous to [pats]. *)

Lemma pure_evals η es φs ψ :
  Forall2 (λ e φ, pure (eval η e) φ ψ) es φs →
  pure (evals η es) (Forall2 id φs) ψ.
Proof.
  revert φs.
  induction es as [ | e es IHes]; intros φs' Hes.
  - simpl_evals. constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (φ & φs & He & Hes & ->).
    simpl_evals.
    eapply pure_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros v vs Hv Hvs. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.

(* The following [_eq] versions should be simpler to use in cases we know the
final values *)

Lemma pure_evals_eq η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (λ x, x = v) ψ) es vs →
  pure (evals η es) (λ x, x = vs) ψ.
Proof.
  revert vs.
  induction es as [ | e es IHes]; intros vs' Hes; simpl_evals.
  - constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (v & vs & He & Hes & ->).
    eapply pure_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros _ _ -> ->. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.

Lemma pure_eval_tuple η es φs ψ :
  Forall2 (λ e φ, pure (eval η e) φ ψ) es φs →
  pure (eval η (ETuple es)) (λ x, ∃ vs, x = VTuple vs ∧ Forall2 id φs vs) ψ.
Proof.
  intros H%pure_evals. simpl_eval.
  apply pure_bind.
  apply (pure_mono_ret _ H).
  eauto using pure_ret.
Qed.

Lemma pure_eval_tuple_eq η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (λ x, x = v) ψ) es vs →
  pure (eval η (ETuple es)) (λ x, x = VTuple vs) ψ.
Proof.
  intros H%pure_evals_eq. simpl_eval.
  apply pure_bind.
  apply (pure_mono_ret _ H). intros; apply pure_ret; congruence.
Qed.


(** Hoare reasoning rules, no encode *)

Lemma pure_ifthenelse η e e1 e2 φ ψ :
  pure (eval η e) (λ v, ∃ b : bool, v = #b ∧ pure (eval η (if b then e1 else e2)) φ ψ) ψ →
  pure (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  simpl.
  intros He. simpl_eval.
  eapply pure_bind, pure_bind, (pure_mono _ He); auto.
  intros _v ([] & -> & H); apply pure_ret, H.
Qed.

Lemma pure_assert η e ψ :
  pure (eval η e) (λ v, v = #true) ψ →
  pure (eval η (EAssert e)) (λ v, v = #()) ψ.
Proof.
  intros He. simpl_eval.
  apply pure_choose. by apply pure_ret.
  apply pure_bind, pure_bind.
  apply (pure_mono _ He); auto.
  intros _ ->.
  repeat econstructor.
Qed.
