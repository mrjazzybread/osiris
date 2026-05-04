From Stdlib.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.
From osiris.lang Require Import lang ind.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Import wp pure_rules judgements pattern_rules.

(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) (ψ : exn -> Prop) :=
  pure (eval_bindings η bs) φ ψ.

Lemma pure_irrefutably_extend {E} η δ p v φ (ψ : E → Prop) :
  pure (eval_pat η δ p v) φ ⊥ →
  pure (irrefutably_extend η δ p v) φ ψ.
Proof.
  intros H.
  apply pure_wp_try, (pure_wp_mono _ H);
    firstorder eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [bindings]. *)

Lemma bindings_cons_unary `{Encode A} η p e bs φ :
  pure (eval η e) (λ a : A, bindings η bs (λ η', pattern η η' p #a φ False) ⊥) ⊥ ->
  bindings η (Binding p e :: bs) φ ⊥.
Proof.
  unfold bindings. simpl. intros He.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par_seq; eauto.
  eapply pure_ret_mono. { apply He. } intros a Ha.
  eapply pure_ret_mono. { apply Ha. } intros η' Hpat.
  apply pure_irrefutably_extend. apply Hpat.
Qed.

Lemma bindings_cons `{Encode A} η p e bs (φ1 : A -> Prop) φ2 φ ψ :
  pure (eval η e) φ1 ψ ->
  bindings η bs φ2 ψ ->
  (∀ (a : A) (η' : env), φ1 a -> φ2 η' -> pattern η η' p #a φ False) ->
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hbs Hp.
  unfold bindings.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par; eauto.
  intros a1 η' Hφ1 Hφ2.
  apply pure_irrefutably_extend.
  apply Hp; auto.
Qed.

Lemma bindings_nil η (φ : env -> Prop) ψ :
  φ [] ->
  bindings η [] φ ψ.
Proof.
  unfold bindings. simpl_eval_bindings. apply pure_ret. encode.
Qed.

Lemma bindings_var `{Encode A} η v e bs (φ : A -> Prop) φ' ψ :
  pure (eval η e) φ ψ ->
  bindings η bs φ' ψ ->
  bindings η
    (Binding (PVar v) e :: bs)
    (λ η,
      ∃ a η', φ a /\ φ' η' /\ η = (v, #a) :: η') ψ.
Proof.
  intros.
  eapply bindings_cons; eauto.
  intros; unfold pattern. simpl_eval_pat.
  eapply pure_ret; eauto.
Qed.

Lemma bindings_pair `{Encode A, Encode B} η p1 p2 e bs φ φ'
  (φ1 : A -> Prop) (φ2 : B -> Prop) ψ :
  pure (eval η e) (λ '(a, b), φ1 a /\ φ2 b) ψ ->
  bindings η bs φ' ψ ->
  (∀ a b η', φ1 a -> φ2 b -> φ' η' -> pattern η η' (PPair p1 p2) #(a, b) φ False) ->
  bindings η (Binding (PPair p1 p2) e :: bs) φ ψ.
Proof.
  intros Hpure Hbs Hpat.
  eapply bindings_cons; eauto.
  intros [a b] η' [Hψ1 Hψ2] Hη'.
  auto.
Qed.


(* -------------------------------------------------------------------------- *)

(* More flexible cons rule *)

Section eval_pat_app.
  Local Ltac rew := repeat (unfold orelse, try, glue2, continue || rewrite ?bind_as_try, ?try2_try2; simpl).
  Local Ltac ext x := let o := fresh "o" in f_equal; extensionality o; destruct o as [ x | ]; auto.

  Lemma eval_pat_app p v η δ : eval_pat η δ p v = 'δ' ← eval_pat η [] p v; ret (δ' ++ δ).
  Proof.
    revert p v δ.
    apply (pat_ind
             (λ p, ∀ v δ, eval_pat η δ p v = bind (eval_pat η [] p v) (λ δ', ret (δ' ++ δ)))
             (λ ps, ∀ vs δ, eval_pats η δ ps vs = bind (eval_pats η [] ps vs) (λ δ', ret (δ' ++ δ)))
             (λ fps, ∀ vs δ, pre_eval_fpats eval_pat η δ fps vs = bind (pre_eval_fpats eval_pat η [] fps vs) (λ δ', ret (δ' ++ δ)))
          ); intros ? ?; intros; simpl_eval_pat || simpl_eval_pats || idtac; simpl; auto.
    - rewrite IHp. rewrite !bind_bind. reflexivity.
    - rewrite IHp1, IHp2. rew. ext δ'.
    - destruct v; auto.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct v; auto. rewrite IHps. rew. ext l'. destruct (locations.eqb _ _); auto.
    - destruct v; auto.
    - destruct v; auto. destruct (int.eq _ _); auto.
    - destruct v; auto. destruct (_ =? _)%char; auto.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct vs; auto.
    - destruct vs; auto. rewrite IHp. rew. ext δ1. rew.
      rewrite (IHps _ δ1), (IHps _ (δ1 ++ _)).
      rew. ext δ2. rewrite app_assoc. auto.
    - rew. ext v.
      rewrite IHp. rew. ext δ1.
      rewrite IHfps. rew.
      rewrite (IHfps _ (δ1 ++ _)). rew.
      ext δ2. rewrite app_assoc. auto.
  Qed.
End eval_pat_app.

Lemma pattern_app η δ p v φ ψ :
  pattern η δ p v φ ψ ↔ pattern η [] p v (λ δ', φ (δ' ++ δ)) ψ.
Proof.
  unfold pattern, pure.
  rewrite eval_pat_app, <-pure_wp_reversible_bind.
  apply pure_wp_ret_equiv; intros δ'.
  rewrite <-pure_wp_reversible_ret. unfold returns.
  split; intros (? & Heq & Hφ).
  - exists δ'. rewrite Heq. eauto.
  - exists (δ' ++ δ). simpl in Heq. rewrite <- Heq in Hφ. eauto.
Qed.

Definition binding `{Encode A} η p e φ ψ :=
  pure (eval η e) (λ a : A, pattern η [] p #a φ False) ψ.

Lemma binding_bindings_conseq `{Encode A} η p e bs (φ1 φ2 φ : env → Prop) ψ :
  binding (A := A) η p e φ1 ψ →
  bindings η bs φ2 ψ →
  (∀ δ η', φ1 δ → φ2 η' → φ (δ ++ η')) →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hbs Hp.
  eapply bindings_cons; eauto.
  intros a η' Hpa Hη'.
  apply pattern_app.
  eapply pure_ret_mono. apply Hpa. eauto.
Qed.

Local Instance name : @ObserveInjective env env _.
Proof. constructor. intros ??; simpl; auto. Qed.

(* May be easier to use but assumes [e] cannot raise exceptions *)
Lemma binding_bindings `{Encode A} η p e bs (φ1 φ2 φ : env → Prop) ψ :
  binding (A := A) η p e (λ δ, bindings η bs (λ η', φ (δ ++ η')) ψ) ⊥ →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He.
  unfold bindings.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par_seq.
  eapply pure_ret_mono. { apply He. } intros a Hpat_a.
  apply invert_pure_order in Hpat_a.
  eapply pure_ret_mono. { apply Hpat_a. }
  intros η' Hpat_η'.
  apply pure_irrefutably_extend.
  eapply (pattern_app η η' p ♯a φ ⊥).
  apply Hpat_η'.
Qed.
