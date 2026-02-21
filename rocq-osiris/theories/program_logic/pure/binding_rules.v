From Stdlib.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.
From osiris.lang Require Import lang ind.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Import wp judgements pattern_rules.

(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) (ψ : exn -> Prop) :=
  pure_wp (eval_bindings η bs) φ ψ.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [bindings]. *)

Lemma bindings_cons_unary `{Encode A} η p e bs φ :
  pure (eval η e)
    (λ a : A,
       pattern η [] p #a
         (λ δ1, bindings η bs (λ δ2, φ (δ1 ++ δ2)) ⊥) False) ⊥ ->
  bindings η (Binding p e :: bs) φ ⊥.
Proof.
  unfold bindings. simpl. intros He.
  simpl_eval_bindings.
  apply pure_wp_Par_vals_left.
  apply pure_wp_bind.
  apply (pure_wp_mono_ret _ He). intros v (a & -> & Ha).
  apply pure_wp_widen_pat. unfold continue; simpl.
  eapply pattern_env_mono. apply Ha. intros δ Hδ.
  apply (pure_wp_mono_ret _ Hδ). intros η' Hη'.
  apply pure_wp_ret. apply Hη'.
Qed.

Lemma bindings_cons `{Encode A} η p e bs (φ1 : A -> Prop) φ P Q ψ :
  pure (eval η e) φ1 ψ ->
  (∀ (a : A), φ1 a -> pattern η [] p #a P False) ->
  bindings η bs Q ψ ->
  (∀ η δ, P η → Q δ → φ (η ++ δ)) →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hp Hbs Hcov.
  unfold bindings.
  simpl_eval_bindings.
  eapply pure_wp_Par_conseq; eauto.
  - apply pure_wp_bind.
    apply (pure_wp_mono_ret _ He). intros ? (? & -> & Hφ1).
    apply pure_wp_widen_pat, Hp; auto.
  - intros. unfold continue; simpl.
    apply pure_wp_ret. auto.
  - intros exc Hexc. apply pure_wp_throw. tauto.
Qed.

Lemma bindings_nil η (φ : env -> Prop) ψ :
  φ [] ->
  bindings η [] φ ψ.
Proof.
  unfold bindings. simpl_eval_bindings. apply pure_wp_ret.
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
  intros; unfold pattern.
  eapply (pat_PVar _ _ _ _ (λ η, ∃ a, η = [(v,#a)] ∧ φ a)). eauto.
  intros ?? (a & -> & Hφ) Hφ'. eauto.
Qed.

Lemma bindings_pair `{Encode A, Encode B} η p1 p2 e bs φ
  (φ1 : A -> Prop) (φ2 : B -> Prop) P Q ψ :
  pure (eval η e) (λ '(a, b), φ1 a /\ φ2 b) ψ ->
  (∀ a b η', φ1 a -> φ2 b -> pattern η η' (PPair p1 p2) #(a, b) P False) ->
  bindings η bs Q ψ ->
  (∀ η δ, P η → Q δ → φ (η ++ δ)) →
  bindings η (Binding (PPair p1 p2) e :: bs) φ ψ.
Proof.
  intros Hpure Hbs Hpat Hcov.
  eapply bindings_cons; eauto.
  intros [a b] [Hψ1 Hψ2]. apply Hbs; auto.
Qed.


(* -------------------------------------------------------------------------- *)

(* More flexible cons rule *)

Section eval_pat_app.
  Local Ltac rew := repeat (unfold orelse, try, glue2, continue || rewrite ?bind_as_try, ?try2_try2; simpl).
  Local Ltac ext x := let o := fresh "o" in f_equal; extensionality o; destruct o as [ x | ]; auto.

  Local Open Scope stdpp.

  Lemma eval_pat_app p v η δ :
    eval_pat η δ p v = δ' ← eval_pat η [] p v; Some (δ' ++ δ).
  Proof.
    revert p v δ.
    apply (pat_ind
             (λ p, ∀ v δ, eval_pat η δ p v = mbind (λ δ', Some (δ' ++ δ)) (eval_pat η [] p v))
             (λ ps, ∀ vs δ, eval_pats η δ ps vs = mbind (λ δ', Some (δ' ++ δ)) (eval_pats η [] ps vs) )
             (λ fps, ∀ vs δ, pre_eval_fpats eval_pat η δ fps vs = mbind (λ δ', Some (δ' ++ δ)) (pre_eval_fpats eval_pat η [] fps vs))
          ); intros ? ?; intros; simpl_eval_pat || simpl_eval_pats || idtac; simpl; auto.
    - rewrite IHp. destruct (eval_pat η [] p v0); auto.
    - rewrite IHp1, IHp2. destruct (eval_pat η [] p1 v); simpl.
      + rewrite !union_Some_l. reflexivity.
      + rewrite !union_None_l. reflexivity.
    - destruct v; auto.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct v; auto. rewrite IHps.
      destruct (lookup_path η π); simpl; auto.
      destruct (val_as_loc_opt v0); simpl; auto.
      destruct (locations.eqb _ _); auto.
    - destruct v; auto.
    - destruct v; auto. destruct (int.eq _ _); auto.
    - destruct v; auto. destruct (_ =? _)%char; auto.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct vs; auto.
    - destruct vs; auto. rewrite IHp.
      destruct (eval_pat η [] p v); simpl; last reflexivity.
      rewrite !bind_with_Some.
      rewrite (IHps _ (e ++ δ)).
      rewrite (IHps _ e).
      destruct (eval_pats η [] ps vs); simpl; auto.
      by rewrite app_assoc.
    - destruct (lookup_name vs f); simpl; auto.
      rewrite IHp.
      destruct (eval_pat η [] p v); simpl; auto.
      rewrite IHfps.
      rewrite (IHfps _ e).
      destruct (pre_eval_fpats eval_pat η [] fps vs); simpl; auto.
      by rewrite app_assoc.
  Qed.
End eval_pat_app.

Lemma pattern_app η δ p v φ ψ :
  pattern η δ p v φ ψ ↔ pattern η [] p v (λ δ', φ (δ' ++ δ)) ψ.
Proof.
  unfold pattern.
  rewrite eval_pat_app.
  destruct (eval_pat η [] p v); auto.
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
  intros a Hpa. apply Hpa.
Qed.

(* May be easier to use but assumes [e] cannot raise exceptions *)
Lemma binding_bindings `{Encode A} η p e bs (φ1 φ2 φ : env → Prop) ψ :
  binding (A := A) η p e (λ δ, bindings η bs (λ η', φ (δ ++ η')) ψ) ⊥ →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He.
  unfold bindings.
  simpl_eval_bindings.
  apply pure_wp_Par_val_left.
  eapply pure_wp_bind_conseq; first apply He.
  intros v (a & -> & Hpa).
  apply pure_wp_widen_pat.
  unfold continue, discontinue; simpl.
  eapply pattern_env_mono; first apply Hpa.
  intros δ Hbindings.
  eapply pure_wp_mono; first apply Hbindings.
  - intros ? Hφ. apply pure_wp_ret; auto.
  - intros exc Hexc. apply pure_wp_throw; auto.
Qed.
