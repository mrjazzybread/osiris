From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Import wp judgements pattern_rules.

(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) (ψ : exn -> Prop) :=
  pure_wp (eval_bindings η bs) φ ψ.

Lemma pure_wp_irrefutably_extend η δ p v φ ψ :
  pure_wp (extend η δ p v) φ ⊥ →
  pure_wp (irrefutably_extend η δ p v) φ ψ.
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
  simpl_eval_bindings.
  apply pure_wp_Par_vals_left.
  apply (pure_wp_mono_ret _ He). intros v (a & -> & Ha).
  apply (pure_wp_mono_ret _ Ha). intros η' Hη'.
  eapply pure_wp_widen, pure_wp_try_conseq. eauto.
  intros. by apply pure_wp_ret. intros _ [].
Qed.

Lemma bindings_cons `{Encode A} η p e bs (φ1 : A -> Prop) φ2 φ ψ :
  pure (eval η e) φ1 ψ ->
  bindings η bs φ2 ψ ->
  (∀ (a : A) (η' : env), φ1 a -> φ2 η' -> pattern η η' p #a φ False) ->
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hbs Hp.
  unfold bindings.
  simpl_eval_bindings.
  eapply pure_wp_Par_conseq; eauto.
  - intros _ η' (a & -> & Ha) Hη'.
    eapply pure_wp_bind, pure_wp_ret, pure_wp_widen, pure_wp_irrefutably_extend. apply Hp; eauto.
  - intros. eapply pure_wp_bind, pure_wp_throw. tauto.
Qed.

Lemma bindings_nil `{Encode A} η (φ : env -> Prop) ψ :
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
  intros; unfold pattern. simpl_extend.
  apply pure_wp_ret; eauto.
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
