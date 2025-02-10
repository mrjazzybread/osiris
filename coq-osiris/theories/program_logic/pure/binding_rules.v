From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Import wp judgements pattern_rules.

(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) :=
  pure_wp (eval_bindings η bs) φ (λ _, False).

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [bindings]. *)

Lemma bindings_cons `{Encode A} η p e bs φ φ' (ψ : A -> Prop) :
  pure (eval η e) ψ ⊥ ->
  bindings η bs φ' ->
  (∀ (x : A) (η' : env), ψ x -> φ' η' -> pattern η η' p #x φ False) ->
  bindings η ((Binding p e) :: bs) φ.
Proof.
  unfold bindings. simpl. intros Hpure_wp Hbs Hcov.
  simpl_eval_bindings.
  apply pure_wp_Par_vals_left.
  apply (pure_wp_mono_ret _ Hpure_wp). intros v (a & -> & Ha).
  apply (pure_wp_mono_ret _ Hbs). intros η' Hη'.
  eapply pure_wp_widen, pure_wp_try_conseq. by apply Hcov.
  intros. by apply pure_wp_ret. intros _ [].
Qed.

Lemma bindings_nil `{Encode A} η (φ : env -> Prop) :
  φ [] ->
  bindings η [] φ.
Proof.
  unfold bindings. simpl_eval_bindings. apply pure_wp_ret.
Qed.

Lemma bindings_var `{Encode A} η v e bs φ' (ψ : A -> Prop) :
  pure (eval η e) ψ ⊥ ->
  bindings η bs φ' ->
  bindings η
    (Binding (PVar v) e :: bs)
    (λ η,
      ∃ a η', ψ a /\ φ' η' /\ η = (v, #a) :: η').
Proof.
  intros.
  eapply bindings_cons; eauto.
  intros; unfold pattern. simpl_extend.
  apply pure_wp_ret; eauto.
Qed.

Lemma bindings_pair `{Encode A, Encode B} η p1 p2 e bs φ φ'
  (ψ1 : A -> Prop) (ψ2 : B -> Prop) :
  pure (eval η e) (λ '(a, b), ψ1 a /\ ψ2 b) ⊥ ->
  bindings η bs φ' ->
  (∀ a b η', ψ1 a -> ψ2 b -> φ' η' -> pattern η η' (PPair p1 p2) #(a, b) φ False) ->
  bindings η (Binding (PPair p1 p2) e :: bs) φ.
Proof.
    intros Hpure Hbs Hpat.
  eapply bindings_cons; eauto.
  intros [a b] η' [Hψ1 Hψ2] Hη'.
  auto.
Qed.
