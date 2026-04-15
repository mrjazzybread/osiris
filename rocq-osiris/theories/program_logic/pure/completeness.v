From osiris Require Import base.
From osiris.lang Require Import syntax encode notations locations.
From osiris.semantics Require Import semantics.
From osiris.program_logic.pure Require Import pure_rules pattern_rules.

(* Completeness/reversibility of some rules -- useful to check that we did not
forget any case in the rules that we show *)

(** Different versions for [POr] *)

Lemma reversible_pat_POr_unary η δ p1 p2 v φ ψ :
  pattern η δ p1 v φ (pattern η δ p2 v φ ψ)
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  unfold pattern. simpl_eval_pat.
  destruct (eval_pat η δ p1 v).
  - by rewrite union_Some_l.
  - by rewrite union_None_l.
Qed.

Lemma reversible_pat_POr η δ p1 p2 v φ ψ :
  (∃ ψ1, pattern η δ p1 v φ ψ1 ∧ (ψ1 → pattern η δ p2 v φ ψ))
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  rewrite <-reversible_pat_POr_unary.
  firstorder eauto using pattern_mono_exn.
Qed.

Lemma reversible_pat_POr_2 η δ p1 p2 v φ (ψ : Prop) :
  (∃ ψ1 ψ2,
    pattern η δ p1 v φ ψ1 ∧
    (ψ1 → pattern η δ p2 v φ ψ2) ∧
    (ψ1 ∧ ψ2 → ψ))
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  rewrite <-reversible_pat_POr.
  firstorder eauto using pattern_mono_exn.
Qed.


(** [PData] *)

Lemma reversible_pat_PData_nil η δ c c' (φ : env → Prop) (ψ : Prop) :
  (c = c' → φ δ)
  <->
  pattern η δ (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb; tauto.
Qed.

Lemma reversible_pat_PData_or η δ c c' ps vs φ ψ :
  (c = c' -> patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PData c ps) (VData c' vs) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb.
  - unfold patterns.
    destruct (eval_pats η δ ps vs); tauto.
  - tauto.
Qed.


(** [PXData], assuming the path lookup is safe *)

Lemma reversible_pat_PXData η δ π ps l l' vs φ ψ :
  lookup_path η π = Some #l' →
  (l = l' → patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PXData π ps) (VXData l vs) φ (ψ ∨ l ≠ l').
Proof.
  unfold pattern. simpl_eval_pat. intros ->; simpl.
  destruct (eqb_spec l l').
  - unfold patterns.
    destruct (eval_pats η δ ps vs); tauto.
  - tauto.
Qed.
