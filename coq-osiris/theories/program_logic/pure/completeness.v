From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar locations.
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
  apply pure_wp_reversible_orelse.
Qed.

Lemma reversible_pat_POr η δ p1 p2 v φ ψ :
  (∃ ψ1, pattern η δ p1 v φ ψ1 ∧ (ψ1 → pattern η δ p2 v φ ψ))
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  rewrite <-reversible_pat_POr_unary.
  firstorder eauto using pattern_exn_mono.
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
  firstorder eauto using pattern_exn_mono.
Qed.


(** [PData] *)

Lemma reversible_pat_PData_nil η δ c c' (φ : env → Prop) (ψ : Prop) :
  (c = c' → φ δ)
  <->
  pattern η δ (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb.
  rewrite <-pure_wp_reversible_ret. tauto.
  rewrite <-pure_wp_reversible_throw. tauto.
Qed.

Lemma reversible_pat_PData_or η δ c c' ps vs φ ψ :
  (c = c' -> patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PData c ps) (VData c' vs) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb.
  - assert (ψ ↔ (ψ ∨ c ≠ c')) by tauto.
    unfold patterns.
    firstorder eauto using pure_wp_mono_throw.
    eapply pure_wp_mono_throw. apply H2. tauto.
  - rewrite <-pure_wp_reversible_throw. tauto.
Qed.


(** [PXData], assuming the path lookup is safe *)

Lemma reversible_pat_PXData η δ π ps l l' vs φ ψ :
  lookup_path η π = ret (VLoc l') →
  (l = l' → patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PXData π ps) (VXData l vs) φ (ψ ∨ l ≠ l').
Proof.
  unfold pattern. simpl_eval_pat. intros ->.
  change (as_loc (widen (ret (VLoc l')))) with (@ret _ unit l'). rewrite bind_ret.
  destruct (eqb_spec l l').
  - unfold patterns.
    assert ((ψ ∨ l ≠ l') → ψ) by tauto.
    firstorder eauto using pure_wp_mono_throw.
    eapply pure_wp_mono_throw. eassumption. tauto.
  - rewrite <-pure_wp_reversible_throw. tauto.
Qed.



(** [PXData] but making no such assumption *)

Lemma lookup_name_cases η x : (∃ v, lookup_name η x = ret v) ∨ lookup_name η x = crash (String.app "missing_variable_or_field: " x).
Proof.
  induction η as [ | (y, v) η ]. eauto.
  simpl. destruct (x =? y)%string;eauto.
Qed.

Lemma lookup_path_cases η π : (∃ v, lookup_path η π = ret v) ∨ ∃ s, lookup_path η π = crash s.
Proof.
  revert η; induction π as [ | x π ]; intros η. eauto. simpl.
  destruct (lookup_name_cases η x) as [(v, ->) | ->]; simpl.
  - destruct π; eauto.
    destruct v; eauto. simpl val_as_struct.
    rewrite bind_ret.
    destruct (IHπ xvs) as [(v & ->) | ?]; eauto.
  - destruct π; eauto.
Qed.

Lemma reversible_pat_PXData_general η δ π ps l vs φ (ψ : Prop) :
  (∃ l',
      lookup_path η π = ret (VLoc l') ∧
      (l = l' → patterns η δ ps vs φ ψ) ∧
      (l ≠ l' → ψ))
  <->
  pattern η δ (PXData π ps) (VXData l vs) φ ψ.
Proof.
  split.
  - firstorder.
    eapply pattern_exn_mono.
    + apply reversible_pat_PXData; eauto.
    + tauto.
  - unfold pattern. simpl_eval_pat.
    destruct (lookup_path_cases η π) as [[v ->] | [s ->]]. 2: intros []%invert_pure_wp_crash.
    assert (widen (ret v) = ret v) as -> by reflexivity.
    destruct v; try intros []%invert_pure_wp_crash.
    unfold as_loc; simpl. rewrite bind_ret.
    destruct (eqb_spec l l0) as [E | N].
    + firstorder.
    + intros H%invert_pure_wp_throw; firstorder.
Qed.
