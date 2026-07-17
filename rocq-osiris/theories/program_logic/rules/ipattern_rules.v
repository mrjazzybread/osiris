From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang type_nel.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules.
Require Export record_rules.
From osiris.pure_logic Require Import pure.
From osiris.utils Require Import list_z big_opLZ.

(** This file defines Iris-level pattern-matching judgements.

    Matching a pattern against a record value reads the record's memory
    block, so it cannot be captured by the pure [pattern] judgement.
    [ipattern] is its Iris counterpart: the success and failure
    postconditions are [iProp]s, so that matching may consume and give
    back heap resources.

    Sub-patterns of a record are still delegated to the pure judgements
    ([fpatterns], [pattern]); nested record patterns are not supported
    for now. *)

Section ipattern.

  Context `{!osirisGS Σ}.

  Context {E : coPset} {Ψ : iEff Σ}.

  Local Instance notval_listval : NotVal (list val) := {}.

  (* [ipattern η δ p v Φ ψ] means that matching the pattern [p] against
     the value [v] is safe and either results in an extended environment
     [δ'] satisfying [Φ δ'], or fails (reduces to [throw ()]) and
     guarantees [ψ]. *)

  Definition ipattern η δ p v (Φ : env → iProp Σ) (ψ : iProp Σ) : iProp Σ :=
    imp (eval_pat η δ p v) @ E <|Ψ|> ⟨⟨ (λ _ : unit, ψ) ⟩⟩ {{ Φ }}.

  Definition icpattern η δ cp o (Φ : env → iProp Σ) (ψ : iProp Σ) : iProp Σ :=
    imp (eval_cpat η δ cp o) @ E <|Ψ|> ⟨⟨ (λ _ : unit, ψ) ⟩⟩ {{ Φ }}.

  (* A two-channel consequence rule for [impure]. *)

  Lemma imp_wand2 {V X A} `{Observe A V} (m : micro V X)
      (ζ ζ' : X → iProp Σ) (Φ Φ' : A → iProp Σ) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ a, Φ a -∗ Φ' a) ∧ (∀ e, ζ e -∗ ζ' e) -∗
    imp m @ E <|Ψ|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }}.
  Proof.
    iIntros "Hm Hw".
    iApply (imp_wand' with "Hm"). iSplit.
    - iDestruct "Hw" as "[_ $]".
    - iDestruct "Hw" as "[$ _]".
  Qed.

  Lemma ipattern_mono η δ p v Φ Φ' ψ ψ' :
    ipattern η δ p v Φ ψ -∗
    (∀ δ', Φ δ' -∗ Φ' δ') ∧ (ψ -∗ ψ') -∗
    ipattern η δ p v Φ' ψ'.
  Proof.
    iIntros "Hp Hw". iApply (imp_wand2 with "Hp").
    iSplit.
    - iDestruct "Hw" as "[$ _]".
    - iDestruct "Hw" as "[_ Hw]". iIntros (?) "H". iApply ("Hw" with "H").
  Qed.

  (* Pure pattern matching lifts to the Iris judgement. This is how
     the sub-patterns of a record go back down to the pure world. *)

  Lemma ipattern_pure η δ p v (φ : env → Prop) (ψ : Prop) :
    pattern η δ p v φ ψ →
    ⊢ ipattern η δ p v (λ δ', ⌜φ δ'⌝) ⌜ψ⌝.
  Proof.
    intros Hp. iApply impure_pure2. exact Hp.
  Qed.

  Lemma icpattern_pure η δ cp o (φ : env → Prop) (ψ : Prop) :
    cpattern η δ cp o φ ψ →
    ⊢ icpattern η δ cp o (λ δ', ⌜φ δ'⌝) ⌜ψ⌝.
  Proof.
    intros Hp. iApply impure_pure2. exact Hp.
  Qed.

  (* The continuation-passing forms of the pure-lifting lemmas: an Iris
     pattern judgement with arbitrary postconditions [Φ]/[ψ] follows
     from a pure derivation and the two wands. These are the entry
     points of the [next_branch] automation whenever a (sub-)pattern
     does not read the heap. *)

  Lemma ipattern_pure_cps η δ p v (φ : env → Prop) (ψp : Prop)
      (Φ : env → iProp Σ) (ψ : iProp Σ) :
    pattern η δ p v φ ψp →
    (∀ δ', ⌜φ δ'⌝ -∗ Φ δ') ∧ (⌜ψp⌝ -∗ ψ) -∗
    ipattern η δ p v Φ ψ.
  Proof.
    iIntros (Hp) "Hw".
    iApply (ipattern_mono with "[] Hw").
    by iApply ipattern_pure.
  Qed.

  Lemma icpattern_pure_cps η δ cp o (φ : env → Prop) (ψp : Prop)
      (Φ : env → iProp Σ) (ψ : iProp Σ) :
    cpattern η δ cp o φ ψp →
    (∀ δ', ⌜φ δ'⌝ -∗ Φ δ') ∧ (⌜ψp⌝ -∗ ψ) -∗
    icpattern η δ cp o Φ ψ.
  Proof.
    iIntros (Hp) "Hw".
    iApply (imp_wand2 with "[]").
    { by iApply icpattern_pure. }
    iSplit.
    - iDestruct "Hw" as "[$ _]".
    - iDestruct "Hw" as "[_ Hw]". iIntros ([]) "%". by iApply "Hw".
  Qed.

  (* A value pattern under a [CVal] computation pattern. *)

  Lemma icpat_CVal η δ p v Φ ψ :
    ipattern η δ p v Φ ψ -∗
    icpattern η δ (CVal p) (O3Ret v) Φ ψ.
  Proof.
    iIntros "Hp". rewrite /icpattern /=. iApply "Hp".
  Qed.

  (* Structural rules. *)

  Lemma ipat_PVar η δ x v Φ ψ :
    Φ ((x, v) :: δ) -∗
    ipattern η δ (PVar x) v Φ ψ.
  Proof.
    iIntros "HΦ". rewrite /ipattern. simpl_eval_pat.
    by iApply imp_ret.
  Qed.

  Lemma ipat_PAny η δ v Φ ψ :
    Φ δ -∗
    ipattern η δ PAny v Φ ψ.
  Proof.
    iIntros "HΦ". rewrite /ipattern. simpl_eval_pat.
    by iApply imp_ret.
  Qed.

  Lemma ipat_PAlias η δ p x v Φ ψ :
    ipattern η δ p v (λ δ', Φ ((x, v) :: δ')) ψ -∗
    ipattern η δ (PAlias p x) v Φ ψ.
  Proof.
    iIntros "Hp". rewrite /ipattern. simpl_eval_pat.
    iApply (imp_bind with "Hp").
    iIntros (δ') "HΦ".
    by iApply imp_ret.
  Qed.

  (* The Iris judgement for a list of patterns (tuple components),
     matched left to right. *)

  Definition ipatterns η δ ps vs (Φ : env → iProp Σ) (ψ : iProp Σ) : iProp Σ :=
    imp (eval_pats η δ ps vs) @ E <|Ψ|> ⟨⟨ (λ _ : unit, ψ) ⟩⟩ {{ Φ }}.

  Lemma ipats_nil η δ Φ ψ :
    Φ δ -∗
    ipatterns η δ [] [] Φ ψ.
  Proof.
    iIntros "HΦ". rewrite /ipatterns. simpl_eval_pats.
    by iApply imp_ret.
  Qed.

  Lemma ipats_cons η δ p ps v vs Φ ψ :
    ipattern η δ p v (λ δ', ipatterns η δ' ps vs Φ ψ) ψ -∗
    ipatterns η δ (p :: ps) (v :: vs) Φ ψ.
  Proof.
    iIntros "Hp". rewrite /ipatterns. simpl_eval_pats.
    iApply (imp_bind with "Hp").
    iIntros (δ') "Hps".
    iApply (imp_bind with "Hps").
    iIntros (δ'') "HΦ".
    by iApply imp_ret.
  Qed.

  Lemma ipat_PTuple η δ ps vs Φ ψ :
    ipatterns η δ ps vs Φ ψ -∗
    ipattern η δ (PTuple ps) (VTuple vs) Φ ψ.
  Proof.
    iIntros "Hps". rewrite /ipattern. simpl_eval_pat.
    iApply "Hps".
  Qed.

  (* The same rule with an explicit encoding premise, so that it applies
     to an encoded tuple value [#a]. This is the form used by the
     [next_branch] automation. *)

  Lemma ipat_PTuple' η δ ps v vs Φ ψ :
    v = VTuple vs →
    ipatterns η δ ps vs Φ ψ -∗
    ipattern η δ (PTuple ps) v Φ ψ.
  Proof.
    iIntros (->) "Hps". by iApply ipat_PTuple.
  Qed.

  (* Rules for inline-record patterns: the constructor comparison is
     pure; the sub-pattern is matched against the underlying record. *)

  Lemma ipat_PInline_eq η δ c p v l Φ ψ :
    v = VInline c l →
    ipattern η δ p (VRecord l) Φ ψ -∗
    ipattern η δ (PInline c p) v Φ ψ.
  Proof.
    iIntros (->) "Hp". rewrite /ipattern. simpl_eval_pat.
    rewrite String.eqb_refl. iApply "Hp".
  Qed.

  Lemma ipat_PInline_neq η δ c c' p l Φ ψ :
    c ≠ c' →
    ψ -∗
    ipattern η δ (PInline c p) (VInline c' l) Φ ψ.
  Proof.
    iIntros (Hne) "Hψ". rewrite /ipattern. simpl_eval_pat.
    rewrite (proj2 (String.eqb_neq c c')); last assumption.
    by iApply imp_throw.
  Qed.

  (* Reading all the fields of a block. *)

  Lemma imp_loadn {X} (ζ : X → iProp Σ) (q : Qp) ls (vs : list val) :
    ([∗ listZ] l;v ∈ ls; vs, l ↦{#q} v) -∗
    imp (loadn ls) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ vs' : list val,
        ⌜vs' = vs⌝ ∗ [∗ listZ] l;v ∈ ls; vs, l ↦{#q} v }}.
  Proof.
    iInduction ls as [|l ls] "IH" forall (vs); iIntros "Hls"; simpl.
    - iDestruct (big_sepLZ2_nil_inv_l with "Hls") as %->.
      iApply imp_ret; first done.
      iSplit; first done. by iApply big_sepLZ2_nil.
    - iDestruct (big_sepLZ2_cons_inv_l with "Hls") as (v vs' ->) "[Hl Hls]".
      iApply (imp_stop_load with "Hl").
      iIntros "!> Hl /=".
      iApply (imp_bind (A1:=list val) with "[Hls]").
      { iApply ("IH" with "Hls"). }
      iIntros (vs'') "[-> Hls] /=".
      iApply imp_ret; first done.
      iSplit; first done.
      iFrame.
  Qed.

  (* The main rule: matching a record pattern against a record value
     reads the record's fields and then matches the field patterns
     purely. The ownership of the block is given back in both the
     success and the failure branch. *)

  Lemma ipat_PRecord {τ : types} η δ fps (r : record) q t (xs : τ)
      (φ : env → Prop) (ψ : Prop) :
    fpatterns η δ fps (to_vals xs) φ ψ →
    ownBlock r q t xs -∗
    ipattern η δ (PRecord fps) (VRecord r)
      (λ δ', ⌜φ δ'⌝ ∗ ownBlock r q t xs)
      (⌜ψ⌝ ∗ ownBlock r q t xs).
  Proof.
    iIntros (Hfps) "Hown". rewrite /ipattern. simpl_eval_pat.
    iDestruct "Hown" as "(%ls & #Hlocs & Htag & Hxs)".
    iApply (imp_bind (A1:=mut_tag * list loc)).
    { iApply (imp_load_block_ghost with "Hlocs"). }
    iIntros ((t' & ls')) "-> /=".
    iApply (imp_bind (A1:=list val) with "[Hxs]").
    { iApply (imp_loadn with "Hxs"). }
    iIntros (vs) "[-> Hxs] /=".
    iApply (imp_wand2 with "[] [-]").
    { iApply impure_pure2. exact Hfps. }
    iSplit.
    - iIntros (δ') "%". iSplit; first done.
      iExists ls. iFrame "∗#".
    - iIntros (?) "%". iSplit; first done.
      iExists ls. iFrame "∗#".
  Qed.

  (* The same rule, phrased on a user-provided logical model of the
     record (see [RecordRepr] in [record_rules]). *)

  Lemma ipat_PRecord_repr `{RecordRepr A τ t} η δ fps r q (a : A)
      (φ : env → Prop) (ψ : Prop) :
    fpatterns η δ fps (to_vals (repr_to_types a)) φ ψ →
    ownRecord r q a -∗
    ipattern η δ (PRecord fps) (VRecord r)
      (λ δ', ⌜φ δ'⌝ ∗ ownRecord r q a)
      (⌜ψ⌝ ∗ ownRecord r q a).
  Proof.
    intros Hfps. iApply ipat_PRecord. exact Hfps.
  Qed.

  (* Continuation-passing forms of the record rules, used by the
     [next_branch] automation: the success postcondition [Φ] is left
     untouched (so that it can be threaded, as an evar or as the branch
     body, through the surrounding pattern rules), and the caller
     receives the environment extension [φ] and the block's ownership
     back in a wand premise. Field patterns must be irrefutable
     ([ψp → False]), which is the case for the variable and wildcard
     sub-patterns that the automation supports. *)

  Lemma ipat_PRecord_cps {τ : types} η δ fps v (r : record) q t (xs : τ)
      (φ : env → Prop) (ψp : Prop) (Φ : env → iProp Σ) (ψ : iProp Σ) :
    v = VRecord r →
    fpatterns η δ fps (to_vals xs) φ ψp →
    (ψp → False) →
    ownBlock r q t xs -∗
    (∀ δ', ⌜φ δ'⌝ -∗ ownBlock r q t xs -∗ Φ δ') -∗
    ipattern η δ (PRecord fps) v Φ ψ.
  Proof.
    iIntros (-> Hfps Hψ) "Hown Hk".
    iApply (ipattern_mono with "[Hown]").
    { iApply (ipat_PRecord with "Hown"). exact Hfps. }
    iSplit.
    - iIntros (δ') "[%Hφ Hown]". iApply ("Hk" with "[//] Hown").
    - iIntros "[%Hp _]". destruct (Hψ Hp).
  Qed.

  Lemma ipat_PRecord_repr_cps `{RecordRepr A τ t} η δ fps v r q (a : A)
      (φ : env → Prop) (ψp : Prop) (Φ : env → iProp Σ) (ψ : iProp Σ) :
    v = VRecord r →
    fpatterns η δ fps (to_vals (repr_to_types a)) φ ψp →
    (ψp → False) →
    ownRecord r q a -∗
    (∀ δ', ⌜φ δ'⌝ -∗ ownRecord r q a -∗ Φ δ') -∗
    ipattern η δ (PRecord fps) v Φ ψ.
  Proof.
    iIntros (-> Hfps Hψ) "Hown Hk".
    iApply (ipattern_mono with "[Hown]").
    { iApply (ipat_PRecord_repr with "Hown"). exact Hfps. }
    iSplit.
    - iIntros (δ') "[%Hφ Hown]". iApply ("Hk" with "[//] Hown").
    - iIntros "[%Hp _]". destruct (Hψ Hp).
  Qed.

End ipattern.
