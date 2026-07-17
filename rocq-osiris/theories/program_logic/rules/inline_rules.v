From iris Require Import gen_heap proofmode.proofmode.
From iris.bi.lib Require Import fractional.
From osiris Require Import lang type_nel.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules.
Require Export record_rules.
From osiris.utils Require Import list_z big_opLZ.

(** This file defines record resource predicates and [imp] rules for inline-records. *)

Section inline_record_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.

  Local Instance notval_listval : NotVal (list val) := {}.

  Local Instance encode_record c : Encode record := { encode' r := VInline c r }.

  Lemma imp_EInline {τ : types} {ζ} (Φs : τ -#> iProp Σ) c t es :
    let encode_rec := encode_record c in
    τ_length τ ≤ max_array_length →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (EInline c t es)) Ψ ζ
      (λ r, ∃# (xs : τ), ownBlock r 1 t xs ∗ Φs xs).
  Proof.
    iIntros (?) "%Hlength Hes". simpl_eval.
    iApply (imp_bind with "Hes").
    iIntros (xs) "HΦs".
    iApply imp_bind.
    { simpl.
      replace (to_vals xs) with
      (@observe (list val) (list val) (@observe_list val Encode_val) (to_vals xs)).
      iApply (@imp_allocn _ _ _ _ _ val Encode_val (λ ls, [∗ listZ] l;v ∈ ls; (to_vals xs), l ↦ v)%I (to_vals xs)).
      iIntros "!>" (ls) "$".
      simpl. rewrite map_id. reflexivity. }
    iIntros (ls) "Hls".
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlength_ls".
    iApply imp_bind.
    { iApply imp_alloc_block.
      iPureIntro. simpl.
      rewrite Hlength_ls. rewrite to_vals_length. assumption. }
    iIntros (r) "(Hmut & Hblocks)".
    iApply imp_ret. encode.
    rewrite bi_texist_equiv. iFrame.
  Qed.

End inline_record_reasoning.

(* The [RecordRepr]/[ownRecord] machinery from [record_rules] applies to
   inline records as well; we restate the construction rule in terms of a
   user-provided logical model. *)

Section encoded_fields.

  Context `{!osirisGS Σ}.

  Lemma imp_inline_record `{RecordRepr A τ t} {η E Ψ ζ} c es (Φs : τ -#> iProp Σ) :
    let encode_rec := encode_record c in
    (τ_length τ ≤ max_array_length)%Z →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (EInline c t es)) Ψ ζ (λ r, ∃# (xs : τ), ownRecord r 1 (types_to_repr xs) ∗ Φs xs).
  Proof.
    iIntros (? Hlength) "Hes".
    iApply (imp_wand with "[-]").
    { iApply (imp_EInline with "Hes"). assumption. }
    iIntros (r).
    rewrite !bi_texist_equiv.
    iIntros "(%xs & Hr & HΦ)".
    iFrame. unfold ownRecord.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hr".
  Qed.

End encoded_fields.
