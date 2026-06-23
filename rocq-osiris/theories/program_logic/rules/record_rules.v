From iris Require Import gen_heap proofmode.proofmode.
From iris.bi.lib Require Import fractional.
From osiris Require Import lang type_nel.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules.
From osiris.utils Require Import list_z big_opLZ.

(** This file defines record resource predicates and [imp] rules for record expressions. *)

Section record_resources.

  Context `{!osirisGS Σ}.

  (* [ownBlock r qp t xs] is the representation predicate for a block of memory:
     - [r] is the location at which the block is stored
     - [qp] is the fraction of the ownership carried
     - [t] is the tag [Mut/Immut] of the block (for allowing physical equality)
     - [xs] is the logical representation of the block as a tuple *)

  Definition ownBlock {τ : types} (r : record) qp (t : mut_tag) (xs : τ) : iProp Σ :=
    ∃ ls, isBlockLocs r ls ∗ isBlock r (DfracOwn qp) t ∗
      [∗ listZ] l;v ∈ ls; (to_vals xs), l ↦{#qp} v.

End record_resources.

Section record_resources_frac.

  Context `{!osirisGS Σ}.

  Local Lemma isBlock_split (b : locations.loc) p q t :
    isBlock b (DfracOwn (p + q)) t ⊣⊢ isBlock b (DfracOwn p) t ∗ isBlock b (DfracOwn q) t.
  Proof.
    unfold isBlock. iSplit.
    - iIntros "(%ls & Hb)".
      iDestruct "Hb" as "[Hb1 Hb2]".
      iSplitL "Hb1"; iExists ls; iFrame.
    - iIntros "([%ls1 Hb1] & [%ls2 Hb2])".
      iPoseProof (gen_heap.pointsto_agree with "Hb1 Hb2") as "%Heq". simplify_eq.
      iExists ls2. iCombine "Hb1 Hb2" as "Hb". iFrame.
  Qed.

  Global Instance isBlock_fractional (b : locations.loc) t :
    Fractional (λ q, isBlock b (DfracOwn q) t).
  Proof. intros p q. rewrite isBlock_split //. Qed.

  Global Instance isBlock_as_fractional (b : locations.loc) q t :
    AsFractional (isBlock b (DfracOwn q) t) (λ q, isBlock b (DfracOwn q) t) q.
  Proof. constructor; done || apply _. Qed.

  Global Instance ownBlock_fractional {τ : types} (r : record) t (xs : τ) :
    Fractional (λ q, ownBlock r q t xs).
  Proof.
    intros p q. unfold ownBlock. iSplit.
    - iIntros "(%ls & #Hblock & Htag & Hxs)".
      iDestruct (isBlock_split r p q t with "Htag") as "[Htag1 Htag2]".
      iAssert ([∗ listZ] l;v ∈ ls; (to_vals xs), l ↦{DfracOwn p} v ∗ l ↦{DfracOwn q} v)%I
        with "[Hxs]" as "Hxs'".
      { iApply (big_sepLZ2_mono with "Hxs").
        intros k l v _ _. iIntros "[Hl1 Hl2]". iFrame. }
      rewrite big_sepLZ2_sep.
      iDestruct "Hxs'" as "[Hxs1 Hxs2]".
      iSplitL "Htag1 Hxs1"; iExists ls; iFrame "#∗".
    - iIntros "([%ls1 (#Hblock1 & Htag1 & Hxs1)] & [%ls2 (#Hblock2 & Htag2 & Hxs2)])".
      iPoseProof (isBlockLocs_valid with "Hblock1 Hblock2") as "<-".
      iExists ls2. iFrame "Hblock1".
      iSplitL "Htag1 Htag2". { rewrite isBlock_split. iFrame. }
      iAssert ([∗ listZ] l;v ∈ ls2; to_vals xs, l ↦{DfracOwn p} v ∗ l ↦{DfracOwn q} v)%I
        with "[Hxs1 Hxs2]" as "Hxs".
      { rewrite big_sepLZ2_sep. iFrame. }
      iApply (big_sepLZ2_mono with "Hxs").
      intros k l v _ _. iIntros "[Hl1 Hl2]". iCombine "Hl1 Hl2" as "$".
  Qed.

  Global Instance ownBlock_as_fractional {τ : types} (r : record) q t (xs : τ) :
    AsFractional (ownBlock r q t xs) (λ q, ownBlock r q t xs) q.
  Proof. constructor; done || apply _. Qed.

End record_resources_frac.

Section records_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_as_record {ζ} {Φ : record → iProp Σ} (m : microvx) :
    imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    impure E (as_record m) Ψ ζ Φ.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (r) "HΦ".
    iApply (imp_ret with "HΦ"). encode.
  Qed.

  Local Instance notval_listval : NotVal (list val) := {}.

  Lemma imp_ERecord {τ : types} {ζ} (Φs : τ -#> iProp Σ) t es :
    τ_length τ ≤ max_array_length →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ
      (λ r, ∃# (xs : τ), ownBlock r 1 t xs ∗ Φs xs).
  Proof.
    iIntros "%Hlength Hes". simpl_eval.
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

  Lemma imp_ERecordAccess2 {τ : types} {ζ} f {Φ : (τ !!! f) → iProp Σ} r ls e :
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    (∃ dq t (xs : τ),
      ▷ (⌜valid_field f τ⌝ ∗ ownBlock r dq t xs) ∗
      ▷ (ownBlock r dq t xs -∗ Φ (xs !!τ f))) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros "#Hblock He P". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iDestruct "P" as
        "(%dq & %t & %xs & P1 & P2)".
    iCombine "Hblock P1 P2" as "P".

    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[P]").
    { iApply (imp_load_block_ghost' with "Hblock P"). }
    iIntros ((? & ?)) "(-> & #Hblock' & (%Hvalid_field & Hown) & HΦ) /=".
    iClear "Hblock".

    iDestruct "Hown" as "(%ls' & #Hblock & Htag & Hxs)".
    iPoseProof (isBlockLocs_valid with "Hblock' Hblock") as "->".
    iPoseProof (isBlockLocs_length with "Hblock") as "%Hlen".
    iPoseProof (big_sepLZ2_length with "Hxs") as "%Hlen_xs".
    assert (valid f ls) as Hvalid.
    { destruct Hvalid_field. split; first lia.
      rewrite Hlen_xs to_vals_length. assumption. }

    rewrite (list_lookup_lookup_total_valid ls f Hvalid).

    iPoseProof (big_sepLZ2_lookup_acc _ ls (to_vals xs) f with "Hxs") as "(Hx & Hxs)".
    { apply list_lookup_lookup_total_valid. assumption. }
    { instantiate (1:= #(xs !!τ f)).
      transitivity (@Some val ((to_vals xs) !!! f)).
      - apply list_lookup_lookup_total_valid.
        rewrite <- Hlen_xs. assumption.
      - f_equal.
        apply lookup_total_to_vals. }
    iApply (imp_load' with "Hx").
    iIntros "!> Hx".
    iApply "HΦ".
    iExists ls. iFrame "∗#".
    iApply ("Hxs" with "Hx").
  Qed.

  Lemma imp_ERecordAccess {τ : types} {ζ} (r : record) f dq t (xs : τ) e :
    valid_field f τ →
    ▷ ownBlock r dq t xs -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ
      (λ (x : τ !!! f), ⌜x = xs !!τ f⌝  ∗ ownBlock r dq t xs).
  Proof.
    iIntros (Hvalid_field) "Hown He".
    iDestruct "Hown" as "(%ls & #Hblock & Htag & Hxs)".
    iApply (imp_ERecordAccess2 with "Hblock He").
    iExists dq, t, xs.
    iSplitL "Htag Hxs"; iNext.
    - iFrame "∗#%".
    - iIntros "$ //".
  Qed.

  Lemma imp_ERecordSet2 {τ : types} {ζ} f {Φ : unit → iProp Σ} (Φ1 : record → iProp Σ) (Φ2 : τ !!! f → iProp Σ) e1 e2 :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ r a, Φ1 r -∗ Φ2 a -∗
            ∃ t (xs : τ),
              ▷ (⌜valid_field f τ⌝ ∗ ownBlock r 1 t xs) ∗
              ▷ (ownBlock r 1 t <[f τ= a]> xs -∗ Φ ())) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_record with "He1"). }
    iIntros (r a) "HΦ1 HΦ2".
    iDestruct ("P" with "HΦ1 HΦ2") as
        "(%j & %xs & Hown & HΦ)". iNext.
    iDestruct "Hown" as "(%Hvalid_field & Hown)".
    iDestruct "Hown" as "(%ls & #Hblock & Htag & Hxs)".
    iPoseProof (isBlockLocs_length with "Hblock") as "%Hlen_ls".
    iPoseProof (big_sepLZ2_length with "Hxs") as "%Hlen_xs".

    iApply imp_bind. { iApply (imp_load_block_ghost with "Hblock"). }
    iIntros ((t & ls')) "-> /=".

    assert (valid f ls) as Hvalid.
    { destruct Hvalid_field. split; first lia.
      rewrite Hlen_xs to_vals_length. assumption. }

    rewrite (list_lookup_lookup_total_valid ls f Hvalid).

    iPoseProof (big_sepLZ2_insert_acc _ ls (to_vals xs) f with "Hxs") as "(Hx & Hxs)".
    { apply list_lookup_lookup_total_valid. assumption. }
    { instantiate (1:= #(xs !!τ f)).
      transitivity (@Some val ((to_vals xs) !!! f)).
      - apply list_lookup_lookup_total_valid.
        rewrite <- Hlen_xs. assumption.
      - f_equal.
        apply lookup_total_to_vals. }
    iApply (imp_store' with "Hx").
    iIntros "!> Hx".
    iApply "HΦ".
    iExists ls. iFrame "∗#".
    iSpecialize ("Hxs" with "Hx").
    update. rewrite insert_to_vals.
    iApply "Hxs".
  Qed.

  Lemma imp_ERecordSet {τ : types} {ζ} f (Φ : τ !!! f → iProp Σ) (r : record) t (xs : τ) e1 e2 :
    valid_field f τ →
    ▷ ownBlock r 1 t xs -∗
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ
      (λ (_ : unit), ∃ a, Φ a ∗ ownBlock r 1 t (<[f τ= a]> xs)).
  Proof.
    iIntros (Hvalid_field) "Hown He1 He2".
    iApply (imp_ERecordSet2 with "He1 He2").
    iIntros (? a) "-> HΦ".
    iFrame "∗%".
    iIntros "!> Hown".
    iFrame.
  Qed.

End records_reasoning.

(* So far, our logical model of records has been tuples. Although this
   is sufficiently expressive for most purposes, we can allow users to
   provide their own logical model by mapping to our tuples. *)

Section encoded_fields.

  Context `{!osirisGS Σ}.

  (* [RecordRepr A τ t] ties a logical model type [A] to a record with
     fields described by [τ] and with mutable tag [t]. *)

  (* For example, a record type [point := { x : Z; y : Z }] would need
     an instance [RecordRepr point τ[Z; Z] (Mut/Immut)]. *)

  Class RecordRepr (A : Type) (τ : types) (t : mut_tag) :=
    { repr_to_types : A → τ;
      types_to_repr : τ -#> A;
      repr_id : ∀ xs, (repr_to_types ∘ types_to_repr) xs = xs }.

  (* [ownRecord] defines the ownership of a record with logical model [a : A]. *)

  Definition ownRecord `{RecordRepr A τ t} (r : record) qp (a : A) : iProp Σ :=
    ownBlock (τ:=τ) r qp t (repr_to_types a).

  Instance ownRecord_fractional `{RecordRepr A τ t} r (a : A) : Fractional (λ qp, ownRecord r qp a) := _.

  Global Instance ownRecord_as_fractional `{RecordRepr A t} (r : record) q (a : A) :
    AsFractional (ownRecord r q a) (λ q, ownRecord r q a) q.
  Proof. constructor; done || apply _. Qed.

  (* -------------------------------------------------------------------------- *)

  (* We can now redefine reasoning rules in terms of user-provided
     logical models, instead of tuples. *)

  Lemma imp_record `{RecordRepr A τ t} {η E Ψ ζ} es (Φs : τ -#> iProp Σ) :
    (τ_length τ ≤ max_array_length)%Z →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ (λ r, ∃# (xs : τ), ownRecord r 1 (types_to_repr xs) ∗ Φs xs).
  Proof.
    iIntros (Hlength) "Hes".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecord with "Hes"). assumption. }
    iIntros (r).
    rewrite !bi_texist_equiv.
    iIntros "(%xs & Hr & HΦ)".
    iFrame. unfold ownRecord.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hr".
  Qed.

  Lemma imp_record_access `{RecordRepr A τ t} {η E Ψ ζ} f (r : record) (qp : Qp) (a : A) (e : expr) :
    valid_field f τ →
    ▷ ownRecord r qp a -∗
    impure E (eval η e) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ (λ (x : τ !!! f), ⌜x = repr_to_types a !!τ f⌝ ∗ ownRecord r qp a).
  Proof.
    iIntros (Hvalid) "Hown He".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordAccess with "Hown He"). assumption. }
    iIntros (x) "($ & $)".
  Qed.

  (* Despite what we might expect, we do not require the record to be
     mutable for an update to occur. The OCaml typechecker should make
     such a situation impossible, so we only expect this to be relevant
     in the case where unsafe type coercions were used. In such a case,
     our semantics allow updating records with "immutable" fields as
     long as we have full ownership. *)

  Lemma imp_record_update `{RecordRepr A τ t} {η E Ψ ζ} (r : record) f (a : A) e1 e2 Φ :
    valid_field f τ →
    ▷ ownRecord r 1 a -∗
    impure E (eval η e1) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ
      (λ _ : unit, ∃ (x : τ !!! f), Φ x ∗ ownRecord r 1 (types_to_repr (<[ f τ= x]> (repr_to_types a)))).
  Proof.
    iIntros (Hvf) "Hown He1 He2".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordSet with "Hown He1 He2"). exact Hvf. }
    iIntros (_) "(%x & HΦ & Hrecord)".
    iExists x. iFrame "HΦ".
    unfold ownRecord.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hrecord".
  Qed.

End encoded_fields.

Notation "r ⤇ a" :=
  (ownRecord r 1 a)
    (at level 20, format "r  ⤇  a").
Notation "r ⤇{ qp } a" :=
  (ownRecord r qp a)
    (at level 20, qp at level 1, format "r  ⤇{ qp }  a") : bi_scope.
