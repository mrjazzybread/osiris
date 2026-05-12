From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang type_nel.
From osiris.tactics Require Import osiris_utils.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z big_opLZ.

(** This file defines record resource predicates and [imp] rules for record expressions. *)

Section record_resources.

  Context `{!osirisGS Σ}.

  Fixpoint to_vals {τ : types} : τ-#> list val :=
    match τ with
    | Tbase H => tbind (λ x, [ #x])
    | @type_nel.Tcons X H b =>
      λ (x : X), @tbind _ b (λ tt, #x :: (to_vals tt))
    end.

  Fixpoint length (τ : types) : Z :=
    match τ with
    | Tbase _ => 1
    | type_nel.Tcons _ τ => 1 + length τ
    end.

  Lemma to_vals_length (τ : types) :
    ∀ (xs : τ), list_z.length (to_vals xs) = length τ.
  Proof.
    induction τ.
    - intros x. simpl. unfold tapp. by rewrite length_singleton.
    - intros (x & xs). simpl. rewrite tapp_bind. length.
      rewrite IHτ. lia.
  Qed.

  Definition ownRecord {τ : types} (r : record) dq (t : mut_tag) (xs : τ) : iProp Σ :=
    ∃ ls, isBlockLocs r ls ∗ r ⤇{dq} t ∗
      [∗ listZ] l;v ∈ ls; (to_vals xs), l ↦{dq} v.

End record_resources.

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

  Global Instance observe_types (τ : types) : Observe τ (list val) :=
    { observe τ := to_vals τ }.

  Global Instance notval_listloc : NotVal (list loc) := {}.
  Local Instance notval_listval : NotVal (list val) := {}.

  Lemma imp_ERecord {τ : types} {ζ} (Φs : τ -#> iProp Σ) t es :
    ⌜length τ ≤ max_array_length⌝ -∗
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ
      (λ r, ∃ (xs : τ), ownRecord r (DfracOwn 1) t xs ∗ Φs xs).
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
    iFrame.
  Qed.

  Instance types_lookup : Lookup Z Type types :=
    λ i xs, if decide (i < 0) then None else
      let fix go (i : nat) (τ : types) {struct τ} : option Type :=
        match τ, i with
        | Tbase X, 0%nat => Some X
        | Tbase _, _ => None
        | type_nel.Tcons X _, 0%nat => Some X
        | type_nel.Tcons _ τ, (S i0) => go i0 τ
        end
        in
      go (Z.to_nat i) xs.

  Instance types_lookup_total : LookupTotal Z Type types :=
    λ i xs, if decide (i < 0) then ()%type else
      let fix go (i : nat) (τ : types) {struct τ} : Type :=
        match τ, i with
        | Tbase X, 0%nat => X
        | Tbase _, _ => unit
        | type_nel.Tcons X _, 0%nat => X
        | type_nel.Tcons _ τ, (S i0) => go i0 τ
        end
      in
      go (Z.to_nat i) xs.

  Definition types_go : nat -> types -> Type :=
    fix go (i : nat) (τ : types) {struct τ} : Type :=
      match τ, i with
      | Tbase X, 0%nat => X
      | Tbase _, _ => unit
      | type_nel.Tcons X _, 0%nat => X
      | type_nel.Tcons _ τ', S i0 => go i0 τ'
      end.

  Fixpoint tau_lookup_go (τ : types) (i : nat) : τ -> types_go i τ :=
    match τ, i return τ -> types_go i τ with
    | Tbase X, 0%nat => fun xs => xs
    | Tbase _, _ => fun _ => tt
    | type_nel.Tcons X _, 0%nat => fun xs => fst xs
    | type_nel.Tcons _ τ', S i0 => fun xs => tau_lookup_go τ' i0 (snd xs)
    end.

  Definition τ_lookup_total {τ : types} (f : Z) (xs : τ) : τ !!! f.
  Proof.
    unfold lookup_total, types_lookup_total.
    case_decide.
    - exact tt.
    - exact (tau_lookup_go τ (Z.to_nat f) xs).
  Defined.

  Notation "xs !!τ f" := (τ_lookup_total f xs) (at level 20).

  Global Instance encode_types_lookup {τ : types} {f : Z} : Encode (τ !!! f).
  Proof.
    unfold lookup_total, types_lookup_total.
    case_decide. { apply _. }
    generalize (Z.to_nat f).
    induction τ; intros n.
    - destruct n; apply _.
    - destruct n.
      + apply _.
      + apply IHτ.
  Defined.

  Global Instance inhabited_val : Inhabited val :=
    { inhabitant := VUnit }.

  Local Instance Encode_types_aux {τ} n : Encode (types_go n τ).
  Proof.
    revert n.
    induction τ; intros n.
    - simpl. destruct n; apply _.
    - simpl. destruct n; first apply _.
      apply IHτ.
  Defined.

  Local Lemma lookup_total_to_vals_aux {τ : types} (xs : τ) n :
    (to_vals xs) !!! n = #(tau_lookup_go τ n xs).
  Proof.
    revert xs n.
    induction τ as [X H | X H b IH]; intros xs n.
    - rewrite tapp_bind.
      destruct n as [|n'] eqn:Hnat; first reflexivity.
      rewrite (list.lookup_total_cons_ne_0 _ _ _ _); last lia.
      rewrite list.lookup_total_nil. reflexivity.
    - pose proof (Tcons_inv b xs) as [x [xs' ->]].
      simpl; rewrite tapp_bind.
      destruct n as [|n'] eqn:Hnat; first reflexivity.
      rewrite (list.lookup_total_cons_ne_0 _ _ _ _); last lia.
      apply IH.
  Qed.

  Lemma lookup_total_to_vals {τ : types} (xs : τ) (f : Z) :
    (to_vals xs) !!! f = #(xs !!τ f).
  Proof.
    unfold "!!τ", τ_lookup_total, encode_types_lookup, lookup_total, types_lookup_total, listz_lookup_total.
    case_decide as Hlt. { reflexivity. }
    generalize (Z.to_nat f) as n; intros n; clear dependent f.
    apply lookup_total_to_vals_aux.
  Qed.

  Global Instance notval_block : NotVal (mut_tag * list loc) := {}.

  Global Instance inhabited_loc : Inhabited loc.
  Proof.
    do 2 constructor. apply Z.inhabited.(inhabitant).
  Qed.

  Lemma imp_ERecordAccess {τ : types} {ζ} f {Φ : (τ !!! f) → iProp Σ} r ls e :
    ⌜valid f ls⌝ -∗
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    (∃ dq t (xs : τ),
      ▷ ownRecord r dq t xs ∗
      ▷ (ownRecord r dq t xs -∗ Φ (xs !!τ f))) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros "%Hvalid #Hblock He P". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iDestruct "P" as
        "(%dq & %t & %xs & P)".
    rewrite <- (bi.later_sep (ownRecord _ _ _ _)).
    iCombine "Hblock P" as "P".


    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[P]").
    { iApply (imp_load_block_ghost' with "Hblock P"). }
    iIntros ((? & ?)) "(-> & #Hblock' & Hown & HΦ) /=".
    iClear "Hblock".

    iDestruct "Hown" as "(%ls' & #Hblock & Htag & Hxs)".
    iPoseProof (isBlockLocs_valid with "Hblock' Hblock") as "->".
    iPoseProof (isBlockLocs_length with "Hblock") as "%Hlen".
    iPoseProof (big_sepLZ2_length with "Hxs") as "%Hlen_xs".
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

End records_reasoning.
