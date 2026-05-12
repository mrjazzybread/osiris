From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang type_nel.
From osiris.tactics Require Import osiris_utils.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.
From osiris.logic Require Import list_z big_opLZ.

(** This file defines record resource predicates and [imp] rules for record expressions. *)

Section types_helpers.

  Fixpoint to_vals {τ : types} : τ-#> list val :=
    match τ with
    | Tbase H => tbind (λ x, [ #x])
    | @type_nel.Tcons X H b =>
      λ (x : X), @tbind _ b (λ tt, #x :: (to_vals tt))
    end.

  Global Instance observe_types (τ : types) : Observe τ (list val) :=
    { observe τ := to_vals τ }.

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
    (to_vals xs) !!! f = #(τ_lookup_total f xs).
  Proof.
    unfold τ_lookup_total, encode_types_lookup, lookup_total, types_lookup_total, listz_lookup_total.
    case_decide as Hlt. { reflexivity. }
    generalize (Z.to_nat f) as n; intros n; clear dependent f.
    apply lookup_total_to_vals_aux.
  Qed.

  Definition valid_field f τ := 0 ≤ f < length τ.

  Fixpoint tau_insert_go (τ : types) (i : nat) : types_go i τ → τ → τ :=
    match τ, i return types_go i τ → τ → τ with
    | Tbase X, 0%nat        => fun x _ => x
    | Tbase _, _            => fun _ xs => xs
    | type_nel.Tcons X _, 0%nat => fun x xs => (x, snd xs)
    | type_nel.Tcons _ τ', S i0 => fun x xs => (fst xs, tau_insert_go τ' i0 x (snd xs))
    end.

  Definition τ_insert {τ : types} (f : Z) (x : τ !!! f) (xs : τ) : τ.
  Proof.
    unfold lookup_total, types_lookup_total in x.
    revert x. case_decide.
    - intros _. exact xs.
    - intro x. exact (tau_insert_go τ (Z.to_nat f) x xs).
  Defined.

  Local Lemma insert_to_vals_aux {τ : types} (xs : τ) n (x : types_go n τ) :
    to_vals (tau_insert_go τ n x xs) = <[n := #x]> (to_vals xs).
  Proof.
    revert xs n x.
    induction τ as [X H | X H b IH]; intros xs n x.
    - rewrite tapp_bind.
      destruct n as [|n']; first reflexivity.
      simpl. update. reflexivity.
    - pose proof (Tcons_inv b xs) as [y [xs' ->]].
      simpl; rewrite tapp_bind.
      destruct n as [|n']; simpl; rewrite tapp_bind.
      + reflexivity.
      + rewrite IH. reflexivity.
  Qed.

  Lemma insert_to_vals {τ : types} (xs : τ) (f : Z) (x : τ !!! f) :
    to_vals (τ_insert f x xs) = <[ f := #x ]> (to_vals xs).
  Proof.
    revert x.
    unfold τ_insert, encode_types_lookup, lookup_total, types_lookup_total, insert, listz_insert.
    case_decide as Hlt. { auto. }
    generalize (Z.to_nat f) as n; intros n; clear dependent f.
    intros x.
    apply insert_to_vals_aux.
  Qed.

End types_helpers.

Notation "xs !!τ f" := (τ_lookup_total f xs) (at level 20).
Notation "<[ f τ= x ]> xs" := (τ_insert f x xs)
  (at level 5, right associativity, format "<[  f  τ=  x  ]>  xs").

Section record_resources.

  Context `{!osirisGS Σ}.

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

  Global Instance notval_block : NotVal (mut_tag * list loc) := {}.

  Global Instance inhabited_loc : Inhabited loc.
  Proof.
    do 2 constructor. apply Z.inhabited.(inhabitant).
  Qed.

  Lemma imp_ERecordAccess2 {τ : types} {ζ} f {Φ : (τ !!! f) → iProp Σ} r ls e :
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    (∃ dq t (xs : τ),
      ▷ (⌜valid_field f τ⌝ ∗ ownRecord r dq t xs) ∗
      ▷ (ownRecord r dq t xs -∗ Φ (xs !!τ f))) -∗
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

  Lemma imp_ERecordSet2 {τ : types} {ζ} f {Φ : unit → iProp Σ} (Φ1 : record → iProp Σ) (Φ2 : τ !!! f → iProp Σ) e1 e2 :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ r a, Φ1 r -∗ Φ2 a -∗
            ∃ t (xs : τ),
              ▷ (⌜valid_field f τ⌝ ∗ ownRecord r (DfracOwn 1) t xs) ∗
              ▷ (ownRecord r (DfracOwn 1) t <[f τ= a]> xs -∗ Φ ())) -∗
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

End records_reasoning.
