(******************************************************************************)
(*                                                                            *)
(*             Herlihy-Wing queue: the ghost state algebra                    *)
(*                                                                            *)
(******************************************************************************)

(* This file sets up the resource algebras used by the FIFO proof of the
   Herlihy-Wing queue, together with the small lemmas that let one allocate,
   read and update the ghost state they carry.

   It is a port of the corresponding section of the Iris-examples development
   [logatom/herlihy_wing_queue/hwq.v], adapted to Osiris. Two things change:

   - array indices are [Z], not [nat], because Osiris models OCaml arrays with
     [Z]-indexed lists ([list_z]);

   - the elements of the queue are Osiris values [val], not locations. In the
     original the queue stores pointers to boxed elements; here [enqueue] takes
     an arbitrary [val].

   Nothing in this file mentions the program, the program logic or the
   invariant: it is pure Iris ghost-state plumbing. *)

From iris.algebra Require Import auth excl agree csum gmap numbers.
From iris.base_logic.lib Require Import own invariants saved_prop.
From iris.proofmode Require Import proofmode.

From osiris Require Import osiris.

(* ------------------------------------------------------------------------ *)

(* The resource algebras. *)

Definition prod4R A B C D E :=
  prodR (prodR (prodR (prodR A B) C) D) E.

(* A one-shot: [not_shot] can be updated to [shot], and [shot] is persistent,
   so it is a witness that the transition has taken place. *)

Definition oneshotUR := optionUR $ csumR (exclR unitR) (agreeR unitR).
Definition shot     : oneshotUR := Some $ Cinr $ to_agree ().
Definition not_shot : oneshotUR := Some $ Cinl $ Excl ().

(* The ghost state attached to one slot of the array. *)

Definition per_slot :=
  prod4R
    (* Unique token for the index. *)
    (optionUR $ exclR unitR)
    (* The value stored at this index, which never changes. *)
    (optionUR $ agreeR code.valO)
    (* A unique name for the index, present only while help is in play. *)
    (optionUR $ exclR gnameO)
    (* One shot witnessing the transition from pending to committed. *)
    oneshotUR
    (* One shot witnessing the physical writing of the value in the slot. *)
    oneshotUR.

Definition eltsUR := authR $ optionUR $ exclR $ listO code.valO.
Definition contUR := csumR (exclR unitR) (agreeR (prodO ZO ZO)).
Definition slotUR := authR $ gmapUR Z per_slot.
Definition backUR := authR max_natUR.

Class hwqG Σ :=
  HwqG {
    hwq_eltsG :: inG Σ eltsUR; (** Logical contents of the queue. *)
    hwq_contG :: inG Σ contUR; (** One-shot for contradiction states. *)
    hwq_slotG :: inG Σ slotUR; (** State data for used array slots. *)
    hwq_backG :: inG Σ backUR; (** Used to show that [back] only increases. *)
  }.

Definition hwqΣ : gFunctors :=
  #[GFunctor eltsUR; GFunctor contUR; GFunctor slotUR; GFunctor backUR].

Global Instance subG_hwqΣ {Σ} : subG hwqΣ Σ → hwqG Σ.
Proof. solve_inG. Qed.

(* ------------------------------------------------------------------------ *)

Section ghost.

Context `{!hwqG Σ}.

(* ---------------------------------------------------------------------- *)

(* The logical contents of the queue: a list of values, split between the
   invariant (the authoritative half) and whoever is performing an atomic
   update (the fragment). *)

Lemma new_elts (l : list val) : ⊢ |==> ∃ γe, own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iMod (own_alloc (● Excl' l ⋅ ◯ Excl' l)) as (γe) "[H● H◯]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γe. iFrame.
Qed.

Lemma sync_elts γe (l1 l2 : list val) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H".
  iDestruct (own_valid with "H") as "H".
  by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_elts γe (l1 l2 l : list val) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) ==∗
    own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op.
  iApply (own_update with "H").
  by apply auth_update, option_local_update, exclusive_local_update.
Qed.

(* The fragment, handed out to clients. *)

Definition hwq_cont γe (elts : list val) : iProp Σ :=
  own γe (◯ Excl' elts).

Lemma hwq_cont_exclusive γe elts1 elts2 :
  hwq_cont γe elts1 -∗ hwq_cont γe elts2 -∗ False.
Proof.
  iIntros "H1 H2".
  by iCombine "H1 H2" gives %?%auth_frag_op_valid_1.
Qed.

(* ---------------------------------------------------------------------- *)

(* A monotone counter, used to record that [back] only ever increases. *)

Definition back_value γb n := own γb (● MaxNat n).
Definition back_lower_bound γb n := own γb (◯ MaxNat n).

Lemma new_back : ⊢ |==> ∃ γb, back_value γb 0.
Proof.
  iMod (own_alloc (● MaxNat 0)) as (γb) "H●".
  - by rewrite auth_auth_valid.
  - by iExists γb.
Qed.

Lemma back_incr γb n :
  back_value γb n ==∗ back_value γb (S n).
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat (S n))). simpl. lia.
Qed.

Lemma back_snapshot γb n :
  back_value γb n ==∗ back_value γb n ∗ back_lower_bound γb n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

Lemma back_le γb n1 n2 :
  back_value γb n1 -∗ back_lower_bound γb n2 -∗ ⌜n2 ≤ n1⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. iPureIntro.
  apply auth_both_valid_discrete in Hvalid as [H1%max_nat_included _]. done.
Qed.

(* The same algebra is reused to keep a lower bound on the second component
   of any contradiction that has arisen, or may still arise. *)

Definition i2_lower_bound γi n := back_value γi n.

Definition no_contra_wit γi n := back_lower_bound γi n.

Lemma i2_lower_bound_update γi n m :
  n ≤ m →
  i2_lower_bound γi n ==∗ i2_lower_bound γi m.
Proof.
  iIntros (H) "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat m)). simpl. lia.
Qed.

Lemma i2_lower_bound_snapshot γi n :
  i2_lower_bound γi n ==∗ i2_lower_bound γi n ∗ no_contra_wit γi n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

(* ---------------------------------------------------------------------- *)

(* A one-shot recording whether the invariant has entered a contradiction
   state, and if so which pair of indices caused it. *)

Definition no_contra γc : iProp Σ :=
  own γc (Cinl (Excl ())).

Definition contra γc (i1 i2 : Z) : iProp Σ :=
  own γc (Cinr (to_agree (i1, i2))).

Lemma new_no_contra : ⊢ |==> ∃ γc, no_contra γc.
Proof. by apply own_alloc. Qed.

Lemma to_contra i1 i2 γc : no_contra γc ==∗ contra γc i1 i2.
Proof. apply bi.entails_wand, own_update. by apply cmra_update_exclusive. Qed.

Lemma contra_not_no_contra i1 i2 γc :
  no_contra γc -∗ contra γc i1 i2 -∗ False.
Proof. iIntros "HnoC HC". iCombine "HnoC HC" gives %[]. Qed.

Lemma contra_agree i1 i2 i1' i2' γc :
  contra γc i1 i2 -∗ contra γc i1' i2' -∗ ⌜i1' = i1 ∧ i2' = i2⌝.
Proof.
  iIntros "HC HC'". iCombine "HC HC'" gives %H.
  iPureIntro. apply to_agree_op_inv_L in H. by inversion H.
Qed.

Global Instance contra_persistent γc i1 i2 : Persistent (contra γc i1 i2).
Proof. apply own_core_persistent. by rewrite /CoreId. Qed.

End ghost.

(* ------------------------------------------------------------------------ *)

(* The state of one slot, from the point of view of the enqueue that claimed
   it. *)

Inductive state :=
  (** Help was requested: the element is not committed yet. *)
  | Pend : gname → state
  (** Help has been provided: the element is committed. *)
  | Help : gname → state
  (** The enqueue knows it has been committed. *)
  | Done :         state.

Global Instance state_inhabited : Inhabited state.
Proof. constructor. refine Done. Qed.

(* The data attached to a slot:
     - the value being written into the slot,
     - the state of the slot, which carries the name of a saved proposition
       holding the postcondition of the pending enqueue's atomic update,
     - [true] once a value has been physically written into the slot. *)

Definition slot_data : Type := val * state * bool.

Definition update_slot (i : Z) f (slots : gmap Z slot_data) :=
  match slots !! i with
  | Some d => <[i := f d]> (delete i slots)
  | None   => slots
  end.

Definition val_of (data : slot_data) : val :=
  match data with (v, _, _) => v end.

Definition state_of (data : slot_data) : state :=
  match data with (_, s, _) => s end.

Definition name_of (data : slot_data) : option gname :=
  match state_of data with Pend γ => Some γ | Help γ => Some γ | _ => None end.

Definition was_written (data : slot_data) : bool :=
  match data with (_, _, b) => b end.

Definition was_committed (data : slot_data) : bool :=
  match state_of data with Pend _ => false | _ => true end.

Definition set_written (data : slot_data) : slot_data :=
  match data with (v, s, _) => (v, s, true) end.

Definition set_written_and_done (data : slot_data) : slot_data :=
  match data with (v, _, _) => (v, Done, true) end.

Definition to_helped (γ : gname) (data : slot_data) : slot_data :=
  match data with (v, _, w) => (v, Help γ, w) end.

Definition to_done (data : slot_data) : slot_data :=
  match data with (v, _, w) => (v, Done, w) end.

(* What a dequeuer physically reads out of the slot. *)

Definition physical_value (data : slot_data) : option val :=
  match data with (v, _, w) => if w then Some v else None end.

Lemma val_of_set_written d : val_of (set_written d) = val_of d.
Proof. by destruct d as [[v s] w]. Qed.

Lemma was_written_set_written d : was_written (set_written d) = true.
Proof. by destruct d as [[v s] w]. Qed.

Lemma state_of_set_written d : state_of (set_written d) = state_of d.
Proof. by destruct d as [[v s] w]. Qed.

Lemma update_slot_lookup (i : Z) f (slots : gmap Z slot_data) :
  update_slot i f slots !! i = f <$> slots !! i.
Proof.
  rewrite /update_slot. destruct (slots !! i) as [d|] eqn:Hi; last done.
  by rewrite lookup_insert_eq.
Qed.

Lemma update_slot_lookup_ne (i k : Z) f (slots : gmap Z slot_data) :
  i ≠ k → update_slot i f slots !! k = slots !! k.
Proof.
  intros Hne. rewrite /update_slot. destruct (slots !! i) eqn:Hi; last done.
  rewrite lookup_insert_ne // lookup_delete_ne //.
Qed.

Lemma update_slot_update_slot (i : Z) f g (slots : gmap Z slot_data) :
  update_slot i f (update_slot i g slots) = update_slot i (f ∘ g) slots.
Proof.
  rewrite /update_slot. destruct (slots !! i) as [d|] eqn:Hi; last by rewrite Hi.
  by rewrite lookup_insert_eq delete_insert_eq delete_delete_eq.
Qed.

Lemma update_slot_dom (i : Z) f (slots : gmap Z slot_data) :
  dom (update_slot i f slots) = dom slots.
Proof.
  rewrite /update_slot. destruct (slots !! i) as [d|] eqn:Hi; last done.
  rewrite dom_insert_L dom_delete_L.
  assert (i ∈ dom slots) as Hin by (apply elem_of_dom; by eexists).
  by rewrite -union_difference_singleton_L.
Qed.

(* The two sequences of slot updates that an [enqueue] performs at its write,
   composed. *)
Lemma update_slot_written_done (i : Z) (slots : gmap Z slot_data) :
  update_slot i to_done (update_slot i set_written slots)
  = update_slot i set_written_and_done slots.
Proof.
  rewrite update_slot_update_slot /update_slot.
  by destruct (slots !! i) as [[[v st] w]|].
Qed.

Lemma update_slot_written_helped_done (i : Z) g (slots : gmap Z slot_data) :
  update_slot i to_done
    (update_slot i (to_helped g) (update_slot i set_written slots))
  = update_slot i set_written_and_done slots.
Proof.
  rewrite !update_slot_update_slot /update_slot.
  by destruct (slots !! i) as [[[v st] w]|].
Qed.

(* The image of the slot data in the resource algebra. *)

Definition of_slot_data (data : slot_data) : per_slot :=
  match data with
  | (v, s, w) =>
    let name := match s with Pend γ => Excl' γ | Help γ => Excl' γ | Done => None end in
    let comm := if was_committed data then shot else not_shot in
    let wr := if w then shot else not_shot in
    (Excl' (), Some (to_agree v), name, comm, wr)
  end.

Lemma of_slot_data_valid d : ✓ of_slot_data d.
Proof. by destruct d as [[v []] []]. Qed.

(* ------------------------------------------------------------------------ *)

Section slots.

Context `{!hwqG Σ}.

Implicit Types slots : gmap Z slot_data.

(* The (unique) token for slot [i]. *)
Definition slot_token γs (i : Z) : iProp Σ :=
  own γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).

(* A witness that the value enqueued in slot [i] is [v]. *)
Definition slot_val_wit γs (i : Z) (v : val) : iProp Σ :=
  own γs (◯ {[i := (None, Some (to_agree v), None, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been committed. *)
Definition slot_committed_wit γs (i : Z) : iProp Σ :=
  own γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).

Definition slot_name_tok γs (i : Z) γ : iProp Σ :=
  own γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been written. *)
Definition slot_written_wit γs (i : Z) : iProp Σ :=
  own γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).

(* A token proving that the enqueue in slot [i] has not been committed. *)
Definition slot_pending_tok γs (i : Z) : iProp Σ :=
  own γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).

(* A token proving that no value has been written in slot [i]. *)
Definition slot_writing_tok γs (i : Z) : iProp Σ :=
  own γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).

Global Instance slot_val_wit_persistent γs i v :
  Persistent (slot_val_wit γs i v).
Proof. apply _. Qed.

Global Instance slot_committed_wit_persistent γs i :
  Persistent (slot_committed_wit γs i).
Proof. apply _. Qed.

Global Instance slot_written_wit_persistent γs i :
  Persistent (slot_written_wit γs i).
Proof. apply _. Qed.

Lemma new_slots : ⊢ |==> ∃ γs, own γs (● ∅ : slotUR).
Proof.
  iMod (own_alloc (● ∅ ⋅ ◯ ∅ : slotUR)) as (γs) "[H● _]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γs. iFrame.
Qed.

(* Allocate a new slot with data [d] at the fresh index [i]. *)
Lemma alloc_slot γs slots (i : Z) (d : slot_data) :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := d]> slots)) : slotUR) ∗
    own γs (◯ {[i := of_slot_data d]} : slotUR).
Proof.
  iIntros (Hi) "H". rewrite -own_op fmap_insert.
  iApply (own_update with "H"). apply auth_update_alloc.
  apply alloc_singleton_local_update.
  - by rewrite lookup_fmap Hi.
  - apply of_slot_data_valid.
Qed.

Lemma alloc_done_slot γs slots (i : Z) v :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := (v, Done, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i v ∗
    slot_committed_wit γs i ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma alloc_pend_slot γs slots (i : Z) v γ :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> (<[i := (v, Pend γ, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i v ∗
    slot_pending_tok γs i ∗
    slot_name_tok γs i γ ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma use_val_wit γs slots (i : Z) v :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i v -∗
  ⌜val_of <$> slots !! i = Some v⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dv ds] dw].
  destruct H1 as [[[[_ H1] _] _] _]; simpl in H1. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ H2] _] _] _]; simpl in H2.
    assert (Some (to_agree v) ≡ Some (to_agree dv)) as H by by transitivity b2.
    apply Some_equiv_inj, to_agree_inj in H. done.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    assert (Some (to_agree v) ≼ Some (to_agree dv)) as H by set_solver.
    apply option_included in H.
    destruct H as [H|[a [b (H11 & H12 & H13)]]]; first done.
    simplify_eq. destruct H13 as [H|H].
    + by apply to_agree_inj in H.
    + by apply to_agree_included in H.
Qed.

Lemma use_name_tok γs slots (i : Z) γ :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ -∗
  ⌜name_of <$> slots !! i = Some (Some γ)⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dv ds] dw].
  destruct H1 as [[[[_ _] H1] _] _]; simpl in H1. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] H2] _] _]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≡ Excl' γ') as H by by transitivity b3.
      inversion H as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ Excl' γ') as H by by transitivity b3.
      inversion H as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ None) as H by by transitivity b3.
      inversion H.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≼ Excl' γ') as H by set_solver.
      by apply Excl_included in H.
    + assert (Excl' γ ≼ Excl' γ') as H by set_solver.
      by apply Excl_included in H.
    + assert (Excl' γ ≼ None) as H by set_solver.
      exfalso. apply option_included in H as [H|H]; first done.
      destruct H as [a [b (H11 & H12 & H13)]]. by simplify_eq.
Qed.

Lemma shot_not_equiv_not_shot : shot ≢ not_shot.
Proof.
  intros H. rewrite /shot /not_shot in H.
  inversion H as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_equiv_not_shot' e : shot ≢ not_shot ⋅ e.
Proof.
  intros H. rewrite /shot /not_shot in H.
  destruct e as [e|]; first destruct e.
  - rewrite -Some_op -Cinl_op in H.
    inversion H as [x y Habsurd|]; inversion Habsurd.
  - rewrite -Some_op in H. compute in H.
    inversion H as [x y HAbsurd|]. inversion HAbsurd.
  - inversion H as [x y HAbsurd|]. inversion HAbsurd.
  - inversion H as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_included_not_shot : ¬ shot ≼ not_shot.
Proof.
  intros H. rewrite /shot /not_shot in H.
  apply option_included in H. destruct H as [H|H]; first done.
  destruct H as [a [b (H1 & H2 & [H3|H3])]].
  - simplify_eq. by inversion H3.
  - simplify_eq. apply csum_included in H3.
    destruct H3 as [H3|H3]; first done. destruct H3 as [H3|H3].
    + destruct H3 as [a [b (H1 & H2 & H3)]]. by inversion H1.
    + destruct H3 as [a [b (H1 & H2 & H3)]]. by inversion H1.
Qed.

Lemma use_committed_wit γs slots (i : Z) :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_committed_wit γs i -∗
  ⌜was_committed <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dv ds] dw].
  destruct H1 as [[[[_ _] _] H1]]; simpl in H1. f_equal.
  destruct (was_committed (dv, ds, dw)); first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] H2] _]; simpl in H2.
    apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_written_wit γs slots (i : Z) :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_written_wit γs i -∗
  ⌜was_written <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %H.
  iPureIntro. apply auth_both_valid_discrete in H as [H%singleton_included_l _].
  destruct H as [ps (H1 & H2%option_included)]. rewrite lookup_fmap in H1.
  destruct (slots !! i) as [d|]; last by inversion H1. simpl in H1.
  inversion_clear H1.
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into H1 end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5]. destruct d as [[dv ds] dw].
  destruct H1 as [[[[_ _] _] _] H1]; simpl in H1. f_equal.
  destruct dw; first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] _] H2]; simpl in H2.
    exfalso. apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [_ H2]; simpl in H2.
    exfalso. apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_writing_tok γs (i : Z) slots :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i set_written slots) : slotUR) ∗
    slot_written_wit γs i.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H". rewrite -own_op.
  iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[v s] w]|] eqn:Hi; last by inversion H1_1.
  apply Some_equiv_inj in H1_1.
  assert (w = false) as ->.
  { destruct w; [ exfalso | done ].
    apply Some_included in H1_2 as [H1_2|H1_2].
    - assert ((None, None, None, None, not_shot)
            ≡ of_slot_data (v, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by apply shot_not_equiv_not_shot.
    - destruct H1_2 as [f H1_2].
      assert ((None, None, None, None, not_shot) ⋅ f
            ≡ of_slot_data (v, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by eapply shot_not_equiv_not_shot'. }
  rewrite /update_slot Hi insert_delete_eq fmap_insert.
  apply auth_update. eapply (singleton_local_update _ i).
  { by rewrite lookup_fmap Hi. }
  rewrite /set_written. apply prod_local_update; first done. simpl.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma writing_tok_not_written γs slots (i : Z) :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i -∗
    ⌜was_written <$> slots !! i = Some false⌝.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H".
  iDestruct (own_valid with "H") as %Hvalid%auth_both_valid_discrete.
  iPureIntro. destruct Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[v s] w]|]; last by inversion H1_1.
  apply Some_equiv_inj in H1_1. simpl. f_equal. destruct w; last done.
  exfalso. apply Some_included in H1_2 as [H1_2|H1_2].
  - assert ((None, None, None, None, not_shot)
          ≡ of_slot_data (v, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by apply shot_not_equiv_not_shot.
  - destruct H1_2 as [f H1_2].
    assert ((None, None, None, None, not_shot) ⋅ f
          ≡ of_slot_data (v, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by eapply shot_not_equiv_not_shot'.
Qed.

Lemma None_op {A : cmra} : (None : optionUR A) ⋅ None = None.
Proof. done. Qed.

Lemma use_pending_tok γs (i : Z) γ slots :
  state_of <$> slots !! i = Some (Pend γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_pending_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i (to_helped γ) slots) : slotUR) ∗
    slot_committed_wit γs i.
Proof.
  iIntros (Hlookup) "Hs● Htok". iCombine "Hs● Htok" as "H".
  rewrite -own_op. iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [H1 H2].
  apply singleton_included_l in H1 as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[v s] w]|] eqn:Hi; last by inversion H1_1.
  simpl in Hlookup. inversion Hlookup; subst s.
  rewrite /update_slot Hi insert_delete_eq fmap_insert.
  apply auth_update. repeat rewrite pair_op.
  eapply (singleton_local_update _ i). { by rewrite lookup_fmap Hi. }
  rewrite /to_helped. repeat rewrite None_op.
  repeat apply prod_local_update; try done.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma slot_token_exclusive γs (i : Z) :
  slot_token γs i -∗ slot_token γs i -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %H. iPureIntro.
  move:H =>/auth_frag_valid H. apply singleton_valid in H.
  by repeat apply pair_valid in H as [H _]; simpl in H.
Qed.

Lemma helped_to_done_aux γs (i : Z) γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR) ∗
    own γs (◯ {[i := (None, None, None, None, None)]} : slotUR).
Proof.
  iIntros (H) "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. rewrite -own_op.
  iApply (own_update with "H"). apply auth_update. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:Hd; last by inversion H.
  rewrite insert_delete_eq fmap_insert. eapply singleton_local_update.
  { by rewrite lookup_fmap Hd /=. }
  destruct d as [[dv ds] dw]. inversion H; subst ds; simpl.
  repeat apply prod_local_update; try done. simpl.
  apply delete_option_local_update. apply _.
Qed.

Lemma helped_to_done γs (i : Z) γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR).
Proof.
  iIntros (H) "H1 H2". by iMod (helped_to_done_aux with "H1 H2") as "[H _]".
Qed.

Lemma val_wit_from_auth γs (i : Z) v slots :
  val_of <$> slots !! i = Some v →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> slots) : slotUR) ∗
    slot_val_wit γs i v.
Proof.
  iIntros (H) "H". rewrite -own_op. iApply (own_update with "H").
  apply auth_update_dfrac_alloc; first apply _.
  assert (∃ d, slots !! i = Some d) as [d Hlookup].
  { destruct (slots !! i) as [d|]; inversion H. by exists d. }
  apply singleton_included_l. rewrite lookup_fmap. rewrite Hlookup /=.
  exists (of_slot_data d). split; first done.
  apply Some_included. right. destruct d as [[dv ds] dw]. simpl.
  repeat (apply prod_included; split; simpl);
    try by (apply option_included; left).
  apply option_included; right. exists (to_agree v), (to_agree dv).
  repeat (split; first done). left.
  rewrite Hlookup /= in H. by inversion H.
Qed.

End slots.
