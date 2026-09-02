From iris.algebra Require Import auth gset.
From stdpp Require Import relations.

From osiris Require Import osiris.

Require Import UnionFind08DataConc.

Section same_class.

Local Abbreviation elem := record.
Context `{!osirisGS Σ, !inG Σ (authR (gsetUR (elem * elem)))}.

Implicit Types γ : uf_names.

(* ------------------------------------------------------------------------ *)
(* Equivalence, as monotone ghost knowledge. *)

(* [same_class γ u w]: [u] and [w] belong to the same equivalence class of
   the structure. *)

(* [same_class] is a chain of recorded pairs, a single pair would make
   transitivity a ghost update, and an update would need full ownership. *)

Fixpoint same_class_chain (γ : uf_names) (n : nat) (u w : elem) : iProp Σ :=
  match n with
  | O => ⌜u = w⌝
  | S n =>
      ∃ c, (own γ.(uf_class) (◯ {[ (u, c) ]}) ∨
            own γ.(uf_class) (◯ {[ (c, u) ]})) ∗
           same_class_chain γ n c w
  end.

Definition same_class (γ : uf_names) (u w : elem) : iProp Σ :=
  ∃ n, same_class_chain γ n u w.

(* Persistent: [◯] of a [gset] is [CoreId], and the rest is structure. *)
Global Instance same_class_chain_persistent γ n u w :
  Persistent (same_class_chain γ n u w).
Proof. revert u; induction n; apply _. Qed.

Global Instance same_class_persistent γ u w : Persistent (same_class γ u w).
Proof. apply _. Qed.

Global Instance same_class_chain_timeless γ n u w :
  Timeless (same_class_chain γ n u w).
Proof. revert u; induction n; apply _. Qed.

Global Instance same_class_timeless γ u w : Timeless (same_class γ u w).
Proof. apply _. Qed.

Lemma same_class_refl γ u : ⊢ same_class γ u u.
Proof. by iExists O. Qed.

Lemma same_class_chain_trans γ n m u w t :
  same_class_chain γ n u w -∗ same_class_chain γ m w t -∗
  same_class_chain γ (n + m) u t.
Proof.
  iInduction n as [|n] "IH" forall (u); simpl.
  - iIntros "-> $".
  - iIntros "(%c & Hc & Hrest) Hwt".
    iExists c. iFrame "Hc". iApply ("IH" with "Hrest Hwt").
Qed.

Lemma same_class_trans γ u w t :
  same_class γ u w -∗ same_class γ w t -∗ same_class γ u t.
Proof.
  iIntros "(%n & Hn) (%m & Hm)". iExists (n + m).
  iApply (same_class_chain_trans with "Hn Hm").
Qed.

(* Symmetry: reverse the chain. Each link is stored in both directions,
   which is exactly what makes this go through. *)

Lemma same_class_chain_sym γ n u w :
  same_class_chain γ n u w -∗ same_class γ w u.
Proof.
  iInduction n as [|n] "IH" forall (u); simpl.
  - iIntros "->". iApply same_class_refl.
  - iIntros "(%c & Hc & Hrest)".
    iDestruct ("IH" with "Hrest") as "Hwc".
    iApply (same_class_trans with "Hwc").
    iExists 1%nat. iExists u. simpl. iSplitL; last done.
    iDestruct "Hc" as "[Hc|Hc]"; [by iRight | by iLeft].
Qed.

Lemma same_class_sym γ u w : same_class γ u w -∗ same_class γ w u.
Proof. iIntros "(%n & Hn)". iApply (same_class_chain_sym with "Hn"). Qed.

(* The invariant's coupling between the recorded pairs and the abstract
   state: every pair ever recorded is, in the CURRENT state, a pair of
   equivalent vertices. *)

Definition same_class_sound (S : gset (elem * elem)) (R : elem → elem) : Prop :=
  ∀ u w, (u, w) ∈ S → R u = R w.

(* Reading a chain back. The authority is taken at an arbitrary fraction:
   half of it lives in the client's [UF], which is what lets this be used
   inside an atomic update's access, where no invariant can be opened. *)

Lemma same_class_eq γ dq S R u w :
  same_class_sound S R →
  own γ.(uf_class) (●{dq} S) -∗ same_class γ u w -∗ ⌜R u = R w⌝.
Proof.
  iIntros (HS) "HS (%n & Hn)".
  iInduction n as [|n] "IH" forall (u); simpl.
  { by iDestruct "Hn" as %->. }
  iDestruct "Hn" as (c) "[Hc Hrest]".
  iAssert ⌜R u = R c⌝%I as %Huc.
  { iDestruct "Hc" as "[Hc|Hc]";
      iCombine "HS Hc" gives %[_ [Hincl _]]%auth_both_dfrac_valid_discrete;
      iPureIntro; apply gset_included in Hincl.
    - apply HS. set_solver.
    - symmetry. apply HS. set_solver. }
  rewrite Huc. iApply ("IH" with "HS Hrest").
Qed.

(* Recording a new pair. This is the ONLY operation that mints anything,
   and it needs the full authority — so it can only happen where the two
   halves meet, namely at the linking CAS. *)

Lemma same_class_update γ S R u w :
  same_class_sound S R →
  R u = R w →
  own γ.(uf_class) (● S) ==∗
  ∃ S', own γ.(uf_class) (● S') ∗ same_class γ u w ∗ ⌜same_class_sound S' R⌝ ∗ ⌜S ⊆ S'⌝.
Proof.
  intros HSsound Huw.
  iIntros "HS".
  iMod (own_update _ _ (● (S ∪ {[ (u, w) ]}) ⋅ ◯ (S ∪ {[ (u, w) ]}))
         with "HS") as "[Hauth Hfrag]".
  { apply auth_update_alloc, gset_local_update. set_solver. }
  iModIntro. iExists (S ∪ {[ (u, w) ]}). iFrame "Hauth".
  iSplitL "Hfrag".
  { iExists 1%nat. iExists w. simpl. iSplitL; last done.
    iLeft. iApply (own_mono with "Hfrag").
    apply auth_frag_mono, gset_included. set_solver. }
  iPureIntro. split; last set_solver.
  intros a b Hab.
  apply elem_of_union in Hab as [Hab | Hab]; first by apply HSsound.
  apply elem_of_singleton in Hab. by simplify_eq.
Qed.

(* Soundness survives any COARSENING of the state — which is the only kind
   of change the structure ever makes to it. This is the obligation the
   linking CAS discharges, and it is the reason recorded pairs may be kept
   forever. *)

Lemma same_class_sound_coarsen S R R' :
  same_class_sound S R →
  (∀ u w, R u = R w → R' u = R' w) →
  same_class_sound S R'.
Proof. intros HS Hmono u w Huw. by apply Hmono, HS. Qed.

End same_class.
