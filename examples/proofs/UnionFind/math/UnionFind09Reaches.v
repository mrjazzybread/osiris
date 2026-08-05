From iris.algebra Require Import auth gset.
From stdpp Require Import relations.

From osiris Require Import osiris.

Require Import UnionFind03Link.

Section reach.

Local Notation elem := record.
Context `{!osirisGS Σ, !inG Σ (authR (gsetUR (elem * elem)))}.

(* ------------------------------------------------------------------------ *)
(* Reachability in the abstract graph. *)

(* [reaches γR u w]: [w] is reachable from [u] in the abstract equivalence
   graph [F] of [uf_inv]. *)

Definition reaches (γR : gname) (u w : elem) : iProp Σ :=
  own γR (◯ {[ (u, w) ]}).

(* The fragment is persistent ([◯] of a [gset] is [CoreId]). *)
Global Instance reaches_persistent γR u w : Persistent (reaches γR u w).
Proof. apply _. Qed.

(* The invariant's coupling between the recorded pairs and the graph [F]. *)

Definition reaches_sound (R : gset (elem * elem)) (F : elem → elem → Prop) : Prop :=
  ∀ u w, (u, w) ∈ R → rtc F u w.

(* Reading a recorded pair back. *)

Lemma reaches_lookup γR R u w :
  own γR (● R) -∗ reaches γR u w -∗ ⌜(u, w) ∈ R⌝.
Proof.
  iIntros "HR Hf".
  iCombine "HR Hf" gives %[Hincl _]%auth_both_valid_discrete.
  iPureIntro. apply gset_included in Hincl. set_solver.
Qed.

(* Recording a new pair [(u, w)]. *)

Lemma reaches_update γR R F u w :
  reaches_sound R F →
  rtc F u w →
  own γR (● R) ==∗
  ∃ R', own γR (● R') ∗ reaches γR u w ∗ ⌜reaches_sound R' F⌝ ∗ ⌜R ⊆ R'⌝.
Proof.
  intros HRsound Huw.
  iIntros "HR".
  iMod (own_update _ _ (● (R ∪ {[ (u, w) ]}) ⋅ ◯ (R ∪ {[ (u, w) ]}))
         with "HR") as "[Hauth Hfrag]".
  { apply auth_update_alloc, gset_local_update. set_solver. }
  iModIntro. iExists (R ∪ {[ (u, w) ]}). iFrame "Hauth".
  iSplitL "Hfrag".
  { iApply (own_mono with "Hfrag").
    apply auth_frag_mono, gset_included. set_solver. }
  iPureIntro. split; last set_solver.
  intros a b Hab.
  apply elem_of_union in Hab as [Hab | Hab]; first by apply HRsound.
  apply elem_of_singleton in Hab. by simplify_eq.
Qed.

(* [reaches_sound] is preserved by [link] (UnionFind03Link). *)

Lemma reaches_sound_link R F a y' :
  reaches_sound R F → reaches_sound R (link F a y').
Proof.
  intros HR u w Huw.
  eapply rtc_subrel; [|by apply HR]. intros ? ? ?. by left.
Qed.

End reach.
