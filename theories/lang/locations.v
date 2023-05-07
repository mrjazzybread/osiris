From stdpp Require Import countable numbers gmap.

Local Open Scope Z_scope.

(* A location is an integer. *)

Definition loc := Z.

(* If needed, one could declare instances of the type classes [EqDecision],
   [Inhabited], [Countable], [Infinite] for the type [loc]. *)

(* [max_loc ls] computes an upper bound of the finite set of locations [ls].
   It is in the fact the least upper bound of the set [ls], except when [ls]
   is empty. *)

Definition max_loc (ls : gset loc) : loc :=
  set_fold Z.max 0 ls.

Lemma le_max_loc :
  ∀ ls l, l ∈ ls → l ≤ max_loc ls.
Proof.
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → l ≤ r)).
  { set_solver. }
  { intros x X r _ IH l.
    rewrite elem_of_union, Z.max_le_iff.
    set_solver by eauto with lia. }
Qed.

(* [fresh_loc ls] is a location that is guaranteed not to be a member of the
   finite set of locations [ls]. *)

Definition fresh_loc (ls : gset loc) : loc :=
  max_loc ls + 1.

Lemma fresh_loc_fresh ls :
  fresh_loc ls ∉ ls.
Proof.
  unfold fresh_loc.
  intro H.
  specialize (le_max_loc _ _ H); clear H; intro H.
  lia.
Qed.

(* The type of locations can now be made opaque. *)

Global Opaque loc.
