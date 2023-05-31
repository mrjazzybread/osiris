From stdpp Require Import countable numbers gmap.

Local Open Scope Z_scope.

(* A location is an integer. *)

(* We do not want Coq to think that [loc] and [Z] are the same type. Indeed,
   the function [encode] does not work in the same way at memory locations
   and at ordinary integers. For this reason, we use a record type. *)

Record loc :=
  Loc { address : Z }.

(* These instances allow using locations as keys in sets and maps. *)

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable loc.
Proof. apply (inj_countable' address Loc). intros [?]. eauto. Defined.

(* If needed, one could declare instances of the type classes [EqDecision],
   [Inhabited], [Countable], [Infinite] for the type [loc]. *)

(* [max_loc ls] computes an upper bound of the finite set of locations [ls].
   It is in the fact the least upper bound of the set [ls], except when [ls]
   is empty. *)

Definition max_loc (ls : gset loc) : Z :=
  set_fold (λ l accu, Z.max (address l) accu) 0 ls.

Lemma le_max_loc :
  ∀ ls l, l ∈ ls → address l ≤ max_loc ls.
Proof.
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → address l ≤ r)).
  { set_solver. }
  { intros x X r _ IH l.
    rewrite elem_of_union, Z.max_le_iff.
    set_solver by eauto with lia. }
Qed.

(* [fresh_loc ls] is a location that is guaranteed not to be a member of the
   finite set of locations [ls]. *)

Definition fresh_loc (ls : gset loc) : loc :=
  {| address := max_loc ls + 1 |}.

Lemma fresh_loc_fresh ls :
  fresh_loc ls ∉ ls.
Proof.
  unfold fresh_loc.
  intro H.
  specialize (le_max_loc _ _ H); clear H; simpl; intro H.
  lia.
Qed.
