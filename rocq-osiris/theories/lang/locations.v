From stdpp Require Import countable numbers gmap.

Local Open Scope Z_scope.

(* A location is an integer. *)

(* We do not want Coq to think that [loc] and [Z] are the same type. Indeed,
   the function [encode] does not work in the same way at memory locations
   and at ordinary integers. For this reason, we use a record type. *)

Record loc :=
  Loc { address : Z }.

(* Equality. *)

Definition eqb (l1 l2 : loc) :=
  Z.eqb (address l1) (address l2).

(* These instances allow using locations as keys in sets and maps. *)

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable loc.
Proof. apply (inj_countable' address Loc). intros [?]. eauto. Defined.

(* This instance allows us to use [stdpp]'s fresh on [loc]. *)

Global Instance Infinite_loc : Infinite loc.
Proof.
  by apply infinite.inj_infinite with (f := Loc) (g := λ l, Some (address l)).
Defined.

(* This instance allows us to use total lookups with [loc] as the key type. *)

Global Instance inhabited_loc : Inhabited loc.
Proof.
  do 2 constructor. apply Z.inhabited.(inhabitant).
Qed.

(* Usage: [destruct (eqb_spec l1 l2)] will replace [eqb l1 l2] with [true] and
   add the hypothesis [l1 = l2] in a first subgoal, and the same with [false]
   and [l1 ≠ l2] in a second subgoal. *)
Lemma eqb_spec l1 l2 : reflect (l1 = l2) (eqb l1 l2).
Proof.
  apply iff_reflect.
  unfold eqb. rewrite Z.eqb_eq.
  destruct l1, l2; simpl; split; congruence.
Qed.
