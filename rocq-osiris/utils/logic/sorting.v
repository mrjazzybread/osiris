From Stdlib Require Import Program.Equality.
From Stdlib Require Export Sorting.Sorted.
Require Import stdpp.sorting.
Require Import base orders.
Local Opaque app. (* Prevent undesired simplification. *)

(* This file establishes several properties of sorted lists. *)

(* It complements the libraries Coq.Sorting.Sorted and stdpp.sorting,
   which seem quite poor. *)

Section JustTransitive.

(* -------------------------------------------------------------------------- *)

(* We assume a type [A] and a relation [lt] on this type. *)

(* We assume that this relation is transitive. We do not assume anything
   else; e.g., [lt] could be irreflexive, or it could be reflexive. *)

Context {A : Type}.
Context {lt : A → A → Prop}.
Context {Tlt : Transitive lt}.

(* Here, we write [x < y] when [x] is less than [y]. *)

Notation "x '<' y" := (lt x y).

Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* Coq defines [Sorted] and [StronglySorted]; these notions are equivalent. *)

Lemma Sorted_iff_StronglySorted xs :
  Sorted lt xs ↔ StronglySorted lt xs.
Proof.
  split; eauto using Sorted_StronglySorted, StronglySorted_Sorted.
Qed.

(* Here, we write just [sorted]. *)

Abbreviation sorted xs :=
  (Sorted lt xs).

(* -------------------------------------------------------------------------- *)

(* We write [xs ≺ ys] when every element of the list [xs] is less than
   every element of the list [ys]. This notion is used in the statement
   of the lemma [Sorted_app_iff], which is as follows:

     sorted (xs ++ ys) ↔
     sorted xs ∧ sorted ys ∧ xs ≺ ys

   The notation [xs ≺ ys] looks nice inside this section. Unfortunately,
   outside this section, one must write [pairwise lt xs ys]; it seems
   difficult to come with a generic infix notation. *)

Definition pairwise xs ys :=
  ∀ x y, x ∈ xs → y ∈ ys → x < y.

Notation "xs '≺' ys" := (pairwise xs ys) (at level 80).

(* -------------------------------------------------------------------------- *)

(* [pairwise] is transitive in the following restricted sense: transitivity
   requires the middle list to be nonempty. *)

Lemma pairwise_transitive_singleton xs y zs :
  xs ≺ [y] → [y] ≺ zs → xs ≺ zs.
Proof.
  unfold pairwise. intros Hl Hr x z.
  specialize (Hl x y).
  specialize (Hr y z).
  rewrite list_elem_of_singleton in *.
  eauto.
Qed.

Lemma pairwise_transitive_nonempty xs ys zs :
  ys ≠ [] →
  xs ≺ ys → ys ≺ zs → xs ≺ zs.
Proof.
  unfold pairwise. intros Hys Hl Hr x z.
  destruct ys as [| y ys]; [ congruence | clear Hys ].
  specialize (Hl x y).
  specialize (Hr y z).
  rewrite elem_of_cons in *.
  intuition eauto.
Qed.

(* [pairwise] interacts with list concatenation in a simple way. *)

Lemma pairwise_app_left_iff xs ys zs :
  xs ++ ys ≺ zs ↔ (xs ≺ zs) ∧ ys ≺ zs.
Proof.
  unfold pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

Lemma pairwise_app_right_iff xs ys zs :
  xs ≺ ys ++ zs ↔ (xs ≺ ys) ∧ xs ≺ zs.
Proof.
  unfold pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

(* [Forall (lt x) ys] can be reformulated in terms of [pairwise]. *)

(* This technical lemma is used below. *)

Local Lemma Forall_lt_iff x ys :
  Forall (lt x) ys ↔ [x] ≺ ys.
Proof.
  rewrite Forall_forall. unfold pairwise. split; intros H.
  { intros x' y. rewrite list_elem_of_singleton. intros ->. eauto. }
  { intros y ?. specialize (H x y). rewrite list_elem_of_singleton in H.
    eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The empty list is sorted. *)

Lemma Sorted_empty :
  sorted [].
Proof.
  econstructor.
Qed.

Lemma Sorted_empty_iff :
  sorted [] ↔ True.
Proof.
  split; eauto using Sorted_empty.
Qed.

(* A singleton list is sorted. *)

Lemma Sorted_singleton x :
  sorted [x].
Proof.
  econstructor.
  + eauto using Sorted_empty.
  + econstructor.
Qed.

Lemma Sorted_singleton_iff x :
  sorted [x] ↔ True.
Proof.
  split; eauto using Sorted_singleton.
Qed.

(* The concatenation [xs ++ ys] is sorted if and only if [xs] is sorted
   and [ys] is sorted and [xs ≺ ys] holds. *)

Lemma Sorted_app_inv_l xs ys :
  sorted (xs ++ ys) →
  sorted xs.
Proof.
  rewrite !Sorted_iff_StronglySorted. eauto using StronglySorted_app_1_l.
Qed.

Lemma Sorted_app_inv_r xs ys :
  sorted (xs ++ ys) →
  sorted ys.
Proof.
  rewrite !Sorted_iff_StronglySorted. eauto using StronglySorted_app_1_r.
Qed.

Lemma Sorted_app_inv_c xs ys :
  sorted (xs ++ ys) →
  xs ≺ ys.
Proof.
  rewrite !Sorted_iff_StronglySorted. intros.
  unfold pairwise. intros.
  eapply StronglySorted_app_1_elem_of; eauto.
Qed.

Lemma Sorted_app xs ys :
  sorted xs →
  sorted ys →
  xs ≺ ys →
  sorted (xs ++ ys).
Proof.
  rewrite !Sorted_iff_StronglySorted. revert xs ys.
  induction xs as [| x xs ]; intros ys Hxs Hys Hlt.
  { rewrite app_nil_l. assumption. }
  { rewrite <- app_comm_cons.
    dependent destruction Hxs. rewrite Forall_lt_iff in *.
    change (x :: xs) with ([x] ++ xs) in Hlt.
    rewrite pairwise_app_left_iff in Hlt. destruct Hlt.
    econstructor; rewrite ?Forall_lt_iff, ?pairwise_app_right_iff; eauto. }
Qed.

Lemma Sorted_app_iff xs ys :
  sorted (xs ++ ys) ↔
  sorted xs ∧ sorted ys ∧ xs ≺ ys.
Proof.
  intuition eauto
    using Sorted_app_inv_l, Sorted_app_inv_c, Sorted_app_inv_r, Sorted_app.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma HdRel_trans l x y :
  lt x y -> HdRel lt y l -> HdRel lt x l.
Proof.
  intros. destruct l; constructor.
  transitivity y;  [ done | by eapply HdRel_inv].
Qed.

(* If a list is sorted, then being smaller than the head is equivalent to
   being smaller than all elements of the list. *)

Lemma Sorted_HdRel_iff x l :
  Sorted lt l ->
  HdRel lt x l <-> Forall (lt x) l.
Proof.
  intros Hsort. induction l.
  { split; constructor. }
  { split.
    - intros Hhdrel.
      apply Sorted_inv in Hsort as [??].
      apply HdRel_inv in Hhdrel.
      constructor; auto.
      apply IHl; eauto using HdRel_trans.
    - intros Hforall. apply Forall_inv in Hforall; auto. }
Qed.

(* Let l be a sorted list, let l1 and l2 be two sorted lists partitioning l.
   An arbitrary x is smaller that the head of l if it is smaller than the head
   of l1 and the head of l2 *)

Lemma HdRel_Sorted_Permutation l l1 l2 x :
  Sorted lt l ->
  l1 ++ l2 ≡ₚ l ->
  Sorted lt l1 -> Sorted lt l2 ->
  HdRel lt x l1 -> HdRel lt x l2 ->
  HdRel lt x l.
Proof.
  intros ? Hperm ????.
  apply Sorted_HdRel_iff; try auto.
  rewrite <- Hperm.
  apply Forall_app.
  split; apply Sorted_HdRel_iff; auto.
Qed.


End JustTransitive.

Arguments pairwise {A} lt xs ys.

(* -------------------------------------------------------------------------- *)

(* We now assume that [lt] is a strict order, that is, both transitive and
   irreflexive. *)

Section TransitiveAndIrreflexive.

Context {A : Type}.
Context {lt : A → A → Prop}.
Context {Olt : StrictOrder lt}.
Notation "x '<' y" := (lt x y).
Notation "xs '≺' ys" := (pairwise lt xs ys) (at level 80).
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* -------------------------------------------------------------------------- *)

(* If [[x] ≺ ys] holds then [x] cannot be an element of the list [ys]. *)

Lemma pairwise_contradiction_left x ys :
  [x] ≺ ys →
  x ∈ ys →
  False.
Proof.
  unfold pairwise. intros Hlt Hmember.
  specialize (Hlt x x). rewrite list_elem_of_singleton in Hlt.
  eauto using strict_order_irreflexive.
Qed.

(* A symmetric statement. *)

Lemma pairwise_contradiction_right xs y :
  xs ≺ [y] →
  y ∈ xs →
  False.
Proof.
  unfold pairwise. intros Hlt Hmember.
  specialize (Hlt y y). rewrite list_elem_of_singleton in Hlt.
  eauto using strict_order_irreflexive.
Qed.

(*[x < y] implies [[x] ≺ [y]]. *)

Lemma lt_pairwise x y :
  x < y →
  [x] ≺ [y].
Proof.
  unfold pairwise. intros ? x' y'.
  rewrite !list_elem_of_singleton. intros; subst.
  assumption.
Qed.

(* A characteristic property of sorted lists, which is exploited in binary
   search trees: if [x] is less than [y], and if the elements of [zs] are
   greater than [y], then searching for [x] in the list [xs ++ [y] ++ zs]
   boils down to searching for [x] in the list [xs]. *)

Lemma bst_search_left x xs y zs :
  x < y →
  [y] ≺ zs →
  x ∈ xs ++ [y] ++ zs ↔ x ∈ xs.
Proof.
  assert (Transitive lt) by typeclasses eauto.
  intros.
  rewrite !elem_of_app, list_elem_of_singleton.
  split; [| eauto ].
  intros [|[|]]; [| subst y; exfalso | exfalso ].
  { eauto. }
  { eauto using strict_order_irreflexive. }
  { eauto using lt_pairwise, pairwise_transitive_singleton,
                pairwise_contradiction_left. }
Qed.

(* A symmetric statement. *)

Lemma bst_search_right x xs y zs :
  y < x →
  xs ≺ [y] →
  x ∈ xs ++ [y] ++ zs ↔ x ∈ zs.
Proof.
  assert (Transitive lt) by typeclasses eauto.
  intros.
  rewrite !elem_of_app, list_elem_of_singleton.
  split; [| eauto ].
  intros [|[|]]; [ exfalso | subst y; exfalso |].
  { eauto using lt_pairwise, pairwise_transitive_singleton,
                pairwise_contradiction_right. }
  { eauto using strict_order_irreflexive. }
  { eauto. }
Qed.

End TransitiveAndIrreflexive.

(* -------------------------------------------------------------------------- *)

(* We now assume not only that [lt] is a strict preorder, but also that [lt]
   is [strict le], where [le] is a preorder. *)

(* We define a notion of membership in a list modulo the preorder [le] and
   we establish a few key properties of this notion. These properties help
   reason about binary search trees in a setting where [le] is not
   necessarily antisymmetric. *)

Section PreOrder.

Context {A : Type}.
Context (le : A → A → Prop).
Context {Ple : PreOrder le}.
Local Set Warnings "-notation-overridden".
Notation "x '≤' y" := (le x y).

Abbreviation lt := (strict le).
Notation "x '<' y" := (lt x y).
Notation "xs '≺' ys" := (pairwise lt xs ys) (at level 80).

Abbreviation eq := (equivalent le).
Notation "x '≡' y" := (eq x y).

Implicit Types x y z : A.
Implicit Types xs ys zs : list A.
Implicit Type ox : option A.

(* We define membership in a list, up to the preorder [le], as a 3-place
   relation [member x xs ox'], where [x] is the desired element, [xs] is
   the list of interest, and [ox'] is the result of searching for [x] in
   the list: it is an element of the list that is equivalent to [x], if
   there is one. *)

(* Outside this section, one must write [member le x xs ox']. *)

Definition member x xs ox' :=
  match ox' with
  | None =>
      (* If [ox'] is [None] then no element that is equivalent to [x]
         appears in the list. *)
      ∀ x', x ≡ x' → x' ∉ xs
  | Some x' =>
      (* If [ox'] is [Some x'] then [x'] is equivalent to [x] and
         appears in the list. *)
      x ≡ x' ∧ x' ∈ xs
  end.

(* No element is a member of the empty list. *)

Lemma member_empty x ox' :
  member x [] ox' ↔
  ox' = None.
Proof.
  destruct ox' as [x'|]; simpl member.
  (* Case: [Some]. *)
  { rewrite elem_of_nil. split; [ tauto | congruence ]. }
  (* Case: [None]. *)
  { split; [ tauto | intros ]. rewrite elem_of_nil. tauto. }
Qed.

(* A characteristic property of sorted lists, which is exploited in binary
   search trees: if [x] is less than [y], and if the elements of [zs] are
   greater than [y], then searching for [x] in the list [xs ++ [y] ++ zs]
   boils down to searching for [x] in the list [xs]. *)

(* This lemma is analogous to [bst_search_left], but uses [member x xs]
   instead of [x ∈ xs]. *)

Lemma bst_member_left x xs y zs ox' :
  x < y →
  [y] ≺ zs →
  member x (xs ++ [y] ++ zs) ox' ↔
  member x xs ox'.
Proof.
  intros. destruct ox' as [x'|]; simpl member.
  (* Case: [Some]. *)
  { apply share_common_conjunct; intro. destruct_equivalent.
    rewrite (@bst_search_left _ lt _) by eauto using strict_transitive_r.
    tauto. }
  (* Case: [None]. *)
  { apply share_common_hypothesis; intro x'.
    apply share_common_hypothesis; intro. destruct_equivalent.
    rewrite (@bst_search_left _ lt _) by eauto using strict_transitive_r.
    tauto. }
Qed.

(* A symmetric statement. *)

Lemma bst_member_right x xs y zs ox' :
  y < x →
  xs ≺ [y] →
  member x (xs ++ [y] ++ zs) ox' ↔
  member x zs ox'.
Proof.
  intros. destruct ox' as [x'|]; simpl member.
  (* Case: [Some]. *)
  { apply share_common_conjunct; intro. destruct_equivalent.
    rewrite (@bst_search_right _ lt _) by eauto using strict_transitive_l.
    tauto. }
  (* Case: [None]. *)
  { apply share_common_hypothesis; intro x'.
    apply share_common_hypothesis; intro. destruct_equivalent.
    rewrite (@bst_search_right _ lt _) by eauto using strict_transitive_l.
    tauto. }
Qed.

End PreOrder.
