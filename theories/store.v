From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

Require Import lang.


(* TODO:
 * - add the required lemmas so that the above types can remain opaque to the
 *   rest of the development.
 * - declare the required instances of [ElemOf] and [Dom].
 *)

(* -------------------------------------------------------------------------- *)
(* Locations: The following section comes from the file 
 * [iris_heap_lang/locations.v] available in the [iris] repository. *)

Section Locations.

  Record loc := Loc { loc_car : Z }.

  Add Printing Constructor loc.

  Global Instance loc_eq_decision : EqDecision loc.
  Proof. solve_decision. Defined.

  Global Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

  Global Instance loc_countable : Countable loc.
  Proof. by apply (inj_countable' loc_car Loc); intros []. Defined.

  Global Program Instance loc_infinite : Infinite loc :=
    inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
  Next Obligation. done. Qed.

  Definition loc_add (l : loc) (off : Z) : loc :=
    {| loc_car := loc_car l + off|}.

  Notation "l +ₗ off" :=
    (loc_add l off) (at level 50, left associativity) : stdpp_scope.

  Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
  Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

  Lemma loc_add_0 l : l +ₗ 0 = l.
  Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

  Global Instance loc_add_inj l : Inj eq eq (loc_add l).
  Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

  Definition fresh_locs (ls : gset loc) : loc :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z ls |}.

  Lemma fresh_locs_fresh ls i :
    (0 ≤ i)%Z → fresh_locs ls +ₗ i ∉ ls.
  Proof.
    intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls) + i)%Z.
    { intros help Hf%help. simpl in *. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)%Z));
    set_solver by eauto with lia.
  Qed.
End Locations.

(* -------------------------------------------------------------------------- *)
(* The following section defines the physical store *)

Section Store.
  Definition store : Type := gmap loc val.


  (* [store_ref] finds a fresh location to add to its argument.
   * It returns the fresh location and the updated store. *)
  Definition store_ref (s: store) (v: val) : loc * store :=
    let l := fresh_locs (dom s) in
    (l, <[l := v]>s).

  Lemma store_ref_dom (s: store) (v: val) :
    let '(l, s') := store_ref s v in
    dom s' = (dom s) ∪ {[ l ]} ∧ l ∉ dom s.
  Proof.
    split; first set_solver.
    unshelve epose proof (fresh_locs_fresh (dom s) 0 _) as H; first reflexivity.
    rewrite loc_add_0 in H.
    assumption.
  Qed.


  Global Instance val_inhabited: Inhabited val := populate VUnit.

  (* [store_load] lookups the store to find a value given a location (which is 
   * guaranteed to be valid). *)
  (* TODO: directly write a term that represents this function. *)
  Definition store_load (s: store) (l: loc) (Hsl: l ∈ dom s) : val.
  Proof.
    destruct (s !! l) eqn:E.
    - exact v.
    - apply lookup_lookup_total_dom in Hsl.
      rewrite E in Hsl.
      inversion Hsl.
  Qed.


  (* [store_store] updates a value of a store. The location that gets updated 
   * has to be valid beforehand. This is enforced by the request of an argument 
   * of type [l ∈ dom s]. *)
  Definition store_store (s: store) (l: loc) (v: val) (_: l ∈ dom s) : store :=
    <[ l := v ]> s.

End Store.

(*Global Opaque fresh_locs.
Global Opaque store.*)
