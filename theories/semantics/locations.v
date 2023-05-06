From stdpp Require Import countable numbers gmap.

(* TODO:
   - add the required lemmas so that the types declared below can remain opaque
     to the rest of the development. *)

(* The following section comes from the file
   [iris_heap_lang/locations.v] available in the [iris] repository. *)

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

  Definition fresh_locs (ls : gset loc) : loc :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z ls |}.

  Lemma fresh_locs_fresh ls :
    fresh_locs ls ∉ ls.
  Proof.
    cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls))%Z.
    { intros help Hf%help. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r)%Z));
    set_solver by eauto with lia.
  Qed.

End Locations.
