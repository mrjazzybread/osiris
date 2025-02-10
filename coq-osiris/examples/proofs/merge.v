Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.logic Require Import sorting.
From osiris.examples Require Import og_merge.

(* -------------------------------------------------------------------------- *)

(* WIP: Tactics used in local proof scripts. *)

Local Ltac rewrite_permutation t :=
  lazymatch goal with
  | H : t ≡ₚ _ |- _ => rewrite H || (revert H; rewrite_permutation t)
  | H : _ ≡ₚ t |- _ => rewrite <- H || (revert H; rewrite_permutation t)
  end.

Local Ltac Sorted_inversion :=
  match goal with
  | H : Sorted _ (_ :: _) |- _ =>
      apply Sorted_inv in H as [H?]
  end.

Local Ltac HdRel_inversion :=
  lazymatch goal with
  | H : HdRel _ _ (_ :: _) |- _ =>
      apply HdRel_inv in H as H
  end.

Local Ltac Forall_inversion :=
  match goal with
  | H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H
  end.

Local Ltac all_inversions :=
  repeat (Sorted_inversion || (HdRel_inversion || Forall_inversion)).

(* -------------------------------------------------------------------------- *)

(* Helper Lemmas. *)

Lemma even_false_odd_true n : Nat.even n = false <-> Nat.odd n = true.
Proof.
  split;
    [rewrite <- Nat.negb_even | rewrite <- Nat.negb_odd];
    [ apply negb_true_iff; auto   | apply negb_false_iff; auto ].
Qed.

Local Hint Resolve even_false_odd_true : arith.

(* We implicitly use the following lemma when we prove that the list returned
   by [split l] are smaller than l *)

Lemma suc_div2_lt_suc n :
    (Nat.div2 n < S n)%nat.
Proof.
 destruct (Nat.even n) eqn:Hn.
 { (* Case: n is even *)
   rewrite Nat.Even_div2.
   - apply Nat.lt_div2; lia.
   - apply Nat.even_spec. assumption. }
 { (* Case: n is odd *)
   apply Nat.succ_lt_mono.
   rewrite Nat.Odd_div2; auto with arith.
   apply Nat.odd_spec. apply even_false_odd_true. assumption. }
Qed.

Local Hint Resolve suc_div2_lt_suc : arith.

Lemma div2_lt_succ n m :
  (if Nat.even m
   then n = S (Nat.div2 m)
   else n = S (S (Nat.div2 m))) ->
  (n < S (S m))%nat.
Proof.
  destruct (Nat.even m) eqn:Hm; intros ->.
  { (* Case: m is even *)
    auto with arith. }
  { (* Case: m is odd *)
    rewrite Nat.Odd_div2; auto with arith.
    apply Nat.odd_spec. apply even_false_odd_true. assumption. }
Qed.

(* Make a library of commonly used well founded relations? *)

Lemma wf_double_list_length {A B} :
  well_founded (fun (p1 p2 : list A * list B) =>
                  (length p1.1 + length p1.2 < length p2.1 + length p2.2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

#[local] Program Instance list_wf {A} : WellFounded (list A) :=
  {| wf_relation := (fun l1 l2 => length l1 < length l2)%nat |}.
Next Obligation. intros. apply wf_inverse_image, lt_wf. Qed.

#[local] Program Instance list_tuple_wf {A B}
  : WellFounded (list A * list B) :=
  {| wf_relation :=
      (fun p1 p2 =>
         (length p1.1 + length p1.2 < length p2.1 + length p2.2)%nat) |}.
Next Obligation. intros. apply wf_inverse_image, lt_wf. Qed.

(* -------------------------------------------------------------------------- *)

(* Specification for [merge l1 l2]. *)

Definition merge_spec (l1 : list Z) (l2 : list Z) (m : microvx) : Prop :=
  (* Preconditions on [l1] and [l2]. *)
  Forall representable l1 ∧ Sorted Z.le l1 ->
  Forall representable l2 ∧ Sorted Z.le l2 ->
  (* Specification of the function call [merge l1 l2]. *)
  pure m (λ l, Sorted Z.le l ∧ Permutation (l1++l2) l) ⊥.


(* Specification for [split l]. *)

Local Definition split_post {A} :=
  (fun (l : list A) p => (if Nat.even (length l)
            then length p.1 = Nat.div2 (length l)
            else length p.1 = S (Nat.div2 (length l)))
           /\ length p.2 = Nat.div2 (length l) /\ Permutation (p.1 ++ p.2) l).

Definition split_spec `{Encode A} (l : list A) (m : microvx) : Prop :=
  pure m (split_post l) ⊥.


(* Specification for [mergesort l]. *)

Definition mergesort_spec (l : list Z) (m : microvx) : Prop :=
  (* Precondition on [l]. *)
  Forall representable l ->
  (* Specification of the function call [mergesort l]. *)
  pure m (λ l', Sorted Z.le l' ∧ Permutation l' l) ⊥.

(* Specification for [mergesort l]. *)

Local Definition mergesort_pre := (fun l => Forall representable l).
Local Definition mergesort_post := (fun l l' => Sorted Z.le l' /\ Permutation l' l).
Local Hint Unfold mergesort_post : core.
Local Hint Unfold mergesort_pre : core.

Definition mergesort_spec' (l : list Z) (e : microvx) : Prop :=
  mergesort_pre l ->
  pure e (mergesort_post l) ⊥.

(* -------------------------------------------------------------------------- *)

Local Ltac trivial_pure := repeat (first [ pure_path | pure_data | pure_const]).

Local Ltac pure_EOpLe :=
  eapply pure_eval_EOpLe;
  [ trivial_pure; reflexivity
  | trivial_pure; reflexivity
  |
  | ].

(* Pure, Hoare-Style Specification proofs. *)

Section proof.

(* We abstract over the environment, making localised assumptions
   about what it contains when necessary. *)

Variable η : env.

(* TODO: This is not the level of abstraction that we want to present
   the user with. It shouldn't be required to write the induction
   hypothesis or the [EMatch] expression by hand. *)

Lemma merge_mkspec merge (l1 l2 : list Z) :
  (lookup_name η "l1" = ret #l1) ->
  (lookup_name η "l2" = ret #l2) ->
  (lookup_name η "merge" = ret merge) ->
  @Spec τ[list Z; list Z] merge
    (λ (x1 x2 : list Z) (m : microvx),
      (length x1 + length x2 < length l1 + length l2)%nat
      → merge_spec x1 x2 m)
  → merge_spec l1 l2
      (eval η
         (EMatch (ETuple [EPath ["l1"]; EPath ["l2"]]) __branches2)).
Proof.
   intros Hl1 Hl2 Hmerge IH.
   unfold merge_spec. intros [Hreprl1 Hsortl1] [Hreprl2 Hsortl2].
   eapply pure_eval_match.
   { eapply pure_eval_pair.
     eapply pure_eval_path. simpl; rewrite Hl1. pure_ret.
     eapply pure_eval_path. simpl; rewrite Hl2. pure_ret. }

   pure_match; abstract_env.

   { pure_path. }
   { pure_path. split; [ | rewrite app_nil_r ]; auto. }

   eapply pure_eval_ifthenelse.
   { (* Evaluate expression "h1 <= h2" *)
     pure_EOpLe; repeat Forall_inversion; auto. }
   { (* Evaluate expression "h1 :: (merge t1 l2)" knowing h1 <= h2 *)
     intros.
     eapply pure_eval_data. eapply pure_evals_cons.
     pure_path.
     (* FIXME (IY): Automation for encode is broken.
         Probably encode shouldn't unfold here? *)
     unfold observe, observe_encode. encode.
     eapply @pure_evals_cons with (A := list Z).

     (* Evaluate "merge t1 l2" under the cons *)
     eapply (pure_EApp τ[list Z; list Z]).
     { eapply pure_eval_path; simpl; rewrite Hmerge. pure_ret. }
     { pure_path. apply eq_refl. }
     { eapply pure_eval_path; simpl; rewrite Hl2; eapply pure_ret.
       encode. apply eq_refl. }
     simpl; unfold tapp.
     intros t1 l2 -> Ht1.
     intros m Hm.
     unfold merge_spec in Hm.
     all_inversions.
     eapply pure_ret_mono.
     { apply Hm.
       - simpl; auto with arith. - split; auto. - split; auto. }
     intros l [Hsorted Hpermutation].
     eapply pure_evals_nil.
     exists (x :: l).
     split; [ encode | split ].
     + (* Subgoal: the output is sorted *)
       constructor; [ assumption | ].
       eapply HdRel_Sorted_Permutation; eauto with zarith.
     + (* Subgoal: the output is a permutation of the inputs *)
       by rewrite_permutation l. }

   { (* Evaluate expression "h2 :: (merge l1 t2)" knowing  (h1 > h2) *)
     simpl; intros. fold eval.
     eapply pure_eval_data. eapply pure_evals_cons.
     pure_path.
     (* FIXME *)
     unfold observe, observe_encode. encode.
     eapply @pure_evals_cons with (A := list Z).

     (* Evaluate "merge l1 t2" under the cons *)
     eapply (pure_EApp τ[list Z; list Z]).
     { eapply pure_eval_path; simpl; rewrite Hmerge. pure_ret. }
     { eapply pure_eval_path. simpl; rewrite Hl1; eapply pure_ret.
       encode. apply eq_refl. }
     { pure_path. apply eq_refl. }

     unfold tbind, tapp.
     intros ? ? <- <-.
     intros m Hm.
     eapply pure_ret_mono.
     { apply Hm.
       - simpl; lia. - split; auto. - split; by all_inversions. }

     intros l [Hsorted Hpermutation].
     apply pure_evals_nil.
     exists (x0 :: l).
     split; [ encode | split ].
     + (* Subgoal: the output is sorted *)
       constructor; [ assumption | ].
       eapply HdRel_Sorted_Permutation; eauto with zarith;
         by all_inversions.
     + (* Subgoal: the output is a permutation of the inputs *)
       rewrite_permutation l.
       apply Permutation_sym. apply Permutation_middle. }
Qed.

(* We make a nested section, which adds the assumption that [merge]
   satisfies its spec to the environment.

   We could delay this because [split] does not depend on [merge]. *)

Section merge.

Variable merge : val.
Hypothesis _merge_spec : @Spec τ[list Z; list Z] merge merge_spec.
Hypothesis Hmerge : lookup_name η "merge" = ret merge.

Lemma split_mkspec split (l : list Z) :
  (lookup_name η "l" = ret #l) ->
  (lookup_name η "split" = ret split) ->
  Spec split
    (tbind
       (λ (x : τ[list Z]) (m : microvx),
         (length x < length l)%nat → split_spec x m)) ->
  split_spec l (eval η (EMatch (EPath ["l"]) __branches6)).
Proof.
  intros Hl Hsplit IH.
  unfold split_spec.
  eapply pure_eval_match.
  { eapply pure_eval_path. simpl. rewrite Hl. pure_ret. }

  pure_match; abstract_env.

  (* First branch of match *)
  { (* Case: l matches [] *)
    apply pure_eval_pair;
      repeat (eapply pure_eval_const; encode).
    (* Establish the (trivial) postcondition *)
    split; simpl; auto. }
  (* Second branch of match *)
  { (* Case: l matches [x] *)
    apply pure_eval_pair.
    eapply pure_eval_data. eapply pure_evals_cons.
    pure_path. simpl. encode.
    eapply pure_evals_cons.
    (* FIXME. *) eapply pure_eval_const with (x := @nil Z). encode.
    eapply pure_evals_nil.
    exists ([x]); split; [ encode | ].
    eapply pure_eval_const. encode.
    (* Establish postcondition *)
    split; simpl; auto. }
  (* Third branch of match *)
  { (* Case: l matches a::b::t *)
    eapply pure_eval_let_pair.
    eapply (pure_EApp τ[list Z]).
    { eapply pure_eval_path; simpl; rewrite Hsplit. pure_ret. }
    { pure_path. apply eq_refl. }
    unfold tbind.
    intros l -> m Hm.
    unfold split_spec in Hm.
    eapply pure_ret_mono. { apply Hm. simpl; lia. }
    intros [l1 l2] Hpost; clear IH; simpl.
    (* FIXME. *)
    simpl_extend; simpl. fold eval. abstract_env.
    (* Eval (x1::l1, x2::l2) *)
    apply pure_eval_pair.
    eapply pure_eval_data. eapply pure_evals_cons. pure_path.
    simpl; encode.
    eapply pure_evals_cons. pure_path. simpl; encode.
    eapply pure_evals_nil. exists (x1 :: l1); split; [ encode | ].
    eapply pure_eval_data. eapply pure_evals_cons. pure_path.
    simpl; encode.
    eapply pure_evals_cons. pure_path. simpl; encode.
    eapply pure_evals_nil. exists (x :: l2); split; [ encode | ].
    (* Establish postcondition *)
    unfold split_post in *; simpl in *.
    subst.
    destruct Hpost as (Hlength1 & Hlength2 & ?).
    split; [ | split ].
    { (* Subgoal: the length of l1 is half the length of xs *)
      destruct (Nat.even _); rewrite Hlength1; eauto with arith. }
    { (* Subgoal: the length of l2 is half the length of xs *)
      rewrite Hlength2; eauto with arith. }
    { (* Subgoal: l1++l2 is a permutation of xs *)
      rewrite_permutation l.
      apply Permutation_skip.
      apply Permutation_sym.
      apply Permutation_middle. } }
Qed.

(* We make a new section, adding the hypotheses that [split] is in the
   environment and satisfies its spec. *)

Section split.

Variable split : val.
Hypothesis _split_spec : @Spec τ[list Z] split split_spec.
Hypothesis Hsplit : lookup_name η "split" = ret split.

Lemma mergesort_mkspec mergesort (l : list Z) :
  (lookup_name η "l" = ret #l) ->
  (lookup_name η "merge_sort" = ret mergesort) ->
  (Spec mergesort (@tbind _ τ[list Z] (λ x m,
       (length x < length l)%nat ->
       mergesort_spec x m))) ->
  mergesort_spec l (eval η (EMatch (EPath ["l"]) __branches11)).
Proof.
  intros Hl Hmergesort IH Hpre.

  eapply pure_eval_match. { eapply pure_eval_path.
                            simpl. rewrite Hl. pure_ret. }
  pure_match.
  (* Branch: "[]"  *)
  { pure_const. auto. }
  (* Branch: "[x]" *)
  { eapply pure_eval_data. eapply pure_evals_cons.
    pure_path. simpl; encode.
    eapply pure_evals_cons. eapply pure_eval_const with (x := @nil Z).
    encode.
    eapply pure_evals_nil. exists [x]. split; [ encode | auto ]. }

  (* Branch: "_" *)
  assert (exists m, length (x0) = S m) as [m Heql].
  { subst. destruct x0; [ congruence | eauto ]. }
  simpl in IH. rewrite Heql in IH.
  eapply pure_eval_let_pair.
  (* Use knowledge that [split] ⊨ [split_spec] *)
  eapply (pure_EApp τ[list Z]).
  { eapply pure_eval_path. simpl. rewrite Hsplit.
    pure_ret. }
  { eapply pure_eval_path. simpl. rewrite Hl.
    eapply pure_ret. encode. apply eq_refl. }
  unfold tbind.
  intros l <- ms Hsplitm.
  eapply pure_ret_mono. { apply Hsplitm. }
  intros [l1 l2] (Hl1 & Hl2 & Hperm).
  rewrite <- Hperm in Hpre; apply Forall_app in Hpre as [??].
  simpl_extend; simpl.

  eapply pure_eval_let1var.
  { eapply (pure_EApp τ[list Z]).
    eapply pure_eval_path. simpl. rewrite Hmergesort. pure_ret.
    eapply pure_eval_path. eapply pure_ret. encode. apply eq_refl.
    unfold tbind.
    intros l -> mm Hcall.
    apply Hcall.
    - simpl in Hperm, Hl1, Hl2.
      rewrite Heql in Hl1, Hl2 |-*.
      apply div2_lt_succ. apply Hl1.
    - assumption. }

  intros l1' IHl1'.
  eapply pure_eval_let1var.
  { eapply (pure_EApp τ[list Z]).
    eapply pure_eval_path. simpl. rewrite Hmergesort. pure_ret.
    eapply pure_eval_path. eapply pure_ret. encode. apply eq_refl.
    unfold tbind.
    intros ? -> mm Hcall. apply Hcall.
    - rewrite Hl2. simpl. destruct (length x0); auto with arith.
      inversion Heql. auto with arith.
    - assumption. }

  intros l2' IHl2'; clear IH Hl1 Hl2 Heql m.
  abstract_env.
  eapply (pure_EApp τ[list Z; list Z]).
  - (* Use the knowledge that [merge] ∈ [η] *)
    eapply pure_eval_path. simpl; rewrite Hmerge. pure_ret.
  - eapply pure_eval_path. eapply pure_ret. encode. apply eq_refl.
  - eapply pure_eval_path. eapply pure_ret. encode. apply eq_refl.
  - simpl. intros ? ? <-. unfold tapp. intros <- m Hmerge'.
    unfold merge_spec in Hmerge'.
    simpl in IHl1', IHl2'; destruct IHl1' as [??]; destruct IHl2' as [??].
    eapply pure_ret_mono. apply Hmerge'.
    * split; [ by rewrite_permutation l1' | assumption ].
    * split; [ by rewrite_permutation l2' | assumption ].
    * intros l' IH.
      (* Subgoal: show that [l'] ⊨ [mergesort_post] *)
      cbn in IH; destruct IH as [??].
      split; [ assumption | ].
      rewrite_permutation l'. rewrite_permutation (x :: x0).
      rewrite_permutation l1'. rewrite_permutation l2'.
      reflexivity.
Qed.

End split.
End merge.
End proof.

(* We chain together the lemmas in the [proof] section to verify the
   whole [merge.ml] file. *)

Lemma Module__spec' :
  eval_module stdlib_env __main (λ _, True).
Proof.
  apply module_struct.
  (* Proof that [merge] satisfies [merge_spec]. *)
  eapply (@structs_letrec τ[list Z; list Z]) with
    (P := merge_spec). repeat constructor.
  { apply wf_double_list_length. }
  { unfold unfold_spec; simpl.
    intros merge l1 l2 IH.
    eapply merge_mkspec; eauto. }
  intros merge Hmerge.

  (* Proof that [split] satisfies [split_spec]. *)
  eapply (structs_letrec τ[list Z]) with
    (P := split_spec).
  { apply list_wf. }
  { intros split l IH.
    eapply split_mkspec; eauto. }
  intros split Hsplit.

  (* Proof that [merge_sort] satisfies [mergesort_spec]. *)
  eapply (@structs_letrec τ[list Z]) with
    (P := mergesort_spec). repeat constructor.
  { apply list_wf. }
  { unfold unfold_spec; simpl.
    intros mergesort l IH.
    eapply mergesort_mkspec; eauto. }
  intros mergesort Hmergesort.

  (* We have now evaluated the whole struct. *)
  finished_struct.
  (* Goal: Show that the resulting environment satisfies the spec. *)
  simpl. repeat split; assumption.
Qed.
