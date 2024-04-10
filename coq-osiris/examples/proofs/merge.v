Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.logic Require Import sorting.
From osiris.examples Require Import og_merge.

Notation "'<(' f ')>'" := (VCloRec _ _ f) (only printing).
Notation "'<' f '>'" := (VClo _ f) (only printing).
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (cons x _ (.. (cons z _ nil) ..))
 (only printing).

(* -------------------------------------------------------------------------- *)

(* WIP: Tactics used in local proof scripts. *)

Local Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

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
  split; intros;
    [rewrite <- Nat.negb_even | rewrite <- Nat.negb_odd];
    [by apply negb_true_iff   | by apply negb_false_iff].
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
   - by apply Nat.even_spec. }
 { (* Case: n is odd *)
   apply Nat.succ_lt_mono.
   rewrite Nat.Odd_div2; auto with arith.
   apply Nat.odd_spec. by apply even_false_odd_true. }
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
    apply Nat.odd_spec. by apply even_false_odd_true. }
Qed.

(* Make a library of commonly used well founded relations? *)

Lemma wf_list_length {A : Type} :
  well_founded (fun (l1 l2 : list A) => (length l1 < length l2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

Lemma wf_double_list_length {A B} :
  well_founded (fun (p1 p2 : list A * list B) =>
                  (length p1.1 + length p1.2 < length p2.1 + length p2.2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

(* -------------------------------------------------------------------------- *)

(* Specification for [merge l1 l2]. *)

Local Definition merge_pre :=
  (fun l1 l2 => Forall representable l1 /\ Forall representable l2
             /\ Sorted Z.le l1 /\ Sorted Z.le l2).
Local Definition merge_post := (fun l1 l2 l => Sorted Z.le l /\ Permutation (l1++l2) l).
Local Hint Unfold merge_post : core.
Local Hint Unfold merge_pre : core.

Definition merge_spec (merge : val) : Prop :=
  ∀ (l1 l2 : list Z),
    merge_pre l1 l2 ->
    pure
      (call merge #l1)
      (fun c =>
         pure (call c #l2) (merge_post l1 l2)).


(* Specification for [split l]. *)

Local Definition split_post {A} :=
  (fun (l : list A) p => (if Nat.even (length l)
            then length p.1 = Nat.div2 (length l)
            else length p.1 = S (Nat.div2 (length l)))
           /\ length p.2 = Nat.div2 (length l) /\ Permutation (p.1 ++ p.2) l).

Definition split_spec (split : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list A),
    pure
      (call split #l)
      (split_post l).


(* Specification for [mergesort l]. *)

Local Definition mergesort_pre := (fun l => Forall representable l).
Local Definition mergesort_post := (fun l l' => Sorted Z.le l' /\ Permutation l' l).
Local Hint Unfold mergesort_post : core.
Local Hint Unfold mergesort_pre : core.

Definition mergesort_spec (mergesort : val) : Prop :=
  ∀ (l : list Z),
    mergesort_pre l ->
    pure
      (call mergesort #l)
      (mergesort_post l).

(* -------------------------------------------------------------------------- *)

(* Pure, Hoare-Style Specification proofs. *)

Global Instance CRel2Cons `{Encode A} : CRel2 A (list A) (list A) "::" cons := {}.

Ltac trivial_pure := repeat first [ pure_path | pure_data | pure_const].

Ltac pure_eval_app2_conseq :=
  eapply pure_eval_app2_conseq;
  [ trivial_pure; reflexivity
  | trivial_pure; reflexivity
  | trivial_pure; reflexivity
  |
  | ].

Ltac pure_EOpLe :=
  eapply pure_eval_EOpLe;
  [ trivial_pure; reflexivity
  | trivial_pure; reflexivity
  |
  | ].

Lemma Merge_spec' η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec.
  intros.
  pure_nested l1 l2 (@wf_double_list_length Z).
  unfold merge_pre in *; repeat (destruct_hyp).
  abstract_env.
  eapply pure_eval_match.
  { eapply pure_eval_pair. trivial_pure.
    reflexivity. }
  unfold __branches2; pure_match.
  (* First branch of match *)
  { pure_path.
    (* Establish postcondition *)
    unfold merge_post, merge_pre in *; repeat (destruct_hyp).
    done. }
    (* Match against "l, []" *)
  { pure_path.
    (* Establish postcondition *)
    unfold merge_post, merge_pre in *; repeat (destruct_hyp).
    by rewrite app_nil_r. }
  (* Second branch of match *)
  { eapply pure_eval_ifthenelse.
    { (* Evaluate expression "h1 <= h2" *)
      pure_EOpLe; by subst; repeat Forall_inversion. }
    { (* Evaluate expression "h1 :: (merge t1 l2)" knowing h1 <= h2 *)
      intros. unfold __exp0.
      pure_data.
      (* Evaluate "merge t1 l2" under the cons *)
      pure_eval_app2_conseq.
      { (* Use induction hypothesis on [call merge t1 l2] *)
        eapply IH.
        { (* Subgoal: the partial application of merge returns a closure *)
          rewrite eval_eval'; simpl. reflexivity. }
        { (* Subgoal: t1 and l2 satisfy merge's precondition *)
          unfold merge_pre in *.
          repeat (destruct_hyp); all_inversions; auto. }
        { (* Subgoal: justify the recursive call with a size argument *)
          auto with arith. } }
      intros l Hpost.
      split; auto.
      (* Establish the postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp); subst; all_inversions.
      split.
      { (* Subgoal: the output is sorted *)
        constructor; first done.
        eapply HdRel_Sorted_Permutation; eauto with zarith. }
      { (* Subgoal: the output is a permutation of the inputs *)
        by rewrite_permutation l. } }
    { (* Evaluate expression "h2 :: (merge l1 t2)" knowing  (h1 > h2) *)
      simpl; intros. unfold __exp1.
      pure_data.
      (* Evaluate "merge l1 t2" under the cons *)
      pure_eval_app2_conseq.
      (* Use induction hypothesis on [call merge l1 t2] *)
      { eapply IH.
        { (* Subgoal: the partial application of merge returns a closure *)
          rewrite eval_eval'; simpl. reflexivity. }
        { (* Subgoal: l1 and t2 satisfy merge's precondition *)
          unfold merge_pre in *.
          repeat (destruct_hyp); all_inversions; auto. }
        { (* Subgoal: justify the recursive call with a size argument *)
          auto with arith. } }
      intros l Hpost.
      split; auto.
      (* Establish the postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp); subst; all_inversions.
      split.
      { (* Subgoal: the output is sorted *)
        constructor; first done.
        eapply HdRel_Sorted_Permutation; eauto with zarith. }
      { (* Subgoal: the output is a permutation of the inputs *)
        rewrite_permutation l.
        apply Permutation_sym. apply Permutation_middle. } } }
Qed.

Lemma Split_spec' η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec. intros.
  pure_rec l (@wf_list_length A).
  (* Goal: eval match on l *)
  eapply pure_eval_match. { pure_path. apply eq_refl. }
  unfold __branches6; simpl.
  (* First branch of match *)
  pure_match; abstract_env.
  { (* Case: l matches [] *)
    apply pure_eval_pair. trivial_pure.
    (* Establish the (trivial) postcondition *)
    done. }
  (* Second branch of match *)
  { (* Case: l matches [x] *)
    apply pure_eval_pair. trivial_pure.
    (* Establish postcondition *)
    done. }
  (* Third branch of match *)
  { (* Case: l matches a::b::t *)
    eapply pure_eval_let_pair.
    eapply pure_eval_app. trivial_pure.
    (* Call vf #xs *) simpl.
    eapply pure_consequence.
    { (* Use induction hypothesis *)
      apply IH; first done.
      (* Justify use of induction hypothesis *)
      eauto with arith. }
    intros [l1 l2] Hpost; clear IH; simpl.
    abstract_env.
    (* Eval (x1::l1, x2::l2) *)
    apply pure_eval_pair. trivial_pure.
    (* Establish postcondition *)
    unfold split_post in *; simpl in *.
    subst.
    destruct Hpost as (H1 & H2 & ?).
    split; last split.
    { (* Subgoal: the length of l1 is half the length of xs *)
      destruct (Nat.even _); rewrite H1; eauto with arith. }
    { (* Subgoal: the length of l2 is half the length of xs *)
      rewrite H2; eauto with arith. }
    { (* Subgoal: l1++l2 is a permutation of xs *)
      rewrite_permutation xs'0.
      apply Permutation_skip.
      apply Permutation_sym.
      apply Permutation_middle. } }
Qed.

Lemma MergeSort_spec' η :
  (exists split, lookup_name η "split" = ret split /\ split_spec split) ->
  (exists merge, lookup_name η "merge" = ret merge /\ merge_spec merge) ->
  mergesort_spec (VCloRec η __bindings12 "merge_sort").
Proof.
  (* Destruct the hypotheses on split and merge *)
  destruct 1 as (split&Hsplit&_split_spec).
  destruct 1 as (merge&Hmerge&_merge_spec).
  unfold mergesort_spec; intros l ?.
  pure_rec l (@wf_list_length Z).
  eapply pure_eval_match. { pure_path. reflexivity. }
  unfold __branches11.
  pure_match; abstract_env.
  { pure_const. done. } (* Branch: "[]"  *)
  { pure_data. auto. }  (* Branch: "[x]" *)

  (* Branch: "_" *)
  assert (exists m, length l = S (S m)) as [m Heql].
  { (* TODO: too difficult to acquire knowledge from not matching on
       previous branches *)
    destruct no_match0 as [|no_match0]; [congruence | ].
    destruct no_match0 as (?&tail&?&[?|?]); first contradiction; subst.
    destruct tail; [ contradiction | simpl; eauto with arith]. }
  { eapply pure_eval_let_pair.
    eapply pure_eval_app.
    (* Use knowledge that [split] ∈ [η] *)
    eapply pure_eval_path. simpl. rewrite Hsplit. pure_ret.
    pure_path.
    (* Use knowledge that [split] ⊨ [split_spec] *)
    eapply pure_consequence. { apply _split_spec. }
    intros [l1 l2] (Hl1 & Hl2 & Hperm); simpl in *.
    unfold mergesort_pre in HP;
      rewrite <- Hperm in HP; apply Forall_app in HP as [??].
    eapply pure_eval_let.
    { eapply pure_eval_app. pure_path. pure_path.
      (* Use the induction hypothesis on [l1] *)
      apply IH.
      { (* Subgoal: show that [l1] ⊨ [mergesort_pre] *)
        assumption. }
      { (* Subgoal: show [length l1 < length l ] *)
        rewrite Heql; rewrite Heql in Hl1. by apply div2_lt_succ. } }
    intros l1' IHl1'.
    eapply pure_eval_let.
    { eapply pure_eval_app. pure_path. pure_path.
      (* Use the induction hypothesis on [l2] *)
      apply IH.
      { (* Subgoal: show that [l2] ⊨ [mergesort_pre] *)
        assumption. }
      { (* Subgoal: show [length l2 < length l] *)
        rewrite Hl2 Heql. auto with arith. } }
    intros l2' IHl2'; clear IH Hl1 Hl2 Heql m.
    eapply pure_eval_app2_conseq.
    { (* Use the knowledge that [merge] ∈ [η] *)
      eapply pure_eval_path. simpl. rewrite Hmerge. by pure_ret. }
    { by pure_path. }
    { by pure_path. }
    (* Use the knowledge that [merge] ⊨ [_merge_spec] *)
    { apply _merge_spec.
      (* Show that [l1'], [l2'] ⊨ [merge_pre] *)
      unfold mergesort_pre, mergesort_post in *.
      repeat (destruct_hyp).
      split; [ by rewrite_permutation l1'
             | split; [ by rewrite_permutation l2' | auto] ]. }
    intros l' IH.
    (* Subgoal: show that [l'] ⊨ [mergesort_post] *)
    unfold mergesort_post, merge_post in *.
    repeat (destruct_hyp).
    split; [ assumption | ].
    rewrite_permutation l'. rewrite_permutation l.
    rewrite_permutation l1'. rewrite_permutation l2'.
    reflexivity. }
Qed.

(* We use the [toplevel] judgement to specify the module
   created by the whole [merge.ml] file.

   [env_has_pspecs] takes an association list of names and
   specifications. It returns the conjunction of each specification
   applied to the lookup of its corresponding name. *)

Lemma Module__spec' :
  toplevel __main
    (env_has_pspecs [("merge", merge_spec);
                     ("split", split_spec);
                     ("merge_sort", mergesort_spec)]).
Proof.
  apply module_struct.
  eapply structs_cons.
  (* Evaluate "merge" letrec *)
  { eapply struct_letrec_single. apply Merge_spec'. }
  intros [??] (merge & Hmerge & -> & ->).
  eapply structs_cons.
  (* Evaluate "split" letrec *)
  { eapply struct_letrec_single. apply Split_spec'. }
  intros [??] (split & Hsplit & -> & ->).
  eapply structs_cons.
  (* Evaluate "merge_sort" letrec *)
  { eapply struct_letrec_single. apply MergeSort_spec'; eauto. }
  intros [??] (mergesort & Hmergesort & -> & ->).
  (* We have now evaluated the whole struct. *)
  eapply structs_nil.
  (* Goal: Show that the resulting environment satisfies the spec. *)
  simpl. tauto.
Qed.
