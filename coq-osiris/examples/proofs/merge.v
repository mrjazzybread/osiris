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

Section PureProofs.

Opaque encode.

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

Transparent encode.

End PureProofs.

(* -------------------------------------------------------------------------- *)

(* Coq-Evaluation-Dependent Specification proofs. *)

Local Transparent eval_mexpr eval_bindings evals extend encode.

Lemma Merge_spec η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec. intros l1 l2 ?.
  pure_nested l1 l2 (@wf_double_list_length Z).
  unfold merge_pre in HP; repeat destruct_hyp.
  destruct l1 as [|h1 t1]; last destruct l2 as [|h2 t2]; intros.
  (* Case: l1 = [] *)
  { pure1; pure1.
    unfold merge_post; rewrite app_nil_l; auto. }
  (* Case: l2 = [] *)
  { pure1; pure1.
    unfold merge_post; rewrite app_nil_r; auto. }
  (* Case: l1 = h1::t1, l2 = h2::t2 *)
  all_inversions. pure1.
  (* TODO: Environments are too present in the goal *)
  rewrite lt_repr_repr; auto.
  (* Reason by cases on the comparison of the heads *)
  destruct (h2 <? h1)%Z eqn:branch; simpl.
  { (* Case: h2 < h1 *)
    repeat (rewrite eval_eval'; simpl).
    pure1.
    (* Use the induction hypothesis on [call merge (h1::t1) t2] *)
    eapply pure_try.
    { eapply pure_consequence. apply (IH (h1::t1) t2).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: (h1::t1) and t2 satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(h1::t1, t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. }
      intro; simpl; intros. apply H. }
    unfold merge_post; cbn; intros l' (? & ?).
    repeat destruct_hyp. pure1.
    (* Establish the postcondition *)
    split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply (HdRel_Sorted_Permutation x (h1 :: t1) t2); eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      rewrite_permutation x.
      apply Permutation_sym.
      change (h1 :: t1 ++ t2) with ((h1 :: t1) ++ t2).
      apply Permutation_middle. }}
  { (* Case: h1 < h2 *)
    pure1. rewrite bind_try.
    (* Use the induction hypothesis on [call merge t1 (h2::t2)] *)
    eapply pure_try.
    { apply (IH t1 (h2::t2)).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: t1 and (h2::t2) satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(t1, h2::t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. } }
    unfold merge_post; cbn; intros l' (? & ?).
    repeat destruct_hyp. pure1.
    (* Establish the postcondition *)
    split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      by rewrite_permutation x. }}
Qed.

Lemma Split_spec η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec. intros.
  pure_rec l (@wf_list_length A).
  destruct l as [| a l]; last destruct l as [| b l]; pure1.
  (* Case: [] *)
  { by simpl. }
  (* Case: [a] *)
  { by simpl. }
  (* Case: a::b::l *)
  { (* Apply the induction hypothesis *)
    repeat (rewrite eval_eval'; simpl); pure1; cbn.
    pure1.
    eapply pure_try. { apply IH; auto with arith. }
    intros [l1 l2] (Hl1&Hl2&Hperm).
    pure1.
    (* Establish the three conjuncts of the postcondition *)
    unfold split_post; simpl in *; split; last split.
    { (* Subgoal: the length of l1 is half the length of l *)
      destruct (Nat.even _); eauto with arith. }
    { (* Subgoal: the length of l2 is hald the length of l *)
      eauto with arith. }
    { (* Subgoal: l1++l2 is a permutation of l *)
      rewrite_permutation l.
      change ((a::l1)++b::l2) with (a::l1++b::l2).
      apply Permutation_skip.
      apply Permutation_sym.
      apply Permutation_middle. }}
Qed.

Lemma MergeSort_spec η :
  (exists split, lookup_name η "split" = ret split /\ split_spec split) ->
  (exists merge, lookup_name η "merge" = ret merge /\ merge_spec merge) ->
  mergesort_spec (VCloRec η __bindings12 "merge_sort").
Proof.
  (* Destruct the hypotheses on split and merge *)
  destruct 1 as (split&Hsplit&_split_spec).
  destruct 1 as (merge&Hmerge&_merge_spec).
  unfold mergesort_spec; intros l ?.
  pure_rec l (@wf_list_length Z).
  destruct l as [|a l]; last destruct l as [|b l]; pure1.
  (* Case: [] *)
  { auto. }
  (* Case: [a] *)
  { auto. }
  (* Case: a::b::l *)
  repeat (rewrite eval_eval'; simpl); pure1; cbn.
  pure1. rewrite Hsplit. cbn.
  eapply pure_try. { pure_call. }
  unfold split_post; intros [l1 l2]; simpl; intros (Hl1 & Hl2 & Hperm).
  (* Assert that the sublists l1 and l2 satisfy the precondition *)
  assert (Forall representable l1) as Hrep1 by
      (apply Forall_app with (l1:=l1) (l2:=l2); by rewrite_permutation (l1++l2)).
  assert (Forall representable l2) as Hrep2 by
      (apply Forall_app with (l1:=l1) (l2:=l2); by rewrite_permutation (l1++l2)).
  cbn.
  pure1.
  (* Apply the induction hypothesis on l1 *)
  eapply pure_try; first apply IH.
  { (* Subgoal: show the precondition holds for l1 *)
    apply Hrep1. }
  { (* Subgoal: justify the induction by showing [length l1 < length a::b::l] *)
    by apply div2_lt_succ. }
  simpl; intros sl1 (Hsl1 & Hpsl1).
  pure1.
  (* Apply the induction hypothesis on l2*)
  eapply pure_try; first apply IH.
  { (* Subgoal: show the precondition holds for l2 *)
    apply Hrep2. }
  { (* Subgoal: justify the induction by showing [length l2 < length a::b::l] *)
    rewrite Hl2; eauto with arith. }
  simpl; intros sl2 (Hsl2 & Hpsl2).
  pure1.
  eapply pure_bind.
  { rewrite Hmerge; cbn.
    eapply pure_ret; [ rewrite <- solve_encode_val; reflexivity | ].
    apply eq_refl. }
  intros ? <-.
  eapply pure_try.
  (* Use the fact that [merge] satisfies its specification *)
  { eapply _merge_spec with (l2 := sl2).
    unfold merge_pre;
      split; last split; auto.
    - (* Subgoal: show merge's precondition that l1 is representable *)
      by rewrite_permutation sl1.
    - (* Subgoal: show merge's precondition that l2 is representable *)
      by rewrite_permutation sl2. }
  intros c; simpl; intros Hc.
  eapply pure_consequence; first apply Hc.
  intros l' [??].
  (* Establish the postcondition *)
  split.
  { (* Subgoal: the output is sorted *)
    assumption. }
  { (* Subgoal: the output is a permutation of the input *)
    rewrite_permutation l'.
    rewrite_permutation sl1.
    by rewrite_permutation sl2. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Main module specification. *)

Lemma Merge__spec:
  pure (eval_mexpr stdlib_env __main)
    (is_module_with_pspecs [("merge", merge_spec);
                            ("split", split_spec);
                            ("merge_sort", mergesort_spec)]).
Proof.
  intros. simpl. pure_ret. simpl.
  (* split; last split. *)
  (* { apply Merge_spec. } *)
  (* { apply Split_spec. } *)
  (* { apply MergeSort_spec. *)
  (*   - eauto using Split_spec. *)
  (*   - eauto using Merge_spec. } *)
  eauto 9 using MergeSort_spec, Split_spec, Merge_spec.
Qed.
