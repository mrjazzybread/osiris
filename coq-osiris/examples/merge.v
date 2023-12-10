Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.logic Require Import sorting.
From osiris.examples Require Import og_merge.
Local Opaque app. (* Prevent undesired simplification. *)


Notation "'<(' f ')>'" := (VCloRec _ _ f) (only printing).
Notation "'<' f '>'" := (VClo _ f) (only printing).
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (EnvCons x _ (.. (EnvCons z _ EnvNil) ..))
 (only printing).

(* -------------------------------------------------------------------------- *)

(* WIP: Tactics used in local proof scripts. *)
  
Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac rewrite_permutation t :=
  lazymatch goal with
  | H : t ≡ₚ _ |- _ => rewrite H || (revert H; rewrite_permutation t)
  | H : _ ≡ₚ t |- _ => rewrite <- H || (revert H; rewrite_permutation t)
  end.

Ltac Sorted_inversion :=
  match goal with
  | H : Sorted _ (_ :: _) |- _ =>
      apply Sorted_inv in H as [H?]
  end.

Ltac HdRel_inversion :=
  lazymatch goal with
  | H : HdRel _ _ (_ :: _) |- _ =>
      apply HdRel_inv in H as H
  end.

Ltac Forall_inversion :=
  match goal with
  | H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H
  end.

Ltac all_inversions :=
  repeat (Sorted_inversion || (HdRel_inversion || Forall_inversion)).

(* -------------------------------------------------------------------------- *)

(* Helper Lemmas. *)

(* We implicitly use the following lemma when we prove that the list returned
   by [split l] are smaller than l *)

Lemma suc_div2_lt_suc n :
    (Nat.div2 n < S n)%nat.
Proof.
 destruct (Nat.even n) eqn:Hn.
 { rewrite Nat.Even_div2; last by apply Nat.even_spec.
   apply Nat.lt_div2; lia. }
 { apply Nat.succ_lt_mono.
   rewrite <- Nat.negb_odd in Hn.
   apply negb_false_iff in Hn.
   rewrite Nat.Odd_div2; last by apply Nat.odd_spec.
   auto with arith. }
Qed.

Local Hint Resolve suc_div2_lt_suc : arith.

Lemma even_false_odd_true n : Nat.even n = false <-> Nat.odd n = true.
Proof.
  split; intros;
    [rewrite <- Nat.negb_even | rewrite <- Nat.negb_odd];
    [by apply negb_true_iff   | by apply negb_false_iff].
Qed.

Local Hint Resolve even_false_odd_true : arith.

Lemma div2_lt_succ n m :
  (if Nat.even m
   then n = S (Nat.div2 m)
   else n = S (S (Nat.div2 m))) ->
  (n < S (S m))%nat.
Proof.
  intros Hn.
  destruct (Nat.even m) eqn:Hm; rewrite Hn.
  { auto with arith. }
  apply even_false_odd_true in Hm.
  rewrite Nat.Odd_div2; last by apply Nat.odd_spec.
  auto with arith.
Qed.

(* Make a library of commonly used well founded relations? *) 

Lemma wf_list_length {A : Type} :
  well_founded (fun (l1 l2 : list A) => (length l1 < length l2)%nat).
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
  ∀ A `(_ : Encode A) (l1 l2 : list Z),
    merge_pre l1 l2 ->
    SIMP
      (call merge #l1)
      (fun c =>
         SIMP (call c #l2) (merge_post l1 l2)).


(* Specification for [split l]. *)

Local Definition split_post {A} :=
  (fun (l : list A) p => (if Nat.even (length l)
            then length p.1 = Nat.div2 (length l)
            else length p.1 = S (Nat.div2 (length l)))
           /\ length p.2 = Nat.div2 (length l) /\ Permutation (p.1 ++ p.2) l).

Definition split_spec (split : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list A),
    SIMP
      (call split #l)
      (split_post l).


(* Specification for [mergesort l]. *)

Local Definition mergesort_pre := (fun l => Forall representable l).
Local Definition mergesort_post := (fun l l' => Sorted Z.le l' /\ Permutation l' l).
Local Hint Unfold mergesort_post : core.
Local Hint Unfold mergesort_pre : core.

Definition mergesort_spec (mergesort : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list Z),
    mergesort_pre l ->
    SIMP
      (call mergesort #l)
      (mergesort_post l).

(* -------------------------------------------------------------------------- *)

(* Specification proofs. *)

Lemma wf_double_list_length {A B} :
  well_founded (fun (p1 p2 : list A * list B) =>
                  (length p1.1 + length p1.2 < length p2.1 + length p2.2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

Lemma Merge_spec η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec. intros ?? l1 l2 ?.
  SIMP_nested l1 l2  (@wf_double_list_length Z).
  unfold merge_pre in HP; repeat destruct_hyp.
  destruct l1 as [|h1 t1]; last destruct l2 as [|h2 t2]; intros.
  (* Case: l1 = [] *)
  { SIMP1; SIMP1; SIMP_continue.
    unfold merge_post; rewrite app_nil_l; auto. }
  (* Case: l2 = [] *)
  { SIMP1; SIMP1; SIMP_continue.
    unfold merge_post; rewrite app_nil_r; auto. }
  (* Case: l1 = h1::t1, l2 = h2::t2 *)
  all_inversions. SIMP1. SIMP_continue.
  rewrite lt_repr_repr by auto.
  (* Reason by cases on the comparison of the heads *)
  destruct (h2 <? h1) eqn:branch; simpl.
  { (* Case: h2 < h1 *)
    SIMP_execute.
    (* Use the induction hypothesis on [call merge (h1::t1) t2] *)
    eapply SIMP_bind_binary.
    { apply (IH (h1::t1) t2).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: (h1::t1) and t2 satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(h1::t1, t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. } }
    unfold merge_post; cbn; intros l' (? & ?).
    (* Establish the postcondition *)
    eapply SIMP_ret; first solve [encode]. split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      rewrite_permutation l'. apply Permutation_sym; apply Permutation_middle. }}
  { (* Case: h1 < h2 *)
    SIMP_execute.
    (* Use the induction hypothesis on [call merge t1 (h2::t2)] *)
    eapply SIMP_bind_binary.
    { apply (IH t1 (h2::t2)).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: t1 and (h2::t2) satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(t1, h2::t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. } }
    unfold merge_post; cbn; intros l' (? & ?).
    (* Establish the postcondition *)
    eapply SIMP_ret; first solve [encode]. split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      by rewrite_permutation l'. }}
Qed.

Lemma Split_spec η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec. intros.
  SIMP_rec l (@wf_list_length A).
  destruct l as [| a l]; last destruct l as [| b l]; SIMP_execute.
  (* Case: [] *)
  { by simpl. }
  (* Case: [a] *)
  { by simpl. }
  (* Case: a::b::l *)
  { (* Apply the induction hypothesis *)
    eapply SIMP_try; first apply IH; auto with arith.
    intros [l1 l2] (Hl1&Hl2&Hperm).
    SIMP_execute.
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
  unfold mergesort_spec; intros ?? l ?.
  SIMP_rec l (@wf_list_length Z).
  destruct l as [|a l]; last destruct l as [|b l]; SIMP_execute.
  (* Case: [] *)
  { auto. }
  (* Case: [a] *)
  { auto. }
  (* Case: a::b::l *)
  unfold split_post; intros [l1 l2]; simpl; intros (Hl1 & Hl2 & Hperm).
  (* Assert that the sublists l1 and l2 satisfy the precondition *)
  assert (Forall representable l1) as Hrep1 by
      (apply Forall_app with (l1:=l1) (l2:=l2); by rewrite_permutation (l1++l2)).
  assert (Forall representable l2) as Hrep2 by
        (apply Forall_app with (l1:=l1) (l2:=l2); by rewrite_permutation (l1++l2)).  
  SIMP_continue.
  (* Apply the induction hypothesis on l1 *)
  eapply SIMP_try; first apply IH.
  { (* Subgoal: show the precondition holds for l1 *)
    apply Hrep1. }
  { (* Subgoal: justify the induction by showing [length l1 < length a::b::l] *)
    by apply div2_lt_succ. }
  simpl; intros sl1 (Hsl1 & Hpsl1).
  SIMP_continue.
  (* Apply the induction hypothesis on l2*)
  eapply SIMP_try; first apply IH.
  { (* Subgoal: show the precondition holds for l2 *)
    apply Hrep2. }
  { (* Subgoal: justify the induction by showing [length l2 < length a::b::l] *)
    rewrite Hl2; eauto with arith. }
  simpl; intros sl2 (Hsl2 & Hpsl2).
  SIMP_continue.
  eapply SIMP_bind.
  (* Use the fact that [merge] satisfies its specification *)
  { eapply _merge_spec with (l2:=sl2); unfold merge_pre; eauto.
    split; last split; auto.
    { (* Subgoal: show merge's precondition that l1 is representable *)
      by rewrite_permutation sl1. }
    { (* Subgoal: show merge's precondition that l2 is representable *)
      by rewrite_permutation sl2. }}
  intros c; simpl; intros Hc.
  eapply SIMP_covariant; first apply Hc.
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
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  SIMP (eval_mexpr η __main)
    (is_module_with_pspecs [("merge", merge_spec);
                        ("split", split_spec);
                        ("merge_sort", mergesort_spec)]).
Proof.
  intros.
  SIMP1.
  SIMP_specify "merge" merge_spec.
  { apply Merge_spec. } intros merge _spec1.
  SIMP_continue.
  SIMP_specify "split" split_spec.
  { apply Split_spec. } intros split _spec2.
  SIMP_continue.
  SIMP_specify "merge_sort" mergesort_spec.
  { apply MergeSort_spec; eauto. } intros mergesort _spec3.
  repeat SIMP_continue.
  (* Postcondition *)
  simpl. auto.
Qed.
