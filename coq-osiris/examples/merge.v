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
  ∀ A `(_ : Encode A) (l : list Z),
    mergesort_pre l ->
    pure
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
  pure_nested l1 l2  (@wf_double_list_length Z).
  unfold merge_pre in HP; repeat destruct_hyp.
  destruct l1 as [|h1 t1]; last destruct l2 as [|h2 t2]; intros.
  (* Case: l1 = [] *)
  { pure1; pure1; pure_continue.
    unfold merge_post; rewrite app_nil_l; auto. }
  (* Case: l2 = [] *)
  { pure1; pure1; pure_continue.
    unfold merge_post; rewrite app_nil_r; auto. }
  (* Case: l1 = h1::t1, l2 = h2::t2 *)
  all_inversions. pure1. pure_continue.
  (* TODO: Environments are too present in the goal *)
  rewrite lt_repr_repr by auto.
  (* Reason by cases on the comparison of the heads *)
  destruct (h2 <? h1) eqn:branch; simpl.
  { (* Case: h2 < h1 *) Transparent app. simpl.
    pure_execute.
    (* Use the induction hypothesis on [call merge (h1::t1) t2] *) 
    eapply pure_bind_binary.
    { apply (IH (h1::t1) t2).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: (h1::t1) and t2 satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(h1::t1, t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. } }
    unfold merge_post; cbn; intros l' (? & ?).
    (* Establish the postcondition *)
    eapply pure_ret; first solve [encode]. split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply (HdRel_Sorted_Permutation l' (h1 :: t1) t2); eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      rewrite_permutation l'.
      apply Permutation_sym.
      change (h1 :: t1 ++ t2) with ((h1 :: t1) ++ t2).
      apply Permutation_middle. }}
  { (* Case: h1 < h2 *)
    pure_execute.
    (* Use the induction hypothesis on [call merge t1 (h2::t2)] *)
    eapply pure_bind_binary.
    { apply (IH t1 (h2::t2)).
      (* Subgoal: the partial application of merge returns a closure *)
      { rewrite eval_eval'; reflexivity. }
      (* Subgoal: t1 and (h2::t2) satisfy the merge's precondition *)
      { unfold merge_pre; auto. }
      (* Subgoal: justify the induction: show [(t1, h2::t2) < (h1::t1, h2::t2)] *)
      { simpl; auto with arith. } }
    unfold merge_post; cbn; intros l' (? & ?).
    (* Establish the postcondition *)
    eapply pure_ret; first solve [encode]. split.
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
  pure_rec l (@wf_list_length A).
  destruct l as [| a l]; last destruct l as [| b l]; pure_execute.
  (* Case: [] *)
  { by simpl. }
  (* Case: [a] *)
  { by simpl. }
  (* Case: a::b::l *)
  { (* Apply the induction hypothesis *)
    eapply pure_try; first apply IH; auto with arith.
    intros [l1 l2] (Hl1&Hl2&Hperm).
    pure_execute.
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

Transparent ret_concat.

Lemma pat_pNil2`{Encode A} η v (xs : list A) (φ : env -> Prop) :
  v = #xs →
  φ η →
  pat η pNil v (λ η', xs = [] /\ φ η') (xs ≠ []).
Proof.
  intros; subst.
  eapply pat_consequence with (φ:=fun η' => xs = [] /\ φ η');
    eauto using pat_pNil.
Qed.

Lemma pat_pCons2 `{Encode A} v xs η η' p1 p2 (φ : env -> Prop) (ψ : Prop) ψ1 ψ2 :
  v = #xs ->
  (∀ (x : A) (xs' : list A),
      xs = x :: xs' →
      pat η p1 #x (λ η0, η0 = (η' x xs')) (ψ1 x xs')) ->
  (∀ (x : A) (xs' : list A),
      xs = x :: xs' →
      pat (η' x xs') p2 #xs' φ (ψ2 x xs')) ->
  ((exists x xs', xs = x :: xs' /\ (ψ1 x xs' \/ ψ2 x xs')) ∨ xs = [] → ψ) ->
  pat η (pCons p1 p2) v φ ψ.
Proof.
  intros ? Hpat Hpats; subst.
  destruct xs as [| x xs ]; eapply pat_consequence_psi.
  { eapply pat_consequence_psi.
    - eapply pat_PData_neq; eauto.
    - by right. }
  { specialize (Hpat x xs eq_refl).
    specialize (Hpats x xs eq_refl).
    eapply pat_PData_eq.
    rewrite ?encode_list_is_encode. (* optional, but helpful *)
    eapply pat_PTuple.
    eapply pats_consequence_psi.
    eapply pats_PCons.
    { eauto. }
    { intros ? ->. apply pats_PCons_single.
      eapply pat_consequence; eauto. }
    intros Hψ. left. exists x, xs. destruct Hψ; eauto. }
Qed.

Lemma pats_PCons2 η p ps v vs φ' φ ψ1 ψ2 :
  pat η p v φ' ψ1 →
  (forall η', φ' η' -> pats η' ps vs φ ψ2) →
  pats η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
Proof.
  intros. eapply pats_PCons; eauto.
Qed.

Lemma pats_PCons_var η x ps vs v φ ψ :
  pats ((x, v) :: η) ps vs φ ψ →
  pats η (PVar x :: ps) (v :: vs) φ (ψ).
Proof.
  intros.
  eapply pats_consequence_psi.
  eapply pats_PCons.
  - apply pat_PVar. apply eq_refl.
  - by intros ? <-.
  - tauto.
Qed.

Lemma Split_spec' η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec. intros.
  pure_rec l (@wf_list_length A).
  (* Goal: eval match on l *)
  eapply pure_eval_match. { pure_path. apply eq_refl. }
  intros ? <-. unfold __branches6; simpl.
  (* First branch of match *)
  eapply pure_match_cons.
  { (* Match against "[]" *)
    eapply pat_pNil; first solve [encode].
    intros Heql. (* We now know that l = [] *)
    (* Traverse the expression after a succesful match *)
    apply pure_eval_pair. pure_const. pure_const.
    (* Establish the (trivial) postcondition *)
    by rewrite Heql. }
  (* Case: we don't match the first branch, we now know that l ≠ [] *)
  intros l_neq_nil.
  (* Second branch of match *)
  eapply pure_match_cons.
  { (* Match against "x :: []" *)
    eapply pat_pCons2; eauto; intros h t Heql.
    (* Match #h with "x" *)
    { apply pat_PVar. apply eq_refl. }
    (* Match #t with "[]" *)
    simpl. eapply pat_pNil; eauto.
    intros ->. (* We now know t = [] *)
    (* Traverse the expression after a succesful match *)
    apply pure_eval_pair.
    apply pure_eval_data.
    apply pure_eval_pair_val. pure_path. pure_const.
    pure_ret.
    pure_const.
    (* Establish postcondition *)
    by rewrite Heql. }
  (* Case: we don't match the first or second branch, we know that
     ∃ h t, l = h :: t and t ≠ [] *)
  simpl.
  intros [ (h & t & Heql & tneq) | ?]; last contradiction.
  destruct tneq as [ ? | tneq ]; first contradiction.
  (* Third branch of match *)
  eapply pure_match_cons.
  { (* Match against "x1 :: x2 :: t" *)
    eapply pat_pCons2 with (ψ2 := fun _ _ => False); eauto; intros x1 xs' Heql2.
    { (* Match #x1 with "x1" *) 
      apply pat_PVar. apply eq_refl. }
    simpl. (* Match #xs' with "x2 :: t" *)
    eapply pat_pCons2; eauto; try intros x2 xs Heqxs'.
    { (* Match #x2 with "xw" *)
      apply pat_PVar. apply eq_refl. }
    { simpl. (* Match #xs with "t" *)
      apply pat_PVar. simpl.
      (* Traverse the expression after a succesful match *)
      eapply pure_eval_let_pair.
      eapply pure_eval_app. pure_path. pure_path.
      (* Call vf #xs *)
      eapply pure_consequence.
      { (* Use induction hypothesis *)
        apply IH; first done.
        rewrite Heql2, Heqxs'.
        eauto with arith. }
      intros [l1 l2] Hpost; clear IH; simpl.
      unfold __exp5; simpl.
      (* Eval (x1::l1, x2::l2) *)
      apply pure_eval_pair.
      (* Eval x1::l1 *)
      apply pure_eval_data.
      apply pure_eval_pair_val. pure_path. pure_path. pure_ret.
      (* Eval x2::l2 *)
      apply pure_eval_data.
      apply pure_eval_pair_val. pure_path. pure_path. pure_ret.
      (* Establish postcondition *)
      unfold split_post in *; simpl in *.
      rewrite Heql2, Heqxs'.
      repeat destruct_hyp.
      split; last split.
      { (* Subgoal: the length of l1 is half the length of xs *)
        destruct (Nat.even _); rewrite H0; eauto with arith. }
      { (* Subgoal: the length of l2 is half the length of xs *)
        rewrite H1.
        eauto with arith. }
      { (* Subgoal: l1++l2 is a permutation of xs *)
        rewrite_permutation xs.
        apply Permutation_skip.
        apply Permutation_sym.
        apply Permutation_middle. } }
    simpl.
    subst l. injection Heql2; intros -> ->; clear Heql2.
    intros [ Hf | ? ]; exfalso; last contradiction.
    destruct Hf as (? & ? & Heqht & Hf).
    destruct Hf as [ Hf | ? ]; contradiction. }
  simpl. intros [ Hf | ? ]; exfalso; last contradiction.
  repeat destruct Hf as [? Hf]; tauto.
Qed.

Opaque ret_concat.

Lemma MergeSort_spec η :
  (exists split, lookup_name η "split" = ret split /\ split_spec split) ->
  (exists merge, lookup_name η "merge" = ret merge /\ merge_spec merge) ->
  mergesort_spec (VCloRec η __bindings12 "merge_sort").
Proof.
  (* Destruct the hypotheses on split and merge *)
  destruct 1 as (split&Hsplit&_split_spec).
  destruct 1 as (merge&Hmerge&_merge_spec).
  unfold mergesort_spec; intros ?? l ?.
  pure_rec l (@wf_list_length Z).
  destruct l as [|a l]; last destruct l as [|b l]; pure_execute.
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
  pure_continue.
  (* Apply the induction hypothesis on l1 *)
  eapply pure_try; first apply IH.
  { (* Subgoal: show the precondition holds for l1 *)
    apply Hrep1. }
  { (* Subgoal: justify the induction by showing [length l1 < length a::b::l] *)
    by apply div2_lt_succ. }
  simpl; intros sl1 (Hsl1 & Hpsl1).
  pure_continue.
  (* Apply the induction hypothesis on l2*)
  eapply pure_try; first apply IH.
  { (* Subgoal: show the precondition holds for l2 *)
    apply Hrep2. }
  { (* Subgoal: justify the induction by showing [length l2 < length a::b::l] *)
    rewrite Hl2; eauto with arith. }
  simpl; intros sl2 (Hsl2 & Hpsl2).
  pure_continue.
  eapply pure_bind.
  (* Use the fact that [merge] satisfies its specification *)
  { eapply _merge_spec with (l2:=sl2); unfold merge_pre; eauto.
    split; last split; auto.
    { (* Subgoal: show merge's precondition that l1 is representable *)
      by rewrite_permutation sl1. }
    { (* Subgoal: show merge's precondition that l2 is representable *)
      by rewrite_permutation sl2. }}
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
  let η := ("Stdlib", Stdlib) :: Stdlib_env in
  pure (eval_mexpr η __main)
    (is_module_with_pspecs [("merge", merge_spec);
                        ("split", split_spec);
                        ("merge_sort", mergesort_spec)]).
Proof.
  intros.
  pure1.
  pure_specify "merge" merge_spec.
  { apply Merge_spec. } intros merge _spec1.
  pure_continue.
  pure_specify "split" split_spec.
  { apply Split_spec. } intros split _spec2.
  pure_continue.
  pure_specify "merge_sort" mergesort_spec.
  { apply MergeSort_spec; eauto. } intros mergesort _spec3.
  repeat pure_continue.
  (* Postcondition *)
  simpl. auto.
Qed.
