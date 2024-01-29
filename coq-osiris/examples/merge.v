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

Transparent ret_concat.
Opaque encode.

Lemma pat_PVar2 η x v :
  pat η (PVar x) v (λ η', η' = (x ~> v; η)) False.
Proof.
  by apply pat_PVar.
Qed.

Ltac pat_PVar :=
  match goal with
  | |- pat _ (PVar _) _ _ _ =>
      (apply pat_PVar2 || eapply pat_PVar)
  end.

Lemma pats_PCons2 `{Encode A} η p ps v (x : A) vs φ' φ ψ1 ψ2 :
  v = #x ->
  pat η p v (φ' x) (ψ1 x) ->
  (forall η0, φ' x η0 -> pats η0 ps vs φ ψ2) ->
  pats η (p :: ps) (v :: vs) φ (ψ1 x \/ ψ2).
Proof.
  intro. apply pats_PCons.
Qed.

Lemma pat_PPair `{Encode A, Encode B} η p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
  v1 = #x1 ->
  v2 = #x2 ->
  pat η p1 #x1 (λ η', pat η' p2 #x2 φ (ψ2)) (ψ1) ->
  pat η (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
Proof.
  intros; subst.
  apply pat_PTuple.
  eapply pats_PCons; eauto.
  intros. apply pats_PCons_single. auto.
Qed.

Ltac pat_PPair := eapply pat_PPair; [ solve [encode]
                                    | solve [encode]
                                    |].

Lemma elim_false_l P : (False \/ P) <-> P. Proof. tauto. Qed.
Lemma elim_false_r P : (P \/ False) <-> P. Proof. tauto. Qed.

Ltac cleanup_false_disj := rewrite !elim_false_l, !elim_false_r in *.

Lemma pure_eval_EOpLe_pure `{Encode A} η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ P, P <-> (x1 <= x2)%Z).
Proof.
  intros. destruct_pure a; destruct_pure b.
  subst.
  rewrite eval_eval'; simpl.
  eapply pure_simp.
  apply SimpPar; eauto. eapply pure_simp; [ apply SimpParRetRet | ].
  simpl.
  eapply pure_ret.
  { Transparent encode. unfold encode; unfold Encode_Prop. Opaque encode.
    f_equal. f_equal.
    rewrite lt_repr_repr; try assumption.
    rewrite truth_Is_true.
    reflexivity. }
  apply Zle_spec.
Qed.

Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (λ x1', x1' = x1) ->
  pure (eval η e2) (λ x2', x2' = x2) ->
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ b, (x1 <=? x2)%Z = b).
Proof.
  intros. destruct_pure a; destruct_pure b.
  subst.
  rewrite eval_eval'; simpl.
  eapply pure_simp.
  apply SimpPar; eauto. eapply pure_simp; [ apply SimpParRetRet | ].
  eapply pure_ret. Transparent encode. encode. Opaque encode.
  rewrite lt_repr_repr; try assumption.
  apply Z.leb_antisym.
Qed.

Lemma pure_eval_app2 `{Encode A, Encode B, Encode C} η e1 e2 e3 vf (arg1 : A) (arg2 : B) (ψ : C → Prop) :
  pure (eval η e1) (λ vf', vf' = vf) ->
  pure (eval η e2) (λ arg1', arg1' = arg1) ->
  pure (eval η e3) (λ arg2', arg2' = arg2) ->
  pure_call2 vf #arg1 #arg2 ψ ->
  pure (eval η (EApp (EApp e1 e2) e3)) ψ.
Proof.
  intros.
  destruct_pure v2; destruct_pure v1; destruct_pure vf'. subst.
  eapply pure_simp; [ simp | eauto ]. unfold pure_call2 in *.
  eapply pure_bind_unary with (A:=val).
  Transparent encode. simpl. Opaque encode.
  eassumption.
Qed.

Lemma pure_consequence2 `{Encode A} vf v1 v2 (φ ψ : A → Prop) :
  pure_call2 vf v1 v2 φ →
  (∀ a : A, φ a → ψ a) →
  pure_call2 vf v1 v2 ψ.
Proof.
  intros. unfold pure_call2 in *.
  eapply pure_consequence; first eassumption.
  simpl; intros.
  eapply pure_consequence; eauto.
Qed.

Lemma pure_eval_cons `{Encode A} η e (ψ : list A -> Prop) :
  pure (eval η e) (λ (p : (A * list A)),
      let '(h, t) := p in
      pure (ret (VData "::" (VPair #h #t))) ψ) ->
  pure (eval η (EData "::" e)) ψ.
Proof.
  intros.
  eapply pure_eval_data.
  destruct_pure p. destruct p.
  eapply pure_simp. apply H0.
  eapply pure_ret; eauto. by rewrite <- solve_encode_val.
Qed.

Ltac strip_disjunction :=
  match goal with
  | H : _ \/ _ |- _ =>
      destruct H as [ H | H ]; try contradiction
  end.
Ltac remove_tauto :=
  lazymatch goal with
  | H : ?x = ?x |- _ => clear H
  | _ => idtac
  end.
Ltac subst_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ => subst x
  | _ => idtac
  end.
Ltac inject_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ => injection H; repeat (intros ->)
  | _ => idtac
  end.
Ltac elim_exists :=
  lazymatch goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  end.
(* Goal: show that never matching is impossible *)
Ltac resolve_no_match :=
  repeat ((repeat strip_disjunction);
          (repeat elim_exists);
          (repeat destruct_hyp);
          try contradiction;
          remove_tauto;
          subst_eq;
          remove_tauto;
          inject_eq).

Lemma pure_eval_match2 `{Encode A, Encode B} η e bs (a : A) (φ : B -> Prop) :
  pure (eval η e) (λ x, x = a) →
  pure_match η #a bs φ →
  pure (eval η (EMatch e bs)) φ.
Proof.
  intros.
  eapply pure_eval_match; eauto.
  intros ? ->; assumption.
Qed.

Lemma Merge_spec' η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec. intros.
  pure_nested l1 l2 (@wf_double_list_length Z).
  eapply pure_eval_match2.
  { eapply pure_eval_pair. pure_path. pure_path. reflexivity. }
  unfold __branches2; simpl.
  (* First branch of match *)
  pure_match.
  { apply pat_POr.
    (* Match against "[], l" *)
    { pat_PPair. (* Todo: better rule for pure_eval_tuple? *)
      pat_pNil. intros ->.
      pat_PVar. simpl.
      (* Traverse expression after matching *)
      pure_path.
      (* Establish postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp).
      done. }
    (* Match against "l, []" *)
    { pat_PPair.
      pat_PVar. simpl.
      pat_pNil. intros ->.
      (* Traverse expression after matching *)
      pure_path.
      (* Establish postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp).
      by rewrite app_nil_r. } }
  intros no_match1.
  (* Second branch of match *)
  pure_match.
  { pat_PPair.
    pat_pCons; intros h1 t1 Heql1. { pat_PVar. }
    intros ? ->.
    pat_PVar. simpl.
    pat_pCons; intros h2 t2 Heql2. { pat_PVar. }
    intros ? ->.
    pat_PVar. simpl.
    (* Traverse expression after matching *)
    eapply pure_eval_ifthenelse.
    { (* Evaluate expression "h1 <= h2" *)
      unfold merge_pre in *.
      repeat (destruct_hyp); subst; repeat Forall_inversion.
      eapply pure_eval_EOpLe.
      { pure_path. reflexivity. }
      { pure_path. reflexivity. }
      { assumption. }
      { assumption. } }
    { (* Evaluate expression "h1 :: (merge t1 l2)" knowing h1 <= h2 *)
      simpl; intros. unfold __exp0. (* TODO: can we change pure_eval_data to make it usable? *)
      eapply pure_eval_cons. simpl.
      apply pure_eval_pair. pure_path.
      eapply pure_eval_app2.
      { pure_path. reflexivity. }
      { pure_path. reflexivity. }
      { pure_path. reflexivity. }
      unfold pure_call2.
      (* Use induction hypothesis on [call merge t1 l2] *)
      eapply pure_consequence2.
      { eapply IH; subst.
        { (* Subgoal: the partial application of merge returns a closure *)
          rewrite eval_eval'; simpl. reflexivity. }
        { (* Subgoal: t1 and l2 satisfy merge's precondition *)
          unfold merge_pre in *.
          repeat (destruct_hyp); all_inversions; auto. }
        { (* Subgoal: justify the recursive call with a size argument *)
          auto with arith. } }
      intros l Hpost.
      pure_ret.
      (* Establish the postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp); subst; all_inversions.
      split.
      { (* Subgoal: the output is sorted *)
        constructor; first done.
        eapply HdRel_Sorted_Permutation; eauto with zarith. }
      { (* Subgoal: the output is a permutation of the inputs *)
        by rewrite_permutation l. } }
    { (* Evaluate expression "h2 :: (merge l1 t2)" knowing ~ (h1 <= h2) *)
      simpl; intros. unfold __exp1.
      eapply pure_eval_cons. simpl.
      apply pure_eval_pair. pure_path.
      eapply pure_eval_app2.
      { pure_path. reflexivity. }
      { pure_path. reflexivity. }
      { pure_path. reflexivity. }
      (* Use induction hypothesis on [call merge l1 t2] *)
      eapply pure_consequence2.
      eapply IH; subst.
      { (* Subgoal: the partial application of merge returns a closure *)
        rewrite eval_eval'; simpl. reflexivity. }
      { (* Subgoal: l1 and t2 satisfy merge's precondition *)
        unfold merge_pre in *.
        repeat (destruct_hyp); all_inversions; auto. }
      { (* Subgoal: justify the recursive call with a size argument *)
        auto with arith. }
      intros l Hpost.
      pure_ret.
      (* Establish the postcondition *)
      unfold merge_post, merge_pre in *; repeat (destruct_hyp); subst; all_inversions.
      split.
      { (* Subgoal: the output is sorted *)
        constructor; first done.
        eapply HdRel_Sorted_Permutation; eauto with zarith. }
      { (* Subgoal: the output is a permutation of the inputs *)
        rewrite_permutation l.
        apply Permutation_sym. apply Permutation_middle. } } }
  intros no_match2.
  (* Goal: Show that not matching any of the branches is impossible *)
  resolve_no_match.
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
  pure_match.
  { (* Case: l matches [] *)
    pat_pNil. intros ->. (* We learn that l = [] *)
    (* Traverse the expression after a succesful match *)
    apply pure_eval_pair. pure_const. pure_const.
    (* Establish the (trivial) postcondition *)
    done. }
  (* Case: the first branch doesn't match, we learn that l ≠ [] *)
  intros no_match1.
  (* Second branch of match *)
  pure_match.
  { (* Case: l matches "cons x []" *)
    pat_pCons; intros h t Heql. (* We learn that l = h :: t *)
    { (* Match #h with "x" *) pat_PVar. }
    (* Match #t with "[]" *) simpl.
    intros ? ->. pat_pNil.
    intros ->. (* We now know t = [] *)
    (* Traverse the expression after a succesful match *)
    apply pure_eval_pair.
    apply pure_eval_data.
    apply pure_eval_pair_val. pure_path. pure_const.
    pure_ret.
    pure_const.
    (* Establish postcondition *)
    by rewrite Heql. }
  (* Case: we don't match the second branch,
     we learn that either l = [] or ∃ h t, l = h :: t and t ≠ [] *)
  simpl. intros no_match2.
  (* Third branch of match *)
  pure_match.
  { (* Match against "x1 :: x2 :: t" *)
    pat_pCons; intros x1 xs' Heql.
    { (* Match #x1 with "x1" *) pat_PVar. }
    simpl. intros ? ->. (* Match #xs' with "x2 :: t" *)
    pat_pCons; intros x2 xs Heqxs'.
    { (* Match #x2 with "xw" *) pat_PVar. }
    simpl. intros ? ->.
    (* Match #xs with "t" *)
    pat_PVar. simpl.
    (* Traverse the expression after a succesful match *)
    subst.
    eapply pure_eval_let_pair.
    eapply pure_eval_app. pure_path. pure_path.
    (* Call vf #xs *) simpl.
    eapply pure_consequence.
    { (* Use induction hypothesis *)
      apply IH; first done.
      (* Justify use of induction hypothesis *)
      eauto with arith. }
    intros [l1 l2] Hpost; clear IH; simpl.
    unfold __exp5.
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
    destruct Hpost as (H1 & H2 & ?).
    split; last split.
    { (* Subgoal: the length of l1 is half the length of xs *)
      destruct (Nat.even _); rewrite H1; eauto with arith. }
    { (* Subgoal: the length of l2 is half the length of xs *)
      rewrite H2; eauto with arith. }
    { (* Subgoal: l1++l2 is a permutation of xs *)
      rewrite_permutation xs.
      apply Permutation_skip.
      apply Permutation_sym.
      apply Permutation_middle. } }
  simpl; intros no_match3.
  resolve_no_match.
  (* TODO: Make automation more robust *)
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
  eapply pure_eval_match2. { pure_path. reflexivity. }
  unfold __branches11.
  pure_match.
  { pat_pNil. intros ->.
    (* Traverse expression after succesful match *)
    simpl; pure_const.
    done. }
  intros no_match1.
  pure_match.
  { pat_pCons; intros ?? Heql.
    { pat_PVar. }
    simpl; intros ? ->.
    pat_pNil. intros ->.
    (* Traverse expression after succesful match *)
    apply pure_eval_cons.
    apply pure_eval_pair. pure_path. pure_const. (* TODO: decoration fails here *)
    pure_ret.
    subst; auto. }
  intros no_match2. strip_disjunction.
  assert (exists m, length l = S (S m)) as [m Heql].
  { destruct no_match2 as (?&tail&?&[?|?]); first contradiction; subst.
    destruct tail; [ contradiction | simpl; eauto with arith]. }
  pure_match.
  { eapply pat_PAny.
    (* Traverse expression after succesful match *)
    eapply pure_eval_let_pair.
    eapply pure_eval_app.
    (* Use knowledge that [split] ∈ [η] *)
    eapply pure_eval_path. simpl. rewrite Hsplit. pure_ret.
    pure_path.
    (* Use knowledge that [split] ⊨ [split_spec] *)
    eapply pure_consequence. { apply _split_spec. }
    intros [l1 l2] (Hl1 & Hl2 & Hperm); simpl in *.
    unfold mergesort_pre in HP;
      rewrite <- Hperm in HP; apply Forall_app in HP as [??].
    unfold __exp10.
    eapply pure_eval_let.
    { eapply pure_eval_app. pure_path. pure_path.
      (* Use the induction hypothesis on [l1] *)
      apply IH.
      { (* Subgoal: show that [l1] ⊨ [mergesort_pre] *)
        assumption. }
      { (* Subgoal: show [length l1 < length l ] *)
        rewrite Heql in *. by apply div2_lt_succ. } }
    intros l1' IHl1'.
    unfold __exp9.
    eapply pure_eval_let.
    { eapply pure_eval_app. pure_path. pure_path.
      (* Use the induction hypothesis on [l2] *)
      apply IH.
      { (* Subgoal: show that [l2] ⊨ [mergesort_pre] *)
        assumption. }
      { (* Subgoal: show [length l2 < length l] *)
        rewrite Hl2, Heql. auto with arith. } }
    intros l2' IHl2'; clear IH Hl1 Hl2 Heql m.
    unfold __exp8.
    eapply pure_eval_app2.
    { (* Use the knowledge that [merge] ∈ [η] *)
      eapply pure_eval_path. simpl. rewrite Hmerge. by pure_ret. }
    { by pure_path. }
    { by pure_path. }
    (* Use the knowledge that [merge] ⊨ [_merge_spec] *)
    eapply pure_consequence2.
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
  (* Show that not matching on any of pattern matching branches is impossible *)
  intros no_match3.
  congruence. (* [resolve_no_match] still works *)
Qed.

Opaque ret_concat.
Transparent encode.

End PureProofs.

(* -------------------------------------------------------------------------- *)

(* Coq-Evaluation-Dependent Specification proofs. *)

Lemma Merge_spec η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec. intros l1 l2 ?.
  pure_nested l1 l2 (@wf_double_list_length Z).
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
    eapply pure_bind; first apply IH; auto with arith.
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
  eapply pure_bind; first apply IH.
  { (* Subgoal: show the precondition holds for l1 *)
    apply Hrep1. }
  { (* Subgoal: justify the induction by showing [length l1 < length a::b::l] *)
    by apply div2_lt_succ. }
  simpl; intros sl1 (Hsl1 & Hpsl1).
  pure_continue.
  (* Apply the induction hypothesis on l2*)
  eapply pure_bind; first apply IH.
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
