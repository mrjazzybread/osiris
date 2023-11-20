Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_merge.
Local Opaque app. (* Prevent undesired simplification. *)


Notation "'<(' f ')>'" := (VCloRec _ _ f) (only printing).
Notation "'<' f '>'" := (VClo _ f) (only printing).
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (EnvCons x _ (.. (EnvCons z _ EnvNil) ..))
 (only printing).

(* -------------------------------------------------------------------------- *)

(* WIP: Tactics used in local proof scripts. *)

Ltac SimpParRetNext :=
  (apply SimpParRetLeftNext || apply SimpParRetRightNext).

Ltac SimpParRet :=
  (SimpParRetNext || (apply SimpParRetLeft || apply SimpParRetRight)).

Ltac SIMP_Par_Ret :=
  repeat (eapply SIMP_simp; [SimpParRet|]; simpl).
  
Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac rewrite_permutation t :=
  lazymatch goal with
  | H : t ≡ₚ _ |- _ => rewrite H || (revert H; rewrite_permutation t)
  | H : _ ≡ₚ t |- _ => rewrite <- H || (revert H; rewrite_permutation t)
  end.

Ltac unfold_breakpoint1 :=
  match goal with
  | |- simp ?m _ => unfold_breakpoint m
  | _ => fail "Not at breakpoint"
  end.

Ltac simp_evaluate :=
  simpl; repeat (rewrite eval_eval'; simpl).

Ltac SIMP_evaluate :=
  eapply SIMP_simp; [simp_evaluate; apply SimpReflexive|].

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

Lemma HdRel_trans A (cmp : A -> A -> Prop) `{Transitive A cmp} l x y :
  cmp x y -> HdRel cmp y l -> HdRel cmp x l.
Proof.
  intros.
  destruct l; first done.
  apply HdRel_cons. HdRel_inversion.
  by transitivity y.
Qed.

(* If a list is sorted, then being smaller than the head is equivalent to 
   being smaller than all elements of the list. *)

Lemma Sorted_Hd_cmp A x (l : list A) (cmp : A -> A -> Prop) `{Transitive A cmp}:
  Sorted cmp l ->
  HdRel cmp x l <-> Forall (cmp x) l.
Proof.
  intros.
  induction l.
  { split; constructor. }
  { split; first last.
    - constructor; by Forall_inversion.
    - intros; all_inversions.
      constructor; first assumption.
      apply IHl; first assumption.
      eapply HdRel_trans; eauto. }
Qed.

(* Let l be a sorted list, let l1 and l2 be two sorted lists partinioning l.
   An arbitrary x is smaller that the head of l if it is smaller than the head
   of l1 and the head of l2 *)

Lemma HdRel_Sorted_Permutation {A} (cmp : A -> A -> Prop) `{Transitive A cmp} l l1 l2 x :
  Sorted cmp l ->
  l1 ++ l2 ≡ₚ l ->
  Sorted cmp l1 -> Sorted cmp l2 ->
  HdRel cmp x l1 -> HdRel cmp x l2 ->
  HdRel cmp x l.
Proof.
  intros.
  apply Sorted_Hd_cmp; try auto.
  rewrite_permutation l.
  apply Forall_app.
  split; apply Sorted_Hd_cmp; auto.
Qed.

Lemma suc_div2_lt_suc n :
    (S (Nat.div2 n) < S (S n))%nat.
Proof.
 destruct (Nat.even n) eqn:Hn.
 { rewrite Nat.Even_div2; last by apply Nat.even_spec.
   apply -> Nat.succ_lt_mono.
   apply Nat.lt_div2; lia. }
 { rewrite <- Nat.negb_odd in Hn.
   apply negb_false_iff in Hn.
   rewrite Nat.Odd_div2; last by apply Nat.odd_spec.
   apply Nat.lt_succ_r.
   eapply Nat.le_trans. { apply Nat.le_div2. }
   apply Nat.le_succ_diag_r. }
Qed.

Lemma even_false_odd_true n : Nat.even n = false <-> Nat.odd n = true.
Proof.
  split; intros;
    [rewrite <- Nat.negb_even | rewrite <- Nat.negb_odd];
    [by apply negb_true_iff   | by apply negb_false_iff].
Qed.

(* -------------------------------------------------------------------------- *)

(* Specifications for [merge_sort]. *)

Definition merge_spec (merge : val) : Prop :=
  ∀ A `(_ : Encode A) (l1 l2 : list Z),
    Forall (fun n => representable n) l1 ->
    Forall (fun n => representable n) l2 ->
    Sorted (Z.le) l1 ->
    Sorted (Z.le) l2 ->
    SIMP
      (c ← call merge #l1;
       call c #l2)
      (λ l, Sorted (Z.le) l /\ Permutation (l1 ++ l2) l).

Definition split_spec (_split : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list A),
    SIMP
      (call _split #l)
      (λ p, (if Nat.even (length l)
                then length p.1 = Nat.div2 (length l)
                else length p.1 = S (Nat.div2 (length l))) /\
              length p.2 = Nat.div2 (length l) /\
              Permutation (p.1 ++ p.2) l).

Definition mergesort_spec (mergesort : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list Z),
    Forall (fun n => representable n) l ->
    SIMP
      (call mergesort #l)
      (λ l', Sorted (Z.le) l' /\ Permutation l' l).

(* -------------------------------------------------------------------------- *)

(* Custom induction principles. *)

Lemma list_ind2 A (P : list A -> Prop) :
  P [] ->
  (forall (a : A), P [a]) ->
  (forall (a b : A) (l : list A), P l -> P (a::b::l)) ->
  forall l : list A, P l.
Proof.
  intros.
  induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct l; first done.
  destruct l; first done.
  apply H1.
  apply H2. auto with arith.
Qed.

Lemma list_ind_split
  `{Encode A} (P : list A -> Prop) (split : val) (_split_spec : split_spec split) :
  P [] ->
  (forall (a : A), P [a]) ->
  (forall (l1 l2 l : list A) (a b : A),
      l1 ++ l2 ≡ₚ (a::b::l) ->
      SIMP (call split #(a::b::l)) (fun p => p = (l1, l2)) ->
      P l1 ->
      P l2 ->
      P (a::b::l)) ->
  forall l, P l.
Proof.
  intros ?? IHsplit l.
  induction l as [l IHwf] using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct l; first done.
  destruct l; first done.
  unfold split_spec in _split_spec.
  specialize _split_spec with (l:=a::a0::l) (H:=H).
  destruct _split_spec as ([l1 l2]&simp_split&IHn1&IHn2&l1l2_perm).
  simpl in *.
  generalize dependent (length l); intros n???.
  eapply IHsplit; [eassumption | | |]; clear IHsplit.
  { exists (l1, l2).
    split; [assumption | reflexivity]. }
  { apply IHwf.
    destruct (Nat.even n) eqn:Hn; rewrite IHn1.
    { apply suc_div2_lt_suc. }
    { apply even_false_odd_true in Hn.
      rewrite Nat.Odd_div2; last by apply Nat.odd_spec.
      auto with arith. }}
  { apply IHwf.
    rewrite IHn2. apply suc_div2_lt_suc. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Specification proofs. *)

Lemma Merge_spec η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec.
  intros.
  
  eapply SIMP_bind_unary.
  SIMP1.
  eapply SIMP_ret. { rewrite <- solve_encode_val. reflexivity. }
  rewrite <- solve_encode_val.
  eapply SIMP_rec_call with (v:=l2) (ψ:=fun (l2 :list Z) => fun (l : list Z) => Sorted Z.le l /\ (Permutation (l1 ++ l2) l)).
  Unset Printing Notations. unfold __fun3. simpl.
  unfold __fun3. simpl.
  eapply SIMP_covariant.
  eapply SIMP_rec_call with (v:=l2).
  {  admit. }
  { admit. }
  { intros merge l ? ?.
    eapply SIMP_enter_call_VCloRec.
    simpl. unfold acall. destruct merge.
    SIMP1.
    admit. }
  intros.
  eapply SIMP_covariant.


  induction l1 as [|h1 t1]; intros.
  { rewrite app_nil_l.
    SIMP1; repeat SIMP_continue. auto. }
  induction l2 as [|h2 t2].
  { rewrite app_nil_r.
    SIMP1; repeat SIMP_continue. auto. }

  specialize (IHt1 (h2::t2)).
  inversion H0; inversion H1; inversion H2; inversion H3; subst.
  destruct IHt1 as (h1l2&IH1&?&?); auto.
  destruct IHt2 as (l1t2&IH2&?&?); auto.
  SIMP1. SIMP_continue.
  destruct (lt _) eqn:branch; simpl;
    rewrite lt_repr_repr in branch; try auto.
  { unfold __exp1. simpl.
    (* Advance to call merge *)
    SIMP_evaluate. SIMP_Par_Ret.
    (* Use induction hypothesis on merge (h1::t1) *)
    eapply SIMP_simp.
    { eapply prove_simp_bind in IH2.
      rewrite bind_bind in IH2.
      apply IH2. apply SimpReflexive. }
    SIMP_ret.
    split.
    { apply Sorted_cons; first assumption.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* (h1 :: t1) ++ h2 :: t2 =p h2 :: l1t2 *)
      rewrite Permutation_app_comm.
      rewrite <- app_comm_cons.
      apply Permutation_skip.
      by rewrite Permutation_app_comm. }}
   { unfold __exp5. simpl.
     (* Advance to call merge *)
     SIMP_evaluate. SIMP_Par_Ret.
     (* Use induction hypothesis on merge (h2::t2) *)
     eapply SIMP_simp.
     { eapply prove_simp_bind in IH1.
       rewrite bind_bind in IH1.
       apply IH1. apply SimpReflexive. }
    SIMP_ret.
    split.
    { (* Goal: Sorted le (h1 :: h1l2) *)
      apply Sorted_cons; first assumption.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* (h1  :: t1) ++ h2 :: t2 =p h1 :: h1l2 *)
      rewrite <- app_comm_cons.
      by apply Permutation_skip. }}
Qed.

Lemma Split_spec η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec.  
  intros.
  induction l using list_ind2.
  { SIMP1. SIMP_continue. by simpl. }
  { SIMP1. SIMP_continue. by simpl. }
  SIMP_enter.
  eapply SIMP_simp.
  { unfold_breakpoint1. simpl. simp_evaluate. SimpParRet. }
  simpl. SIMP_Par_Ret.
  eapply SIMP_try. { apply IHl. } clear IHl.
  intros [l1 l2] (H0&H1&H2).
  SIMP1. SIMP_continue.
  split.
  { simpl length; simpl fst in H0.
    generalize dependent (length l); intros.
    destruct (Nat.even n); rewrite H0.
    { reflexivity. }
    reflexivity. }
  { split.
    { simpl length. simpl snd in H1.
      rewrite H1. reflexivity. }
    { clear - H2. simpl in *.
      rewrite <- app_comm_cons; apply Permutation_skip.
      rewrite <- Permutation_middle; apply Permutation_skip.
      assumption. }}
Qed.

Lemma MergeSort_spec η :
  (exists split, lookup_name η "split" = ret split /\ split_spec split) ->
  (exists merge, lookup_name η "merge" = ret merge /\ merge_spec merge) ->
  mergesort_spec (VCloRec η __bindings12 "merge_sort").
Proof.
  destruct 1 as (split&Hsplit&_split_spec).
  destruct 1 as (merge&Hmerge&_merge_spec).
  unfold mergesort_spec; intros ?? l.
  (* Custom induction principle based on sublist splitting *)
  apply list_ind_split with (l:=l) (split:=split); clear dependent l.
  { apply _split_spec. }
  { intros _. SIMP1. SIMP_continue. auto. }
  { intros ??. SIMP1. SIMP_continue. auto. }
  intros l1 l2 l a b.
  intros ? SIMP_split IH1 IH2 Hrepr.
  assert (Forall (fun n : Z => representable n) l1) as repr_l1.
  { apply proj1 with (B:= Forall (fun n : Z => representable n) l2).
    apply Forall_app.
    by rewrite_permutation (l1 ++ l2). }
  specialize (IH1 repr_l1).
  assert (Forall (fun n : Z => representable n) l2) as repr_l2.
  { apply proj2 with (A:= Forall (fun n : Z => representable n) l1).
    apply Forall_app.
    by rewrite_permutation (l1 ++ l2). }
  specialize (IH2 repr_l2).
  clear Hrepr.
  (* Would like to use SIMP_enter here, but it leaves a goal on the shelf *)
  SIMP1_call_step. simpl.
  eapply SIMP_simp.
  { apply advance_SimpEvalNext. rewrite bind_ret_right.
    simp_evaluate. unfold_breakpoint1. simp_evaluate.
    SimpParRet. }
  simpl. rewrite Hsplit.
  SIMP_Par_Ret.
  eapply SIMP_try. { apply SIMP_split. } clear SIMP_split.
  intros [l1' l2'] paireq. simpl.
  apply pair_eq in paireq as [??].
  subst l1'; subst l2'.
  eapply SIMP_simp.
  { unfold_breakpoint1. simp_evaluate. SimpParRet. }
  simpl. SIMP_Par_Ret.
  (* Apply induction hypothesis on merge_sort l1 *)
  eapply SIMP_try. { apply IH1. } intro l1'; simpl; intros (?&?).
  eapply SIMP_simp.
  { unfold_breakpoint1. simp_evaluate. SimpParRet. }
  simpl. SIMP_Par_Ret.
  (* Apply induction hypothesis on merge_sort l2 *)
  eapply SIMP_try. { apply IH2. } intros l2'; simpl; intros (?&?).
  SIMP_continue.
  eapply SIMP_covariant.
  { apply _merge_spec with (A:=A) (l1:=l1') (l2:=l2'); try auto.
    { by rewrite_permutation l1'. }
    { by rewrite_permutation l2'. }}
  { intros l'; simpl; intros [??].
    split; first assumption.
    rewrite_permutation l'.
    rewrite_permutation l1'.
    by rewrite_permutation l2'. } 
Qed.

(* -------------------------------------------------------------------------- *)

(* [TO-DO: move] Higher level specification definitions. *)


Definition is_env_with_spec name (spec : val -> Prop) :=
  fun v =>
    match v with
    | VStruct env =>
        match (lookup_name env name) with
        | ret v' => spec v'
        | _ => False
        end
    | _ => False
    end.

Fixpoint env_has_specs env (l : list (string * (val -> Prop))) :=
  match l with
  | [] => True
  | [x] => let (name, spec) := x in
          match (lookup_name env name) with
          | ret v' => spec v'
          | _ => False
          end
  | h::t => let (name, spec) := h in
          match (lookup_name env name) with
          | ret v' => spec v' /\ env_has_specs env t
          | _ => False
          end
  end.

Definition is_env_with_specs (l : list (string * (val -> Prop))) :=
  fun v => match v with
        | VStruct env => env_has_specs env l
        | _ => False
        end.

(* -------------------------------------------------------------------------- *)

(* Main module specification. *)

Lemma Merge__spec:
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  SIMP (eval_mexpr η __main)
    (is_env_with_specs [("merge", merge_spec);
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
