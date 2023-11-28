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
  (match goal with
   | |- SIMP (Stop CEval _ _ _) _ =>
       eapply SIMP_simp; first ((apply advance_SimpEvalRetNext ||
                                   (apply advance_SimpEvalNext ||
                                      apply advance_SimpEval)); apply SimpReflexive)
   | _ => idtac
   end);
  eapply SIMP_simp; [simp_evaluate; apply SimpReflexive|].

Ltac SIMP_execute :=
  repeat (simpl; (SIMP_evaluate || SIMP_continue)); try SIMP_Par_Ret.

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

Ltac conj_upto g b :=
  match goal with
  | |- g => idtac
  | |- _ -> g =>
      match b with
      | true => idtac
      | false => intros ?
      end
  | |- ?A -> ?B -> _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      intros H1 H2; assert (H3 := conj H2 H1);
      generalize dependent H3;
      match b with
      | true => clear H1; conj_upto g true
      | false => conj_upto g true
      end
  end.

Ltac capture_hypotheses l :=
  match goal with
  | |- ?g =>
      generalize dependent l; intro l; conj_upto g false
  end.

Tactic Notation "capture_hypotheses" constr(l) :=
  capture_hypotheses l.

Tactic Notation "capture_hypotheses" constr(l) "as" simple_intropattern(x) :=
  capture_hypotheses l; intros x.


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

(* TODO : move next two lemmas *)

Lemma simp_prove_bind_bind {A B C : Type} m m' a (f : A -> micro B) (g : B -> micro C) :
  simp ('a ← m;
        f a) (ret a) ->
  simp (g a) m' ->
  simp ('a ← m;
        'x ← f a;
        g x) m'.
Proof.
  intros Hsimp HH.
  eapply prove_simp_bind in Hsimp.
  rewrite bind_bind in Hsimp.
  apply Hsimp.
  by simpl.
Qed.

Lemma SIMP_prove_bind_bind `{Encode A} `{Encode X} m (a : A)
  (f : A -> micro val) (g : val -> micro val) (φ : X -> Prop) :
  simp ('c ← m;
        f c) (ret #a) ->
  SIMP (g #a) φ ->
  SIMP ('v1 ← m;
        'v2 ← f v1;
        g v2) φ.
Proof.
  intros Hsimp HSIMP.
  by eapply SIMP_simp;
  first eapply simp_prove_bind_bind; eauto using SimpReflexive.
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
      (call merge #l1)
      (fun c =>
         SIMP (call c #l2)
           (λ l, Sorted (Z.le) l /\ Permutation (l1 ++ l2) l)).

Definition split_spec (split : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list A),
    SIMP
      (call split #l)
      (λ p, (if Nat.even (length l)
             then length p.1 = Nat.div2 (length l)
             else length p.1 = S (Nat.div2 (length l)))
            /\ length p.2 = Nat.div2 (length l) /\ Permutation (p.1 ++ p.2) l).

Definition mergesort_spec (mergesort : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list Z),
    Forall (fun n => representable n) l ->
    SIMP
      (call mergesort #l)
      (λ l', Sorted (Z.le) l' /\ Permutation l' l).

(* -------------------------------------------------------------------------- *)

Lemma wf_double_list_length {A B} :
  well_founded (fun (p1 p2 : list A * list B) =>
                  (length p1.1 + length p1.2 < length p2.1 + length p2.2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

(* Specification proofs. *)

Ltac generalize_pair_aux x y p :=
  remember (x, y) as p eqn:Heqp;
  replace x with (p.1); [| by rewrite Heqp];
  replace y with (p.2); [| by rewrite Heqp];
  clear dependent x y.

Tactic Notation "generalize_pair" constr(x) constr(y) :=
  let p := fresh "p" in
  generalize_pair_aux x y p.

Tactic Notation "generalize_pair" constr(x) constr(y) "as" ident(p) :=
  generalize_pair_aux x y p.

Lemma Merge_spec η:
  merge_spec (VCloRec η __bindings4 "merge" ).
Proof.
  unfold merge_spec. intros ?? l1 l2.
  intros.
  eapply SIMP_nested_rec_call with
    (v1:=l1)
    (v2:=l2)
    (P:=(fun l1 l2 =>
           Forall representable l1 /\ Forall representable l2 /\
             Sorted Z.le l1 /\ Sorted Z.le l2))
    (φ:=(fun l1 l2 l => Sorted Z.le l /\ Permutation (l1++l2) l)).
  { apply wf_double_list_length. }
  { auto. }
  { rewrite eval_eval'; reflexivity. }
  clear dependent l1 l2.
  intros vf l1 l2 HP IH.
  repeat destruct_hyp.
  destruct l1 as [|h1 t1]; last destruct l2 as [|h2 t2]; intros.
  (* Case: l1 = [] *)
  { SIMP1; SIMP1; SIMP_continue. auto. }
  (* Case: l2 = [] *)
  { rewrite app_nil_r.
    SIMP1; SIMP1; SIMP_continue. auto. }
  (* Case: l1 = h1::t1, l2 = h2::t2 *)
  all_inversions.
  SIMP1. SIMP_continue.
  rewrite lt_repr_repr by auto.
  (* Reason by cases on the comparison of the heads *)
  destruct (h2 <? h1) eqn:branch; simpl.
  { (* Case: h2 < h1 *)
    SIMP_execute.
    (* Use the induction hypothesis on [call merge (h1::t1) t2] *)
    destruct (IH (h1::t1) t2) as (c & Hc & l' & ? & ? & ?); auto with arith.
    exists (h2::l'). split.
    { (* Todo: Make this process easier *)
      repeat (eapply prove_simp_bind; eauto). apply SimpReflexive. }
    (* Establish the postcondition *)
    split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      rewrite_permutation l'. apply Permutation_sym; apply Permutation_middle. }}
  { (* Case: h1 < h2 *)
    SIMP_execute.
    (* Use the induction hypothesis on [call merge t1 (h2::t2)] *)
    destruct (IH t1 (h2::t2)) as (c & Hc & l' & ? & ? & ?); auto with arith.
    exists (h1::l'). split.
    { (* Todo: Make this process easier *)
      repeat (eapply prove_simp_bind; eauto). apply SimpReflexive. }
    (* Establish the postcondition *)
    split.
    { (* Subgoal: the output is sorted *)
      constructor; first done.
      eapply HdRel_Sorted_Permutation; eauto with zarith. }
    { (* Subgoal: the output is a permutation of the concatenation of the inputs *)
      by rewrite_permutation l'. }}
Qed.

Lemma Split_spec η :
  split_spec (VCloRec η __bindings7 "split").
Proof.
  unfold split_spec.  
  intros.
  eapply SIMP_rec_call with
    (φ:=fun l p =>
          (if Nat.even (length l)
           then length p.1 = Nat.div2 (length l)
           else length p.1 = S (Nat.div2 (length l)))
          /\ length p.2 = Nat.div2 (length l) /\ p.1 ++ p.2 ≡ₚ l).
  (* We reason by well-founded induction on the length of the list *)
  { apply wf_list_length. }
  (* Precondition: we have none *)
  { apply I. }
  
  clear l; intros split l _ IH; simpl.
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
    simpl in *; split; last split.
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
  
  unfold mergesort_spec; intros ?? l Hrep.
  eapply SIMP_rec_call with
    (φ:=fun l l' => Sorted Z.le l' /\ l' ≡ₚ l).
  (* We reason by well founded induction on the length of the list *)
  { apply wf_list_length. }
  (* Precondition: all items must be representable *)
  { apply Hrep. }
  
  clear dependent l; intros mergesort l Hrep IH.
  destruct l as [|a l]; last destruct l as [|b l]; SIMP_execute.
  (* Case: [] *)
  { auto. }
  (* Case: [a] *)
  { auto. }
  (* Case: a::b::l *)
  intros [l1 l2]; simpl; intros (Hl1 & Hl2 & Hperm).
  (* Assert that the sublists l1 and l2 satisfy the precondition *)
  assert (Forall (fun n => representable n) l1) as Hrep1 by
      (apply Forall_app with (l1:=l1) (l2:=l2); by rewrite_permutation (l1++l2)).
  assert (Forall (fun n => representable n) l2) as Hrep2 by
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
  eapply SIMP_bind_unary.
  (* Use the fact that [merge] satisfies its specification *)
  { eapply _merge_spec with (l2:=sl2); eauto. 
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
