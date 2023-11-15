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


Fixpoint encode_list `{Encode A} (t : list A) : val :=
  match t with
  | nil => VConstant "[]"
  | cons x l => VData "::" <v #x, (encode_list l) v>
  end.

Local Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (l : list A),
    encode_list l = #l.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_list_is_encode : encode.


Lemma solve_encode_nil `{Encode A} (l : list A) :
  nil = l ->
  VConstant "[]" = #l.
Proof.
  intros. subst l. eauto.
Qed.

Lemma solve_encode_cons `{Encode A} (l : list A) x l1 vx vl1 :
  cons x l1 = l ->
  vx = #x ->
  vl1 = #l1 ->
  VData "::" <v vx, vl1 v> = #l.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve solve_encode_nil solve_encode_cons : encode.

Ltac fixme :=
  unfold EMkTuple; unfold PMkTuple; simpl.

Ltac SimpParRetNext :=
  (apply SimpParRetLeftNext || apply SimpParRetRightNext).

Ltac SimpParRet :=
  (apply SimpParRetLeft || apply SimpParRetRight).

Lemma Sorted_Hd_cmp A x (l : list A) (cmp : A -> A -> Prop) `{Transitive A cmp}:
  Sorted cmp l -> HdRel cmp x l <-> Forall (cmp x) l.
Proof.
  split; intros.
  { induction l; first done.
    destruct l; first (constructor; by inversion H1).
    apply Forall_cons; split; first by inversion H1.
    apply IHl; [ by inversion H0 | apply HdRel_cons].
    eapply H; first by inversion H1.
    inversion H0; subst. by inversion H5. }
  { induction l; first done.
    apply HdRel_cons.
    by inversion H1. }
Qed.

Lemma Zle_Transitive : Transitive Z.le.
Proof.
  unfold Transitive. intros.
  eauto using Z.le_trans.
Qed.
Local Hint Resolve Zle_Transitive : core.

Lemma Sorted_decomp {A} (cmp : A -> A -> Prop) `{Transitive A cmp} l l' x h t :
    Sorted cmp l -> (h :: t) ++ l'  ≡ₚ l ->
    Sorted cmp l' -> Sorted cmp (h :: t) ->
    HdRel cmp x l' -> cmp x h ->
    Sorted cmp (x :: l).
Proof.
  intros.
  apply Sorted_cons; first assumption.
  (* Goal: HdRel cmp x l *)
  apply Sorted_Hd_cmp; only 1-2: auto.
  (* Goal: Forall (cmp x) l *)
  rewrite <- H1; apply Forall_app.
  split; apply Sorted_Hd_cmp; auto.
Qed.

Definition merge_spec (merge : val) : Prop :=
  ∀ A `(_ : Encode A) (l1 l2 : list Z),
    Forall (fun n => representable n) l1 ->
    Forall (fun n => representable n) l2 ->
    Sorted (Z.le) l1 ->
    Sorted (Z.le) l2 ->
    SIMP
      (call merge #(l1, l2))
      (λ l, Sorted (Z.le) l /\ Permutation (l1 ++ l2) l).

Lemma Merge_spec:
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  merge_spec (VCloRec η __bindings4 "merge").
Proof.
  intros.
  generalize η; clear η; intro η.
  unfold merge_spec.
  induction l1 as [|h1 t1]; intros.
  { rewrite app_nil_l.
    SIMP1. repeat SIMP_continue. auto. }
  induction l2 as [|h2 t2].
  { rewrite app_nil_r.
    SIMP1; repeat SIMP_continue. auto. }
  specialize (IHt1 (h2::t2)).
  inversion H0; inversion H1; inversion H2; inversion H3; subst.
  destruct IHt1 as (h1l2&IH1&?&?); auto.
  destruct IHt2 as (l1t2&IH2&?&?); auto.
  (* SIMP_enter_and_abstract *)
  SIMP1. SIMP_continue. SIMP_continue.
  rewrite lt_repr_repr by representable.
  destruct (h2 <? h1) eqn:branch; simpl.
  { unfold __exp1. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpParRetNext.
    repeat (eapply advance_SimpBind; simpl; first SimpParRetNext).
    eapply advance_SimpBind; simpl.

    (* Use induction hypothesis *)
    eapply prove_simp_bind. { apply IH2. }
    all: try apply SimpReflexive; simpl.
    SIMP_ret.
    split.
    { eapply Sorted_decomp; eauto.
      apply Z.ltb_lt in branch.
      by apply Z.lt_le_incl. }
    { (* (h1 :: t1) ++ h2 :: t2 =p h2 :: l1t2 *)
      rewrite Permutation_app_comm.
      rewrite <- app_comm_cons.
      apply Permutation_skip.
      by rewrite Permutation_app_comm. }}

  { unfold __exp0. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpParRetNext.
    repeat (eapply advance_SimpBind; simpl; first SimpParRetNext).
    eapply advance_SimpBind; simpl.

    (* Use Induction hypothesis *)
    eapply prove_simp_bind.  { apply IH1. }
    all: try apply SimpReflexive. simpl.
    SIMP_ret.
    split.
    { (* Goal: Sorted le (h1 :: h1l2) *)
      rewrite Permutation_app_comm in H5.
      eapply Sorted_decomp; eauto.
      (* Goal: h1 <= h2 *)
      by apply Z.ltb_ge in branch. }
    { (* (h1  :: t1) ++ h2 :: t2 =p h1 :: h1l2 *)
      rewrite <- app_comm_cons.
      by apply Permutation_skip. }}
Qed.

Definition merge2_spec (merge2 : val) : Prop :=
  ∀ A `(_ : Encode A) (l1 l2 : list Z),
    Forall (fun n => representable n) l1 ->
    Forall (fun n => representable n) l2 ->
    Sorted (Z.le) l1 ->
    Sorted (Z.le) l2 ->
    SIMP
      (c ← call merge2 #l1;
       call c #l2)
      (λ l, Sorted (Z.le) l /\ Permutation (l1 ++ l2) l).

Lemma Merge2_spec η:
  merge2_spec (VCloRec η
                 (RecBiCons
                    (RecBinding "merge2" (AnonFun "l1" (EAnonFun __fun8))) RecBiNil)
                 "merge2").
Proof.
  unfold merge2_spec.
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
  { unfold __exp6. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpParRetNext.
    repeat (eapply advance_SimpBind; simpl; first SimpParRetNext).
    eapply advance_SimpBind; simpl.

    (* Use induction hypothesis *)
    
    eapply prove_simp_bind in IH2.
    rewrite bind_bind in IH2.
    apply IH2. simpl.
    all: try apply SimpReflexive; simpl.
    SIMP_ret.
    split.
    { eapply Sorted_decomp; eauto.
      apply Z.ltb_lt in branch.
      by apply Z.lt_le_incl. }
    { (* (h1 :: t1) ++ h2 :: t2 =p h2 :: l1t2 *)
      rewrite Permutation_app_comm.
      rewrite <- app_comm_cons.
      apply Permutation_skip.
      by rewrite Permutation_app_comm. }}

   { unfold __exp5. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpParRetNext.
    repeat (eapply advance_SimpBind; simpl; first SimpParRetNext).
    eapply advance_SimpBind; simpl.


    (* Use induction hypothesis *)
    eapply prove_simp_bind in IH1.
    rewrite bind_bind in IH1.
    apply IH1. simpl.
    all: try apply SimpReflexive; simpl.
    SIMP_ret.
    split.
    { (* Goal: Sorted le (h1 :: h1l2) *)
      rewrite Permutation_app_comm in H5.
      eapply Sorted_decomp; eauto.
      (* Goal: h1 <= h2 *)
      by apply Z.ltb_ge in branch. }
    { (* (h1  :: t1) ++ h2 :: t2 =p h1 :: h1l2 *)
      rewrite <- app_comm_cons.
      by apply Permutation_skip. }}
Qed.

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
  apply H2.
  auto with arith.
Qed.

Definition split_spec (_split : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list A),
    SIMP
      (call _split #l)
      (λ p, (if Nat.even (length l)
                then length p.1 = Nat.div2 (length l)
                else length p.1 = S (Nat.div2 (length l))) /\
              length p.2 = Nat.div2 (length l) /\
              Permutation (p.1 ++ p.2) l).

Lemma Split_spec η :
  split_spec (VCloRec η __bindings12 "split").
Proof.
  unfold split_spec.  
  intros.
  induction l using list_ind2.
  { SIMP1. SIMP_continue. by simpl. }
  { SIMP1. SIMP_continue. by simpl. }
  SIMP1.
  eapply SIMP_simp.
  match goal with
  | |- simp ?m _ => unfold_breakpoint m
  | _ => fail ""
  end.
  simpl. simp_eval.
  SimpParRet.
  eapply SIMP_simp. eapply simp_try.
  repeat (rewrite eval_eval'; simpl).
  apply SimpParRetRet.
  eapply SIMP_try. { apply IHl. }
  intros [l1 l2] (H0&H1&H2).
  SIMP1. SIMP_continue.
  split.
  { simpl length; simpl fst in H0.
    generalize dependent (length l); intros.
    simpl Nat.even.
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


Lemma Suc_div2_lt_suc n :
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

Lemma list_ind_split
  `{Encode A} (P : list A -> Prop) (split : val) (H0 : split_spec split) :
  P [] ->
  (forall (a : A), P [a]) ->
  forall (l : list A), (forall (l1 l2 : list A) (l : list A),
                      l1 ++ l2 ≡ₚ l ->
                      simp (call split #(l)) (ret #(l1, l2)) ->
                      P (l1) ->
                      P (l2) -> P l) ->
                  P l.
Proof.
  intros.
  induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct l; first done.
  destruct l; first done.
  unfold split_spec in H0.
  specialize H0 with (l:=a::a0::l) (H:=H).
  destruct H0 as ([l1 l2]&?&?&?&?).
  simpl in *.
  eapply H3.
  { apply H7. }
  { apply H0. }
  generalize dependent (length l); intros.
  { apply H4.
    destruct (Nat.even n) eqn:Hn; rewrite H5.
    { apply Suc_div2_lt_suc. }
    { rewrite <- Nat.negb_odd in Hn.
      apply negb_false_iff in Hn.
      rewrite Nat.Odd_div2; last by apply Nat.odd_spec.
      apply -> Nat.succ_lt_mono.
      apply Nat.lt_div2; lia. } }
  { apply H4. rewrite H6.
    apply Suc_div2_lt_suc. }
Qed.

Ltac Forall_inversion :=
  match goal with
  | H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H
  end.

Definition mergesort_spec (mergesort : val) : Prop :=
  ∀ A `(_ : Encode A) (l : list Z),
    Forall (fun n => representable n) l ->
    SIMP
      (call mergesort #l)
      (λ l', Sorted (Z.le) l' /\ Permutation l' l).
  
Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Lemma MergeSort_spec η :
  (exists split, lookup_name η "split" = ret split /\ split_spec split) ->
  (exists merge, lookup_name η "merge2" = ret merge /\ merge2_spec merge) ->
  mergesort_spec (VCloRec η __bindings17 "merge_sort").
Proof.
  destruct 1 as (split&Hsplit&_split_spec).
  unfold mergesort_spec; intros.
  generalize H1.
  apply list_ind_split with (l:=l) (split:=split); intros; clear dependent l.
  { apply _split_spec. }
  { SIMP1. SIMP_continue. auto. }
  { SIMP1. SIMP_continue. auto. }
  destruct l0.
  { SIMP1. SIMP_continue. auto. }
  destruct l0.
  { SIMP1. SIMP_continue. auto. }
  SIMP1_call_step. simpl.
  eapply SIMP_simp. simp1. 
  match goal with
  | |- simp ?m _ => unfold_breakpoint m
  | _ => fail ""
  end.
  simpl.
  repeat (rewrite eval_eval'; simpl).
  SimpParRet. simpl.
  eapply SIMP_simp. { apply SimpParRetRet. }
  simpl.
  eapply SIMP_try.
  { apply H4.
    apply proj1 with (B:= Forall (fun n : Z => representable n) l2).
    apply Forall_app.
    rewrite H2. apply H6. }
  intros l1'; simpl; intros (?&?). 
  eapply SIMP_simp.
  match goal with
  | |- simp ?m _ => unfold_breakpoint m
  | _ => fail ""
  end.
  simpl.
  repeat (rewrite eval_eval'; simpl).
  SimpParRet. simpl.
  eapply SIMP_simp. { apply SimpParRetRet. }
  simpl. 
  eapply SIMP_try.
  { apply H5.
    apply proj2 with (A:= Forall (fun n : Z => representable n) l1).
    apply Forall_app.
    rewrite H2. apply H6. }
  intro l2'; simpl; intros (?&?).
  destruct H as (merge&Hmerge&_merge_spec).
  SIMP_continue.
  unfold merge2_spec in _merge_spec.
  unfold split_spec in _split_spec.
  destruct _split_spec with (l:=(z::z0::l0)) (H:=Encode_Z).
  repeat destruct_hyp.
  destruct _merge_spec with (A:=A) (l1:=l1') (l2:=l2').
  { apply H0. }
  { rewrite H7.
    apply proj1 with (B:= Forall (fun n : Z => representable n) l2).
    apply Forall_app.
    rewrite H2. apply H6. }
  { rewrite H9.
    apply proj2 with (A:= Forall (fun n : Z => representable n) l1).
    apply Forall_app.
    rewrite H2. apply H6. }
  { auto. }
  { auto. }
  repeat destruct_hyp.
  exists x0.
  split.
  { assumption. }
  { split.
    { assumption. }
    { rewrite <- H15.
      rewrite <- H2.
      rewrite H7. rewrite H9.
      auto. } }
  
  Unshelve. apply next.
Qed.

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

Fixpoint is_env_with_specs (l : list (string * (val -> Prop))) :=
  fun v => match v with
        | VStruct env => env_has_specs env l
        | _ => False
        end.

Lemma Merge__spec:
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  SIMP (eval_mexpr η __main)
    (is_env_with_specs [("merge", merge_spec);
                        ("merge2", merge2_spec);
                        ("split", split_spec);
                        ("merge_sort", mergesort_spec)]).
Proof.
  intros.
  SIMP1.
  SIMP_specify "merge" merge_spec.
  { apply Merge_spec. } intros merge _spec.
  SIMP_continue.
  SIMP_specify "merge2" merge2_spec.
  { apply Merge2_spec. } intros merge2 _spec2.
  SIMP_continue.
  SIMP_specify "split" split_spec.
  { apply Split_spec. } intros split _spec3.
  SIMP_continue.
  SIMP_specify "merge_sort" mergesort_spec.
  { apply MergeSort_spec.
    { exists split. simpl. auto. }
    { exists merge2. simpl. auto. } } intros mergesort _spec4.
  repeat SIMP_continue.
  (* Postcondition *)
  simpl. auto.
Qed.
