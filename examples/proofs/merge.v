From Stdlib Require Import Wellfounded.Inverse_Image.
From osiris Require Import osiris.
From osiris.utils Require Import orders sorting.

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
  split; intros Hn;
    [ rewrite <- Nat.negb_even | rewrite <- Nat.negb_odd ];
    by rewrite Hn.
Qed.

Local Hint Resolve even_false_odd_true : arith.

(* We implicitly use the following lemma when we prove that the list returned
   by [split l] are smaller than l *)

Lemma div2_lt_Sn n :
    (Nat.div2 n < S n)%nat.
Proof.
 destruct (Nat.even n) eqn:Hn.
 { (* Case: n is even *)
   rewrite Nat.Even_div2.
   - apply Nat.lt_div2; lia.
   - apply Nat.even_spec. assumption. }
 { (* Case: n is odd *)
   apply Nat.succ_lt_mono.
   rewrite Nat.Odd_div2.
   - apply PeanoNat.le_lt_n_Sm.
     transitivity n; [ apply Nat.le_div2 | auto ].
   - apply Nat.odd_spec. by apply even_false_odd_true. }
Qed.

Local Hint Resolve div2_lt_Sn : arith.

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
    rewrite Nat.Odd_div2.
    + apply -> Nat.succ_lt_mono. apply Nat.lt_div2. lia.
    + apply Nat.odd_spec. by apply even_false_odd_true. }
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
  pure m (λ l, Sorted Z.le l ∧ Permutation (l1++l2) l) (⊥ : exn → Prop).


(* Specification for [split l]. *)

Local Definition split_post {A} (l : list A) p :=
  (if Nat.even (length l)
   then length p.1 = Nat.div2 (length l)
   else length p.1 = S (Nat.div2 (length l)))
  /\ length p.2 = Nat.div2 (length l) /\ Permutation (p.1 ++ p.2) l.

Definition split_spec `{Encode A} (l : list A) (m : microvx) : Prop :=
  pure m (split_post l) (⊥ : exn → Prop).


(* Specification for [mergesort l]. *)

Definition mergesort_spec (l : list Z) (m : microvx) : Prop :=
  (* Precondition on [l]. *)
  Forall representable l ->
  (* Specification of the function call [mergesort l]. *)
  pure m (λ l', Sorted Z.le l' ∧ Permutation l' l) (⊥ : exn → Prop).

(* Specification for [mergesort l]. *)

Local Definition mergesort_pre := (fun l => Forall representable l).
Local Definition mergesort_post := (fun l l' => Sorted Z.le l' /\ Permutation l' l).
Local Hint Unfold mergesort_post : core.
Local Hint Unfold mergesort_pre : core.

Definition mergesort_spec' (l : list Z) (e : microvx) : Prop :=
  mergesort_pre l ->
  pure e (mergesort_post l) (⊥ : exn → Prop).

(* -------------------------------------------------------------------------- *)

(* Pure, Hoare-Style Specification proofs. *)

Section proof.

(* We abstract over the environment, making localised assumptions
   about what it contains when necessary. *)

Variable η : env.

Local Instance cons_data `{Encode A} : Data "::" τ[A; list A] (list A) :=
  { ctor_apply := λ '(a, l), a :: l;
    ctor_encode := λ '(a, xs), eq_refl }.

Lemma merge_mkspec merge (l1 l2 : list Z) :
  (lookup_name η "l1" = Some #l1) ->
  (lookup_name η "l2" = Some #l2) ->
  (lookup_name η "merge" = Some merge) ->
  @Spec τ[list Z; list Z] merge
    (λ (x1 x2 : list Z) (m : microvx),
      (length x1 + length x2 < length l1 + length l2)%nat
      → merge_spec x1 x2 m)
  → merge_spec l1 l2
      (please_eval η
         (EMatch (ETuple [EPath ["l1"]; EPath ["l2"]]) __merge_branches)).
Proof.
   intros Hl1 Hl2 Hmerge IH.
   unfold merge_spec. intros [Hreprl1 Hsortl1] [Hreprl2 Hsortl2].
   apply pure_please_eval.
   eapply pure_eval_match.
   { eapply pure_eval_tuple.
     eapply pure_evals_cons. pure_path.
     eapply pure_evals_singleton. pure_path.
     intros ? ? (<- & <-). reflexivity. }

   pure_match; abstract_env.

   { pure_path. auto. }
   { pure_path. split; [ | rewrite app_nil_r ]; auto. }

   rename x0 into h2, x into h1, xs' into t1, xs'0 into t2.
   all_inversions.
   eapply pure_eval_ifthenelse.
   { (* Evaluate expression "h1 <= h2" *)
     apply pure_eval_EOpLe. pure_path. pure_path. assumption. assumption. }
   { (* Evaluate expression "h1 :: (merge t1 l2)" knowing h1 <= h2 *)
     intros.
     eapply pure_eval_data.
     eapply pure_evals_cons. pure_path.
     eapply pure_evals_singleton.

     (* Evaluate "merge t1 l2" under the cons *)
     eapply (pure_EApp τ[list Z; list Z]).
     { pure_path. rewrite <- solve_encode_val. reflexivity. eassumption. }
     { pure_path. }
     { pure_path. }
     { simpl; unfold tapp.
       intros ? l2 <- <-.
       intros m Hm.
       unfold merge_spec in Hm.
       apply Hm; auto with arith. }
     intros ? l (<- & Hsorted & Hpermutation).
     split.
     + (* Subgoal: the output is sorted *)
       constructor; [ assumption | ].
       simpl in H.
       eapply (HdRel_Sorted_Permutation l t1 (h2 :: t2)); eauto.
       constructor. simpl in H1. lia.
     + (* Subgoal: the output is a permutation of the inputs *)
       simpl.
       by rewrite_permutation l. }

   { (* Evaluate expression "h2 :: (merge l1 t2)" knowing  (h1 > h2) *)
     simpl; intros.
     eapply pure_eval_data.
     eapply pure_evals_cons. pure_path.
     eapply pure_evals_singleton.

     (* Evaluate "merge l1 t2" under the cons *)
     eapply (pure_EApp τ[list Z; list Z]).
     { pure_path. rewrite <- solve_encode_val. reflexivity. eassumption. }
     { pure_path. }
     { pure_path. }

     { unfold tbind, tapp.
       intros ? ? <- <-.
       intros m Hm.
       apply Hm; simpl; first lia; auto. }

     intros ? l (<- & Hsorted & Hpermutation).
     split; simpl ctor_apply.
     + (* Subgoal: the output is sorted *)
       constructor; [ assumption | ].
       eapply HdRel_Sorted_Permutation; eauto with zarith.
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
Hypothesis Hmerge : lookup_name η "merge" = Some merge.

Lemma split_mkspec split (l : list Z) :
  (lookup_name η "l" = Some #l) ->
  (lookup_name η "split" = Some split) ->
  Spec τ[list Z] split
       (λ (x : list Z) (m : microvx),
         (length x < length l)%nat → split_spec x m) ->
  split_spec l (please_eval η (EMatch (EPath ["l"]) __split_branches)).
Proof.
  intros Hl Hsplit IH.
  unfold split_spec.
  apply pure_please_eval.
  eapply pure_eval_match.
  { pure_path. }

  pure_match; abstract_env.

  (* First branch of match *)
  { (* Case: l matches [] *)
    pure_tuple. pure_const. apply eq_refl. pure_const. apply eq_refl.
    intros ?? (<- & <-). unfold split_post; simpl. auto. }
  (* Second branch of match *)
  { (* Case: l matches [x] *)
    pure_tuple. pure_data. pure_const. apply eq_refl.
    intros ?? (<- & <-). apply eq_refl.
    pure_const. apply eq_refl.
    intros ?? (<- & <-).
    (* Establish postcondition *)
    split; simpl; auto. }
  (* Third branch of match *)
  { (* Case: l matches a::b::t *)
    rename xs' into t.
    eapply pure_eval_let_pair.
    { (* Recursive call to [split t]. *)
      eapply (pure_EApp τ[list Z]).
      { pure_path. rewrite <- solve_encode_val. reflexivity. eassumption. }
      { pure_path. } simpl.
      intros ? <- m Hm. apply Hm. lia. }
    (* Apparte: resolving pattern_matching *)
    2:{ intros l1 l2 Hpost.
        eapply pattern_exn_mono.

        rewrite encode_encode'. eapply pat_PPair.
        reflexivity. reflexivity. pattern_match.
        instantiate (1:= λ (δ : env), ∃ l1 l2, δ = [("l2", #l2); ("l1", #l1)] ∧ split_post t (l1, l2)).
        eexists l1, l2; eauto. tauto. }
    intros ? (l1 & l2 & -> & Hpost).
    (* Eval (x1::l1, x2::l2) *)
    pure_tuple.
    - pure_data. intros ?? (<- & <-). apply eq_refl.
    - pure_data. intros ?? (<- & <-). apply eq_refl.
    - intros ?? (<- & <-).
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
        rewrite_permutation t.
        apply Permutation_skip.
        apply Permutation_sym.
        apply Permutation_middle. } }
Qed.

(* We make a new section, adding the hypotheses that [split] is in the
   environment and satisfies its spec. *)

Section split.

Variable split : val.
Hypothesis _split_spec : @Spec τ[list Z] split split_spec.
Hypothesis Hsplit : lookup_name η "split" = Some split.

Lemma mergesort_mkspec mergesort (l : list Z) :
  (lookup_name η "l" = Some #l) ->
  (lookup_name η "merge_sort" = Some #mergesort) ->
  (Spec τ[list Z] mergesort (λ x m,
       (length x < length l)%nat ->
       mergesort_spec x m)) ->
  mergesort_spec l (please_eval η (EMatch (EPath ["l"]) __merge_sort_branches)).
Proof.
  intros Hl Hmergesort IH Hpre.
  apply pure_please_eval.
  eapply pure_eval_match. { pure_path. }
  pure_match.
  (* Branch: "[]"  *)
  { pure_const. auto. }
  (* Branch: "[x]" *)
  { pure_data. pure_const. apply eq_refl.
    intros ?? (<- & <-).
    auto. }

  (* Branch: "_" *)
  rename x0 into l.
  assert (exists m, length l = S m) as [m Heql].
  { subst. destruct l; [ congruence | eauto ]. }
  simpl in IH. rewrite Heql in IH.
  eapply pure_eval_let_pair.
  (* Use knowledge that [split] ⊨ [split_spec] *)
  { eapply (pure_EApp τ[list Z]).
    { pure_path. rewrite <- solve_encode_val. reflexivity. eassumption. }
    { pure_path. }
    intros ? <- ms Hsplitm. apply Hsplitm. }
    (* Apparte: resolving pattern_matching *)
    2:{ intros l1 l2 Hpost.
        eapply pattern_exn_mono.

        rewrite encode_encode'. eapply pat_PPair.
        reflexivity. reflexivity. pattern_match.
        instantiate (1:= λ (δ : env), ∃ l1 l2, δ = [("l2", #l2); ("l1", #l1)] ∧ split_post (x :: l) (l1, l2)).
        eexists l1, l2; eauto. tauto. }
  intros ? (l1 & l2 & -> & Hpost).
  destruct Hpost as (Hl1 & Hl2 & Hperm).
  assert (Forall representable (l1 ++ l2)) as Hrepr by (rewrite Hperm; done).
  apply Forall_app in Hrepr as [Hreprl1 Hreprl2].
  eapply pure_eval_let1var.
  { eapply (pure_EApp τ[list Z]).
    { pure_path. eassumption. }
    { pure_path. }
    intros ? <- mm Hcall. apply Hcall.
    - simpl in Hl1; rewrite Heql in Hl1.
      apply div2_lt_succ. apply Hl1.
    - apply Hreprl1. }

  intros l1' IHl1'.
  eapply pure_eval_let1var.
  { eapply (pure_EApp τ[list Z]).
    { pure_path. eassumption. }
    { pure_path. }
    intros ? <- mm Hcall. apply Hcall.
    - rewrite Hl2. simpl. destruct (length l); auto with arith.
      inversion Heql. auto with arith.
    - apply Hreprl2. }

  intros l2' IHl2'; clear IH Hl1 Hl2 Heql m.
  abstract_env.
  eapply (pure_EApp τ[list Z; list Z]).
  - (* Use the knowledge that [merge] ∈ [η] *)
    pure_path. rewrite <- solve_encode_val. reflexivity. eassumption.
  - pure_path.
  - pure_path.
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
      rewrite_permutation l'. rewrite_permutation (x :: l).
      rewrite_permutation l1'. rewrite_permutation l2'.
      reflexivity.
Qed.

End split.
End merge.
End proof.

(* We chain together the lemmas in the [proof] section to verify the
   whole [merge.ml] file. *)

Lemma Module__spec' η :
  eval_module η __main (λ _, True).
Proof.
  apply module_struct.
  (* Proof that [merge] satisfies [merge_spec]. *)
  eapply (@structs_letrec τ[list Z; list Z]) with
    (P := merge_spec). repeat constructor.
  { repeat eexists. }
  { apply wf_double_list_length. }
  { simpl.
    intros merge l1 l2 IH.
    eapply merge_mkspec; eauto. }
  intros merge Hmerge.

  (* Proof that [split] satisfies [split_spec]. *)
  eapply (structs_letrec τ[list Z]) with
    (P := split_spec).
  { repeat eexists. }
  { apply list_wf. }
  { intros split l IH.
    eapply split_mkspec; eauto. }
  intros split Hsplit.

  (* Proof that [merge_sort] satisfies [mergesort_spec]. *)
  eapply (@structs_letrec τ[list Z]) with
    (P := mergesort_spec). repeat constructor.
  { repeat eexists. }
  { apply list_wf. }
  { simpl.
    intros mergesort l IH.
    eapply mergesort_mkspec; eauto. by rewrite <- solve_encode_val. }
  intros mergesort Hmergesort.

  (* We have now evaluated the whole struct. *)
  finished_struct.
  (* Goal: Show that the resulting environment satisfies the spec. *)
  simpl. repeat split; assumption.
Qed.
