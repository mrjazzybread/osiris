From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_iter.

Context `{!osirisGS Σ}.

Context (A : Type) `{Encode A}.

Definition isListIter (iter : val) : iProp Σ :=
  ∀ (ψ : iEff Σ) E (I : list A → iProp Σ) φ (f : val) (l : list A),
    □ (∀ (Xs : list A) (X : A),
          ⌜ (Xs ++ [X]) `prefix_of` l ⌝ -∗
            I Xs -∗
            EWP (call f #X) @ E <| ψ |> {{ | RET v => ⌜ v = VUnit ⌝ ∗ I (Xs ++ [X]);
                                           | EXN e => φ e ∗ I Xs }})
      -∗
      I [] -∗
      EWP (ncall iter [f; #l] ) @E <| ψ |>
      {{ | RET v => ⌜ v = VUnit ⌝ ∗ I l;
         | EXN e => φ e ∗ ∃ Xs, I Xs ∗ ⌜ Xs `prefix_of` l ⌝ }}.

Lemma iter_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{ RET m, module_spec [("iter", isListIter)] m}}.
Proof.
  iIntros. unfold __main.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_sitem_letrec_singleton isListIter).
    unfold isListIter.
    iIntros (Ψ E I φ f l).
    iIntros "#Hf HI".

    (* At this point, we have [EWP ncall clo [f; #l] ...]
       Unfortunately, n-ary calls do not play well with proofs by
       induction, so we reduce the [ncall] until we have a call to
       a single closure.  *)
    Bind. iApply ewp_call_rec; [ reflexivity | iNext ].
    simpl_eval. Ret. simpl. (* TODO: expr lemma for [EAnonFun]. *)

    (* We generalize the goal to strengthen the induction. We want the
       invariant [I] to hold over the visited prefix of [l], and we
       want the argument of the call to be the remaining suffix. *)
    assert ([] ++ l = l) as Heql by reflexivity; revert Heql.
    (* We generalize the initial prefix (the empty list)
       in [[] ++ l = l] and in [I []]. *)
    generalize (@nil A) at 1 4; intro lpre.
    (* We generalize the initial suffix (the whole list)
       in [lpre ++ l = l] and in [EWP call clo #l]. *)
    generalize l at 1 4; intro lsuf.
    intros Heql.

    (* Induction generalizing over the prefix and suffix, but not [l]. *)
    iLöb as "IH" forall (lsuf lpre Heql) "Hf HI".

    (* Cases on if the suffix is empty or not. *)
    iApply ewp_call_nonrec; iNext.
    prove_simple_match.
    (* The head of the match is trivial. *)
    { Simp; Ret; equality. }

    (* We are now facing the branches of the match. *)
    iModIntro; next_branch.
    { (* Entering the first branch where [l] is a nil. *)
      iApply ewp_EUnit_exn; simpl.
      (* Subgoal: show the postcondition when we return unit. *)
      iSplit; [ equality | ].
      (* If the suffix is empty, then the prefix is the whole list. *)
      rewrite app_nil_r. iApply "HI". }

    (* As we continue to the next branch, we learn that we did not
       match the first branch, see [H0]. *)

    next_branch.
    { (* Entering the second branch, where [l] is a cons. *)
      iApply (ewp_ESeq_exn with "[HI]").
      { (* Application of f to the head of the list. *)
        Simp. iApply "Hf".
        (* Subgoal 1: we are still withing a prefix of the original list. *)
        - iPureIntro. instantiate (1 := lpre).
          apply prefix_app, prefix_cons, prefix_nil.
        (* Subgoal 2: the invariant [I] is preserved. *)
        - iApply "HI". }

      (* We now have two cases after applying [f],
         either an exception was raised or a value was returned. *)

      - (* Case 1: applying [f] caused an exception to be raised. *)
        simpl. iIntros (e) "[Hφ HI]". iFrame.
        iExists lpre. iFrame. iPureIntro.
        rewrite <- (app_nil_r lpre) at 1.
        apply prefix_app, prefix_nil.

      - (* Case 2: applying [f] returned a value. *)
        iIntros (vu); simpl; fold eval.
        iIntros "[-> HI]".

        (* We massage our goal until we get it into a shape where we
           can apply our induction hypothesis. *)
        iApply ewp_EApp.
        { iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality).
          iApply ewp_call_rec; [ reflexivity | ].
          Simp. Ret. equality. }
        { iApply ewp_EPath; Ret; equality. }

        (* We are now ready to use the induction hypothesis. *)
        iApply ("IH" with "[] Hf HI").

        (* Subgoal: show that the new prefix concatenated with
           the new suffix is still equal to the original list. *)
        iPureIntro.
        rewrite (cons_middle _ lpre xs').
        by rewrite app_assoc. }

    (* As we have now traversed all branches, we can use the
       no_matching hypotheses to show a contradiction. *)
    iApply deep_handle_nil_ret.
    destruct_hyp H1. }

  (* We can now show the module specification. *)
  iIntros ([δ η]).
  iIntros "(%iter & Hiter & -> & ->)".

  iApply ewp_sitems_nil. simpl.
  unfold module_spec; intros.
  iExists _; iSplit; [ equality | simpl ].
  iSplit; [ | done ].
  iExists _; iSplit; [ equality | iAssumption ].
Qed.


Definition pure_isListIter (iter : val) : Prop :=
  ∀ (I : list A → Prop) φ (f : val) (l : list A),
    (∀ (Xs : list A) (X : A),
        (Xs ++ [X]) `prefix_of` l ->
        I Xs ->
        pure (call f #X) ##(λ v, v = () ∧ I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
      I [] ->
      pure_call2 iter f #l
        (λ v, v = () ∧ I l)
        (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

Require Import Coq.Wellfounded.Inverse_Image.

Lemma wf_list_length {A B : Type} :
  well_founded (fun (l1 l2 : (B * list A)) => (length l1.2 < length l2.2)%nat).
Proof.
  apply wf_inverse_image. apply lt_wf.
Qed.

Lemma iter_module_pure :
  toplevel __main
    (env_has_pspecs [("iter", pure_isListIter)]).
Proof.
  apply module_struct.
  next_item with pure_isListIter; last first.
  { intros [??] (iter & Hiter & -> & ->).
    by finished_struct. }

  unfold pure_isListIter.
  intros I φ f l Hf HI.

  assert ([] ++ l = l) as Heql by (rewrite app_nil_l; auto); revert Heql HI.
  (* We generalize the initial prefix (the empty list)
     in [[] ++ l = l] and in [I []]. *)
  generalize (@nil A) at 1 2; intro lpre.
  (* We generalize the initial suffix (the whole list)
     in [lpre ++ l = l] and in [EWP call clo #l]. *)
  generalize l at 1 3; intro lsuf.
  intros Heql HI.

  change f with #f.
  eapply pure_rec_call2 with
    (P := λ func lsuf, func = f ∧ ∃ lpref, lpref ++ lsuf = l ∧ I lpref)
    (φ := (λ _ _ v, v = () ∧ I l)).
  { apply wf_list_length. }
  { split; eauto. }

  clear Heql lsuf.

  intros iter ? lsuf IH [-> (lpref & Heql & HIpre)].
  (* Need to do better. *)
  pure_simp. apply pure_ret. pure_enter.

 eapply pure_eval_match. { pure_path. reflexivity. }
 pure_match.

 { pure_const. by rewrite app_nil_r. }

 { eapply pure_eval_seq_exn.
   eapply pure_eval_app. pure_path. pure_path.
   eapply pure_mono.
   { apply Hf.
     - rewrite (cons_middle _ lpref xs'). apply prefix_app.
       rewrite <- (app_nil_r [x]) at 1. apply prefix_app. apply prefix_nil.
     - apply HIpre. }
   intros ? (? & _ & _ & HIx).
   exists a. split; auto.

   pure_simp.
   eapply pure_mono. eapply pure_bind. eapply IH.
   { simpl. lia. }
   { split; first done. exists (lpref ++ [x]). split; last done.
     rewrite (cons_middle x lpref xs'). apply app_assoc_reverse. }
   - intros ? (? & -> & -> & ?). exists (). repeat split. assumption.
   - intros e [Hφ He]. split; assumption.
   - intros e [Hφ HIe]. split; first assumption.
     exists lpref. split; first assumption. rewrite <- (app_nil_r lpref) at 1. apply prefix_app. apply prefix_nil. }
Qed.
