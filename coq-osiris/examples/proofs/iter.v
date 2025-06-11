From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_iter.

Require Import Coq.Wellfounded.Inverse_Image.

Section iris_proof.

Context `{!osirisGS Σ}.
Context `{Encode A}.

Definition isListIter (iter : val) : iProp Σ :=
  ∀ (ψ : iEff Σ) E (I : list A → iProp Σ) φ (f : val) (l : list A),
    □ (∀ (Xs : list A) (X : A),
          ⌜ (Xs ++ [X]) `prefix_of` l ⌝ -∗
            I Xs -∗
            EWP (call f #X) @ E <| ψ |> {{   RET v => ⌜ v = VUnit ⌝ ∗ I (Xs ++ [X]);
                                           | EXN e => φ e ∗ I Xs }})
      -∗
      I [] -∗
      EWP (ncall iter [f; #l] ) @E <| ψ |>
      {{   RET v => ⌜ v = VUnit ⌝ ∗ I l;
         | EXN e => φ e ∗ ∃ Xs, I Xs ∗ ⌜ Xs `prefix_of` l ⌝ }}.

Lemma iter_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{ ensures m, module_spec [("iter", isListIter)] m}}.
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
    simpl; Bind.

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
                   iApply ewp_call_rec; first reflexivity; iNext. Simp. Ret. simpl.
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
        iPureIntro.
        rewrite <- (app_nil_r lpre) at 1.
        apply prefix_app, prefix_nil.

      - (* Case 2: applying [f] returned a value. *)
        iIntros (vu); simpl; fold eval.
        iIntros "[-> HI]".

        (* We massage our goal until we get it into a shape where we
           can apply our induction hypothesis. *)
        iApply (ewp_EApp' with "[HI]").
        { iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality).
          iApply ("IH" with "[] Hf HI").

          iPureIntro. rewrite (cons_middle _ lpre xs').
          by rewrite app_assoc. }

        iApply ewp_EPath. iApply ewp_value. done.
        iIntros (partial_iter l) "Hpart ->". auto. }

    (* As we have now traversed all branches, we can use the
       no_matching hypotheses to show a contradiction. *)
    iApply deep_handle_nil_ret.
    resolve_no_match. }

  (* We can now show the module specification. *)
  iIntros ([δ η]).
  iIntros "(%iter & Hiter & -> & ->)".

  iApply ewp_sitems_nil. simpl.
  unfold module_spec; intros.
  iExists _; iSplit; [ equality | simpl ].
  iSplit; [ | done ].
  iExists _; iSplit; [ equality | iAssumption ].
Qed.

End iris_proof.

Section pure_proof.

Context `{Encode A}.

Definition pure_isListIter (iter : val) : Prop :=
  ∀ (I : list A → Prop) φ (f : val) (l : list A),
    (∀ (Xs : list A) (X : A),
        (Xs ++ [X]) `prefix_of` l ->
        I Xs ->
        pure (call f #X)
          (λ v : (), I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
      I [] ->
      pure_call2 iter f #l
        (λ (v : ()), I l)
        (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

(* -------------------------------------------------------------------------- *)

(* Well-foundedness *)

(* FIXME use the measure function to only have a WF condition on lists *)
#[local] Program Instance list_tuple_wf {A B} : WellFounded (B * list A) :=
  {| wf_relation := (fun x y => (length x.2 < length y.2)%nat )|}.
Next Obligation. intros; apply wf_inverse_image, lt_wf. Qed.

(* -------------------------------------------------------------------------- *)

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
    (φ := (λ _ _ _, I l))
    (R := (λ _ _, True)).
  { split; eauto. }

  clear Heql lsuf.

  intros iter ? lsuf IH [-> (lpref & Heql & HIpre)].
  (* Need to do better. TODO replace with [pure_enter_anonfun]. *)
  pure_simp. pure_enter.

  eapply pure_eval_match. { pure_path. }
  pure_match.

  { pure_const. by rewrite app_nil_r. }

  eapply pure_eval_seq_exn.
  eapply pure_eval_app. pure_path. pure_path.
  intros ? ? -> ->.
  eapply pure_mono.

  { simpl. eapply Hf.
    - rewrite (cons_middle _ lpref xs'). apply prefix_app.
      rewrite <- (app_nil_r [x]) at 1. apply prefix_app.
      apply prefix_nil.
    - apply HIpre. }

  (* TODO: Clean up this portion. *)
  { cbn. intros _ ?; subst. fold eval.
    eapply pure_eval_app; [ | pure_path | ].
    { eapply pure_eval_app; try pure_path.
      intros ? ? -> ->.
      eapply IH with (y2 := xs').
      - simpl; eauto.
      - done.
      - split; first done.
        exists (lpref ++ [x]). split; last done.
        rewrite (cons_middle x lpref xs'). by rewrite app_assoc. }
    intros ? ? Hcall ->.
    eapply Hcall. }

  { cbn. intros ? (?&?). split; eauto.
    exists lpref. split; first assumption. rewrite <- (app_nil_r lpref) at 1.
    apply prefix_app. apply prefix_nil. }
Qed.

End pure_proof.
