(** This file contains both a "pure" and "effectful" proof of exceptions.v, to guide the
   generalization of lemmas about [pure] to non-trivial exceptional postconditions.  *)

From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_exception.

Definition stdlib_with_notfound :=
  ("Not_found", (VLoc (Loc 0))) :: stdlib_env.

Section proof_pure.

  Variable A : Type.
  Hypothesis HA : Encode A.

  (* Calling [head #l] either returns [#h] when [l = h :: t],
     or throws an exception when [l = []]. *)

  Definition head_spec (l : list A) m :=
    pure m
      (λ h : A, exists t, l = h :: t)
      (λ e, e = VXData (Loc 0) [] ∧ l = []).

  (* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
     or returns [None] when [l = []]. *)

  Definition catch_head_spec (l : list A) (m : microvx) :=
    pure m (λ hopt, hopt = list.head l) ⊥.

  Lemma example :
    eval_module stdlib_with_notfound __main (λ η, True).
  Proof.
    unfold __main.
    apply module_struct.

    (* Struct item: [let head l = ...] *)
    eapply structs_cons.
    apply struct_let_single.
    apply (pure_eval_anon τ[list A]) with (P := head_spec).
    { simpl; unfold head_spec; fold eval.
      intros l.
      eapply pure_eval_match. { pure_path. }
      pure_match.

      { (* Case: the list is empty *)
        apply pure_eval_raise.
        simpl_eval. (* FIXME. *)
        pure_ret. }

      { (* Case: the list has a head *)
        pure_path. } }

    intros [??] (head & Hhead & -> & ->); simpl.

    (* Struct item: [let catch_head l = ...] *)
    eapply structs_cons.
    apply struct_let_single.
    apply (pure_eval_anon τ[list A]) with (P := catch_head_spec).
    { simpl; unfold catch_head_spec; fold eval.
      intros l.
      eapply pure_eval_match'_exn.
      { (* Evaluate the scrutinee [head l] *)
        eapply (pure_EApp τ[list A]). pure_path. pure_path. apply eq_refl.
        intros l' <- m Hm. apply Hm. }

      { (* Case: the call to [head] returned a value *)
        intros x [t ->].
        pure_match. pure_data. }

      { (* Case: the call to [head] raised an exception *)
        intros e [-> ->].
        pure_match. pure_const. reflexivity. } }

    intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

    (* Struct item: [let catch_head2 l = ...] *)
    eapply structs_cons.
    apply struct_let_single.
    apply (pure_eval_anon τ[list A]) with (P := catch_head_spec).
    { simpl; unfold catch_head_spec; fold eval.
      intros l.

      eapply pure_eval_match'_exn.
      { (* Evaluate the scrutinee [Some (head l)] *)
        eapply pure_eval_data. eapply pure_evals_singleton.
        eapply (pure_EApp τ[list A]). pure_path. pure_path. apply eq_refl.
        intros ? <- m Hm.
        eapply pure_ret_mono; first apply Hm.
        { intros x [t ->].
          exists (Some x). split; [ encode | ].
          instantiate (1 := (λ v, ∃ x t, l = x :: t ∧ v = Some x)).
          eexists _, _; split; reflexivity. } }

      { (* Case: the call to [head] returned a value *)
        intros o Ho. pure_match. pure_path.
        by destruct Ho as (x & t & -> & ->). }

      { (* Case: the call to [head] raised an exception *)
        intros e [-> ->].
        pure_match. pure_const. done. } }

    intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

    (* We have gone though all of the struct items, time to conclude. *)
    finished_struct.
    done.
  Qed.

End proof_pure.
