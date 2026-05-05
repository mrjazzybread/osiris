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

  Lemma let_fun τ P η δ x e f sitems φ :
    predicate_over_function_body τ P η (EAnonFun (Anon (x => e))) ->
    (∀ c, Spec τ c P -> struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
    struct_items (η, δ) ((ILet [Binding (PVar f) (EAnonFun (AnonFun x e))]) :: sitems) φ.
  Proof.
    intros Hpred Hmono.
    eapply structs_cons.
    { apply struct_let_single.
      apply pure_eval_anon. apply Hpred. }
    intros [η' δ'] (clo & HSpec & -> & ->).
    apply Hmono, HSpec.
  Qed.

  Lemma example :
    eval_module stdlib_with_notfound __main (λ η, True).
  Proof.
    unfold __main.
    apply module_struct.

    (* Struct item: [let head l = ...] *)
    apply (let_fun τ[list A] head_spec).
    { simpl; fold eval.
      unfold head_spec; intros l.
      apply pure_please_eval.
      eapply pure_eval_match. { pure_path. }
      pure_match.
      - eapply pure_eval_raise.
        simpl_eval. rewrite !bind_ret. pure_ret.
      - pure_path. eauto. }
    intros head Hhead.

    (* Struct item: [let catch_head l = ...] *)
    apply (let_fun τ[list A] catch_head_spec).
    { simpl; fold eval.
      unfold catch_head_spec; intros l.
      change encode_list with (@encode.encode (list A) _).
      apply pure_please_eval.
      eapply pure_eval_match'_exn.
      - eapply (pure_EApp τ[list A]).
        { pure_path. rewrite <- solve_encode_val. reflexivity. eassumption. }
        { pure_path. apply eq_refl. }
        simpl.
        intros l' <- m Hm. apply Hm.
      - intros h (t & ->). pure_match.
        apply pure_eval_data. eapply pure_evals_cons.
        pure_path. apply pure_evals_nil. encode.
      - intros e (-> & ->). pure_match.
        eapply pure_eval_const. encode. reflexivity. }
    intros catch_head Hcatch_head.

    (* Struct item: [let catch_head2 l = ...] *)
    apply (let_fun τ[list A] catch_head_spec).
    { simpl; fold eval.
      unfold catch_head_spec; intros l.
      apply pure_please_eval.
      eapply pure_eval_match'_exn.
      { eapply pure_eval_data. eapply pure_evals_cons.
        eapply (pure_EApp τ[list A]). pure_path. pure_path; apply eq_refl.
        simpl.
        intros ? <- m Hm.
        eapply pure_ret_mono; [ apply Hm | intros a (t & Ht) ]; fold evals.
        apply pure_evals_nil.
        instantiate (4 := (option A)).
        exists (Some a). split; [ encode | ].
        instantiate (1 := fun v => ∃ a t, l = a :: t ∧ v = Some a).
        exists a, t; done. }
      - intros o (a & t & -> & ->).
        pure_match. pure_path.
      - intros e (-> & ->).
        pure_match. pure_const. reflexivity. }

    intros catch_head2 Hcatch_head2.

    (* We have gone though all of the struct items, time to conclude. *)
    finished_struct.
    done.
  Qed.

End proof_pure.
