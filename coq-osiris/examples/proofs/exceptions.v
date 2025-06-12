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

  (* Calling [head #l] either returns [#h] when [l = h :: t],
    or throws an exception when [l = []]. *)

  Definition head_spec head :=
    ∀ (A : Type) (H : Encode A) (l : list A),
      pure
        (call head #l)
        (λ h : A, exists t, l = h :: t)
        (λ e, e = VXData (Loc 0) [] ∧ l = []).

  (* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
    or returns [None] when [l = []]. *)

  Definition catch_head_spec catch_head :=
    ∀ (A : Type) (H : Encode A) (l : list A),
      pure
        (call catch_head #l)
        (λ hopt, hopt = list.head l) ⊥.

  (* TODO: MOVE? *)
  Ltac set_pure_postcondition φ :=
    match goal with
      |- @pure ?A ?E ?m ?_φ ?ψ =>
        let H := fresh in
        cut (@pure A E m φ ψ); [ intro H; exact H | ]
    end.

  Lemma example :
    eval_module stdlib_with_notfound __main (λ η, True).
  Proof.
    unfold __main.
    apply module_struct.

    (* Struct item: [let head l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := head_spec).
      pure_simp; unfold head_spec; intros.

      (* in both cases, the expr [simp]lifies to a value or exception *)
      destruct l.
      - eapply pure_wp_simp; first by simp_really. apply pure_wp_throw.
        split; eauto.
      - pure_simp. }
    intros [??] (head & Hhead & -> & ->); simpl.

    (* Struct item: [let catch_head l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := catch_head_spec).
      pure_simp; unfold catch_head_spec; intros.
      pure_enter.
      eapply pure_eval_match'_exn.
      - eapply pure_simp. simp. apply Hhead.
      - intros h (t & ->). pure_simp.
      - intros e (-> & ->). pure_simp. }
    intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

    (* Struct item: [let catch_head2 l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := catch_head_spec).
      pure_simp; unfold catch_head_spec; intros.
      pure_enter.
      (* FIXME: This proof was not so pretty to begin with; but
      we can do better here. *)
      (* TODO: Refactor. *)
      eapply pure_eval_match'_exn with (φ' := λ a, a = #(list.head l)) (ζ := λ e, l = [] ∧ e = VXData (Loc 0) []).
      { eapply pure_eval_data_val; last done.
        simpl_evals. fold eval. eapply pure_wp_Par_conseq.
        + eapply pure_eval_app. pure_path. pure_path.
          unfold head_spec in Hhead.
          intros ?? <- ->. apply Hhead.
        + eapply pure_wp_ret_singleton.
        + intros; returns_eauto. cbn in *.
          eapply pure_wp_ret. destruct Ha_ensures; subst.
          red in H1; subst. encode.
        + intros ? [ (-> & ->)| ]; cbn.
          * eapply pure_wp_throw; eauto.
          * Unshelve.
            2 : { apply (λ e, l = [] ∧ e = VXData (Loc 0) []). }
            eapply pure_wp_throw; eauto. }
      { intros ? ->.
        pure_match.
        pure_path. }
      { intros ? [-> ->]. pure_match. pure_simp. } }

    intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

    (* We have gone though all of the struct items, time to conclude. *)
    eapply structs_nil.
    done.
  Qed.

End proof_pure.

Section proof_effectful.

  Context `{!osirisGS Σ}.

  (* Calling [head #l] either returns [#h] when [l = h :: t],
    or throws an exception when [l = []]. *)

  Definition head_eff_spec head :=
    ∀ (A : Type) (H : Encode A) (l : list A),
      ⊢ ewp_def top (call head #l) ⊥
        ( RET x => ∃ h t, ⌜l = h :: t /\ x = #h⌝
        | EXN e => ⌜e = VXData (Loc 0) [] /\ l = []⌝ )%I.

  (* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
    or returns [None] when [l = []]. *)

  Definition catch_head_eff_spec catch_head :=
    ∀ (A : Type) (H : Encode A) (l : list A),
      ⊢ ewp_def top (call catch_head #l) ⊥
        (ensures #hopt, ⌜match l with
                         | [] => hopt = None
                         | h :: _ => hopt = Some h
                         end⌝)%I.

  Lemma example_eff :
    eval_module stdlib_with_notfound __main (λ η, True).
  Proof.
    unfold __main.
    apply module_struct.

    (* Struct item: [let head l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := head_eff_spec).
      pure_simp; unfold head_eff_spec; intros.
      iIntros.
      destruct l; Simp.
      { iApply ewp_throw. simpl. equality. }
      { Ret. simpl. eauto. } }
    intros [??] (head & Hhead & -> & ->); simpl.

    (* Struct item: [let catch_head l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := catch_head_eff_spec).
      pure_simp; unfold catch_head_eff_spec; intros.
      iIntros. iApply ewp_call_nonrec.
      iModIntro.
      prove_match.
      { (* Call to [head]. *)
        Simp. iApply Hhead. }
      iIntros ([h|e]).
      { (* Value case. *)
        iIntros "(%h0 & %t & -> & ->)".
        iModIntro.
        next_branch.
        next_branch.
        { Simp. iApply ewp_value. simpl.
          iExists (Some h0). equality. } }
      { (* Exception case. *)
        iIntros "[-> ->]".
        next_branch; fold eval.
        iApply ewp_EConstant.
        iExists (None). done. } }

    intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

    (* Struct item: [let catch_head2 l = ...] *)
    eapply structs_cons.
    { apply struct_let_single with (spec := catch_head_eff_spec).
      pure_simp; unfold catch_head_eff_spec; intros.
      iIntros. iApply ewp_call_nonrec.
      iModIntro.
      prove_match.
      { Simp. iApply ewp_bind_exn.
        iApply ewp_mono. { iApply Hhead. }
        iIntros ([ v | ex ]) "Houtcome".
        - simpl.
          iApply (ewp_value _ _ (RET v => bi_pure(_ v) | EXN e => bi_pure(_ e))%I).
          iDestruct "Houtcome" as "(%h & %t & -> & ->)".
          iPureIntro.
          instantiate (1 := (λ v, ∃ h t, l = h :: t ∧ v = (#(Some h)))).
          simpl. eexists; eauto.
        - simpl.
          iDestruct "Houtcome" as "(%Hex & %Hl)".
          iPureIntro.
          instantiate (1 := (λ e, e = VXData {| address := 0 |} [] ∧ l = [])).
          simpl; eauto. }

      iIntros ([h|e]).
      { (* Value case. *)
        iIntros "(%h0 & %t & -> & ->)".
        iModIntro.
        next_branch.
        iApply ewp_EPath. iApply ewp_value. iPureIntro. eauto. }
      { (* Exception case. *)
        iIntros "[-> ->]".
        next_branch. next_branch.
        iApply ewp_EConstant.
        iExists (None). done. } }

    intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

    (* We have gone though all of the struct items, time to conclude. *)
    eapply structs_nil.
    done.
  Qed.

End proof_effectful.
