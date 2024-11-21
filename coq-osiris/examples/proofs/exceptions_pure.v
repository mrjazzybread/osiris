(* This file is a "pure mode" version of exceptions.v, to guide the
generalization of lemmas about [pure] to non-trivial exceptional postconditions,
but one should be aware that the current version of exceptions.v is old and
should not be considered idiomatic (for this see iter.v instead).

TODO: avoid [simp] at least when [eval ...] does not reduce to a value / exn *)

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_exception.

Definition stdlib_with_notfound :=
  ("Not_found", (VLoc (Loc 0))) :: stdlib_env.

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
    total
      (call catch_head #l)
      (λ hopt, hopt = list.head l).

(* TODO: MOVE? *)
Ltac set_pure_postcondition φ :=
  match goal with
    |- @pure ?A ?E ?m ?_φ ?ψ =>
      let H := fresh in
      cut (@pure A E m φ ψ); [ intro H; exact H | ]
  end.

(* TODO MOVE *)
Local Lemma pure_wp_evals_eq `{Encode A} η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (λ x : A, # x = v) ψ) es vs →
  pure_wp (evals η es) (λ x, x = vs) ψ.
Proof.
  revert vs.
  induction es as [ | e es IHes]; intros vs' Hes; simpl_evals.
  - constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (v & vs & He & Hes & ->).
    eapply pure_wp_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros _ _ (?&->&->) ->. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.

Lemma pure_evals_eq `{Encode A} η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (λ x : A, # x = v) ψ) es vs →
  pure (evals η es) (λ x, x = vs) ψ.
Proof.
  apply pure_wp_evals_eq.
Qed.

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
    - eapply pure_eval_app. pure_path. pure_path.
    - intros h (t & ?). pure_simp.
      destruct l; inv H0; eauto.
    - intros e (-> & ->). pure_simp. reflexivity.
  }
  intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

  (* Struct item: [let catch_head2 l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    pure_enter.
    eapply (pure_eval_trywith _ _ _ _ (λ ex, l = [] ∧ ex = VXData (Loc 0) [])).
    - (* matched value (or exn) *)
      eapply pure_mono.
      eapply (@pure_eval_data' A _ (option A)).
      (* TODO: fix [pure_data] -- START *)
      + eapply pure_wp_mono_ret.
        { eapply (@pure_evals_eq A).
          eapply List.Forall2_cons; eauto.
          (* fix [pure_data] -- END *)
          eapply pure_eval_app. pure_path.
          pure_path; first encode.
          eapply pure_strong_mono.
          eapply Hhead.
          - intros ? (h&?); destruct l; inversion H0.
            (* FIXME Automate; this shouldn't happen here. *)
            Unshelve. 4 : { exact (match l with
                                    | nil => #(@None A)
                                    | hd :: tl => #hd end). }
            cbn. reflexivity. shelve. exact (List.head l).
          - intros ? (->&->). auto. }

        intros ex ?. cbn in *. subst.
        eexists _. split; eauto. encode.
  (*       eauto with returns. *)
  (*   cbn in *. subst. destruct l; eauto; cbn; eauto. *)
  (*   apply pure_eval_try_with_cons, pat_PXData_eq; auto. *)
  (*   apply pat_PTuple_val, pure_noexn_weaken, pats_PNil. *)
  (*   eapply pure_eval_const; eauto with encode. *)
  (* } *)
  (* intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl. *)

  (* (* We have gone though all of the struct items, time to conclude. *) *)
  (* eapply structs_nil. *)
  (* done. *)
Admitted.
