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
      (λ h, ∃ t, l = h :: t)
      (λ e, e = VXData (Loc 0) [VTuple []] ∧ l = []).

(* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
   or returns [None] when [l = []]. *)

Definition catch_head_spec catch_head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    total
      (call catch_head #l)
      (λ hopt, hopt = list.head l).

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
    (* pure_simp. *)
    unfold head_spec; intros.

    (* in both cases, the expr [simp]lifies to a value or exception *)
    destruct l.
    - pure_simp. apply pure_throw. auto.
    - pure_simp. apply pure_ret. eauto with encode.
  }
  intros [??] (head & Hhead & -> & ->); simpl.

  (* Struct item: [let cath_head l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    pure_enter.
    eapply pure_eval_match'_exn.
    - pure_simp. apply Hhead.
    - intros h (t & ->). pure_simp. reflexivity.
    - intros e (-> & ->). pure_simp. reflexivity.
  }
  intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

  (* Struct item: [let catch_head2 l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    pure_enter.
    eapply (pure_eval_trywith _ _ _ _ (λ ex, l = [] ∧ ex = VXData (Loc 0) (VTuple []))).
    - (* matched value (or exn) *)
      eapply pure_eval_data1, pure_eval_app_conseq.
      + set_pure_postcondition ##(λ a, a = head).
        eapply pure_noexn_weaken. (* remove after adapting pure_path to exn *)
        pure_path.
        auto.
      + set_pure_postcondition ##(λ a, a = l).
        eapply pure_noexn_weaken. (* remove after adapting pure_path to exn *)
        pure_path.
        auto.
      + intros ? ? -> ->.
        eapply pure_mono. apply Hhead.
        * intros ? (h&->&t&->). eauto 20 with encode.
        * intros ? (->&->). auto.

      Unshelve. constructor.
    - intros ex (-> & ->).
      apply pure_eval_try_with_cons, pat_PXData_eq; auto.
      apply pat_PTuple_val, pure_noexn_weaken, pats_PNil.
      eapply pure_eval_const; eauto with encode.
  }
  intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

  (* We have gone though all of the struct items, time to conclude. *)
  eapply structs_nil.
  done.
Qed.
