Require Import lang monads free eval step safe spec safety handle.

(* This file establishes the equality [handle m = safety m]. *)

(* Thus, the notion of safety that arises out of the ample-step semantics
   (step.v, safe.v) is the same as the one that arises by going from the
   [free] monad through [handle] to the [spec] monad. *)

(* ------------------------------------------------------------------------ *)

(* The following notation is required for the following statement to be
   type-checked by Coq. Otherwise, the type-checker enters an infinite
   loop. *)

(* TODO can this be fixed? *)

Local Notation handle :=
  (@handle spec _ _ _ _).
Local Notation handle_body :=
  (@handle_body spec).

(* -------------------------------------------------------------------------- *)

(* [handle] is sound. *)

(* The property [handle m ∋ φ] is preserved by reduction of [m] to [m']. *)

(* This is a subject reduction property. *)

Lemma handle_preservation {A} (m m' : free A) φ :
  handle m ∋ φ →
  step m m' →
  handle m' ∋ φ.
Proof.
  intros Hmφ Hstep.
  (* [Ret], [Next], [Fail] cannot step. *)
  destruct m; try solve [ simpl in Hstep; tauto ].
  (* Case: [Stop]. *)
  { rewrite handle_stop in Hmφ.
    rewrite step_stop in Hstep. subst m'.
    rewrite unfold_skip in Hmφ.
    assumption. }
  (* Case: [Flip]. *)
  { rewrite handle_flip in Hmφ.
    (* This is where we exploit the fact that [mflip] in the [spec] monad
       expands to a universal quantifier. *)
    simpl in Hmφ.
    rewrite step_flip in Hstep.
    destruct Hstep; subst m'; eauto. }
Qed.

(* The property [handle m ∋ φ] guarantees that [m] is not stuck. *)

(* This is a progress property. *)

Lemma handle_progress {A} (m : free A) φ :
  handle m ∋ φ →
  stuck m →
  False.
Proof.
  intros Hmφ Hstuck.
  destruct m.
  { eauto using invert_stuck_answer with is_answer. }
  { rewrite handle_fail in Hmφ.
    rewrite unfold_spec_mzero in Hmφ.
    tauto. }
  { rewrite handle_next in Hmφ.
    rewrite unfold_spec_mzero in Hmφ.
    tauto. }
  { eauto using invert_stuck_stop. }
  { eauto using invert_stuck_flip. }
Qed.

(* From the previous two results, we deduce that if [handle m ∋ φ] holds
   then [m] is safe with respect to [φ]. We first prove that this holds
   for [n] steps, by induction on [n]. The result follows. *)

Lemma handle_sound_aux {A} :
  ∀ n (m : free A) φ,
  handle m ∋ φ →
  initially_safe n m φ.
Proof.
  (* Reason by induction over [n]. *)
  induction n; [ simpl; tauto |].
  intros m φ Hmφ.
  rewrite unfold_initially_safe_S.
  triplicity m Hm.

  (* Case: [m] is a result. *)
  { destruct_answer.
    (* Sub-case: [m] is [ret a]. *)
    { left. eexists. split; [ eauto |].
      rewrite handle_ret in Hmφ.
      rewrite unfold_spec_ret in Hmφ.
      assumption. }
    (* Sub-case: [m] is [Next]. *)
    { rewrite handle_next in Hmφ. rewrite unfold_spec_mzero in Hmφ. tauto. }
  }

  (* Case: [m] steps. *)
  { right. split; [ eauto |].
    intros m' Hstep.
    eapply IHn; clear IHn.
    eauto using handle_preservation. }

  (* Case: [m] is stuck. *)
  { false. eauto using handle_progress. }

Qed.

Lemma handle_sound {A} (m : free A) (φ : A → Prop) :
  handle m ∋ φ →
  safe m φ.
Proof.
  unfold safe. eauto using handle_sound_aux.
Qed.

(* -------------------------------------------------------------------------- *)

(* [handle] is complete. *)

Section ImportNotations.

Set Warnings "-notation-overridden".
Import spec.Notations.

(* This cryptic lemma is an unfolded version of the lemma that follows.
   It states, roughly, that safety with respect to φ is preserved by
   [handle_body]. It is trivial. *)

Lemma safety_preservation_aux {A} (m : free A) φ :
  safe m φ →
  handle_body m ∋ spec_iter_body_post safety φ.
Proof.
  intros Hsafe.
  destruct m; simpl.
  { rewrite safe_ret in Hsafe. tauto. }
  { rewrite safe_stuck in Hsafe by apply stuck_Fail. tauto. }
  { eauto using invert_safe_next. }
  { eapply invert_safe_step; eauto with step. }
  { intro b. eapply invert_safe_step; eauto with step. }
Qed.

Lemma safety_preservation {A} :
  @safety A ≼ spec_iter_body handle_body safety.
Proof.
  intros m φ. rewrite unfold_safety.
  rewrite unfold_spec_iter_body.
  apply safety_preservation_aux.
Qed.

(* If [m] is safe with respect to [φ] then [handle m ∋ φ] holds. *)

Lemma handle_complete {A} (m : free A) (φ : A → Prop) :
  safe m φ →
  handle m ∋ φ.
Proof.
  intros Hsafe.
  unfold handle.
  (* To establish the goal [iter handle_body m ∋ φ], by definition of
     [iter], we must exhibit a loop invariant. Fortunately, we do have
     a loop invariant: it is the safety of [m]. *)
  erewrite unfold_spec_iter_preliminary by typeclasses eauto.
  exists safety.
  split.
  (* Safety holds initially. *)
  { rewrite unfold_safety. assumption. }
  (* Safety is preserved. *)
  { apply safety_preservation. }
Qed.

End ImportNotations.

(* -------------------------------------------------------------------------- *)

(* The soundness and completeness results can be summed up as follows. *)

Lemma handle_safety {A} (m : free A) :
  handle m = safety m.
Proof.
  eapply prove_spec_eq_ext. intros φ.
  rewrite unfold_safety.
  split; eauto using handle_sound, handle_complete.
Qed.
