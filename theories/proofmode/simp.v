From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics evalprime. (* TODO *)
Global Opaque eval. (* TODO *)

(* This file offers lemmas and tactics that help simplify computations,
   that is, solve goals of the form [simp m1 ?m2]. *)

(* Together, these tactics constitute a simple "proof mode" (in other
   words, a Hoare logic) for pure computations, that is, computations
   that are terminating, deterministic, and do not use mutable state. *)

(* -------------------------------------------------------------------------- *)

(* The following lemmas are reasoning rules for goals of the form [simp _ _]. *)

Lemma prove_simp_ret {A} (a1 a2 : A) :
  a1 = a2 →
  simp (ret a1) (ret a2).
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma prove_simp_bind {A B m m' a} {f : A → free B} :
  simp m (ret a) →
  simp (f a) m' →
  simp (bind m f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

Lemma prove_simp_try {A B m m' a} {f : A → free B} ko :
  simp m (ret a) →
  simp (f a) m' →
  simp (try m f ko) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.

Lemma prove_simp_par {A1 A2 A} m1 m2 a1 a2 (k : A1 * A2 → free A) m' ko :
  simp m1 (ret a1) →
  simp m2 (ret a2) →
  simp (k (a1, a2)) m' →
  simp (Par m1 m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

(* TODO decide which reasoning rules should be automatically applied *)

(* -------------------------------------------------------------------------- *)

(* The following lemmas are used by the [simp] tactic. *)

(* They are trivial. They could be replaced by nested applications of
   constructors, possibly complemented with [rewrite] steps. Using lemmas
   is somewhat more robust and should give rise to smaller proof terms. *)

Lemma simp_reflexive {A} (m1 m2 : free A) :
  m1 = m2 →
  simp m1 m2.
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma advance_SimpEval {A} η e (k : val → free A) ko m' :
  simp (try (eval η e) k ko) m' →
  simp (Stop CEval (η, e) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpEvalNext {A} η e (k : val → free A) m' :
  simp (bind (eval η e) k) m' →
  simp (Stop CEval (η, e) k next) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpLoop {A} η x i1 i2 e (k : val → free A) ko m' :
  simp (try (loop η x i1 i2 e) k ko) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpLoopNext {A} η x i1 i2 e (k : val → free A) m' :
  simp (bind (loop η x i1 i2 e) k) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k next) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpParRetRet {A1 A2 A} a1 a2 (k : A1 * A2 → free A) ko m' :
  simp (k (a1, a2)) m' →
  simp (Par (Ret a1) (Ret a2) k ko) m'.
Proof.
  eauto using SimpParRetRet with simp.
Qed.

Lemma advance_SimpParRetLeft {A1 A2 A} a1 m2 (k : A1 * A2 → free A) ko m' :
  simp (try m2 (λ v2, k (a1, v2)) ko) m' →
  simp (Par (Ret a1) m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetRight {A1 A2 A} m1 a2 (k : A1 * A2 → free A) ko m' :
  simp (try m1 (λ v1, k (v1, a2)) ko) m' →
  simp (Par m1 (Ret a2) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetLeftNext {A1 A2 A} a1 m2 (k : A1 * A2 → free A) m' :
  simp (v2 ← m2 ; k (a1, v2)) m' →
  simp (Par (Ret a1) m2 k next) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetLeft.
Qed.

Lemma advance_SimpParRetRightNext {A1 A2 A} m1 a2 (k : A1 * A2 → free A) m' :
  simp (v1 ← m1 ; k (v1, a2)) m' →
  simp (Par m1 (Ret a2) k next) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetRight.
Qed.

Lemma advance_SimpPar {A1 A2 A} m1 m'1 m2 m'2 (k : A1 * A2 → free A) ko m' :
  simp m1 m'1 →
  simp m2 m'2 →
  simp (Par m'1 m'2 k ko) m' →
  simp (Par m1 m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* The tactics [simp0] and [simp1] expect a goal of the form [simp m1 m2].

   They advance this goal by performing simplification steps that lead from
   [m1] to [m'1] and by leaving a residual goal of the form [simp m'1 m2].

   Whereas [simp0] may find zero or more simplification steps, [simp1] must
   find at least one simplification step; otherwise, it fails.

   The term [m1] is expected to be [cbn]-normal already.

   If the goal is changed to [simp m'1 m2] then the term [m'1] is guaranteed
   to be [cbn]-normal. *)

Ltac simp0 :=
  (* We are allowed to perform zero or more steps. *)
  (* Either perform at least one step, or perform zero step. *)
  first [ simp1; simp0 | idtac ]

with simp1 :=
  (* We must perform at least one step. *)
  (* We examine the syntax of [m1], which is why we require [m1] to be
     [cbn]-normal already. *)
  lazymatch goal with |- simp ?m1 _ =>
  lazymatch m1 with
  | ret ?a1 =>
      fail
  | eval ?η ?e =>
      (* Rewrite [eval η e] to [eval' η e] and simplify the latter form
         using [cbn]. This counts as a simplification step, so our duty is
         fulfilled. We are then free to use [simp0] to find zero or more
         further steps. *)
      rewrite eval_eval'; cbn;
      simp0
  | Stop CEval _ _ _ =>
      first [ eapply advance_SimpEvalNext | eapply advance_SimpEval ]; cbn;
      simp0
  | Stop CLoop _ _ _ =>
      first [ eapply advance_SimpLoopNext | eapply advance_SimpLoop ]; cbn;
      simp0
  | Par ?m1l ?m1r ?k ?ko =>
      (* We want to first simplify both sides of the [Par] independently, as
         far as possible; then, if possible, simplify the [Par] combinator
         away and further simplify the result. Three attempts are needed to
         ensure that we make one step of progress in at least one of the
         three subgoals. This should nevertheless be reasonably efficient. *)
      first [
        (* Attempt 1. Make progress on the left-hand side,
           and possibly more progress elsewhere. *)
        eapply advance_SimpPar; [ simp1; close | simp0; close | simp0_par ]
      |
        (* Attempt 2. Make progress on the right-hand side,
           and possibly more progress elsewhere. *)
        eapply advance_SimpPar; [ close | simp1; close | simp0_par ]
      |
        (* Attempt 3. Make progress by eliminating this [Par],
           and possibly more progress thereafter. *)
        simp1_par
      ]
  end end

(* [simp0_par] and [simp1_par] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (Par m1 m2 _ _) _],
   where [m1] and [m2] are [cbn]-normal and cannot be simplified. *)

with simp0_par :=
  first [ simp1_par | idtac ]

with simp1_par :=
  (* Performing at least one simplification step, when the term is a [Par]
     construct, requires applying one of the following rules. *)
  first [
    eapply advance_SimpParRetRet (* maybe a special case of the following *)
  | eapply advance_SimpParRetLeftNext
  | eapply advance_SimpParRetLeft
  | eapply advance_SimpParRetRightNext
  | eapply advance_SimpParRetRight
  ];
  cbn; simp0

(* [close] solves a goal of the form [simp m1 m2] using reflexivity.

   The term [m1] must be [cbn]-normal.

   If reflexivity cannot solve the goal, then [close] fails. *)

with close :=
  solve [ eapply SimpReflexive | eapply simp_reflexive; [ eauto ]].

(* [simp] is the public entry point into the above tactics. *)

(* [simp] proves or advances a goal of the form [simp m1 m2], where [m2] may
   be a metavariable. If [m2] is a metavariable then it is instantiated with
   a [cbn]-normal term. *)

Ltac simp :=
  cbn;
  lazymatch goal with |- simp ?m1 _ =>
    simp0; try close
  | _ =>
    fail "[simp] expects a goal of the form [simp _ _]"
  end.

(* [simp_continue] unfolds [concatenating] in a goal of the form
   [simp (concatenating ...) _], and continues simplifying via [simp]. *)

Ltac simp_continue :=
  cbn;
  lazymatch goal with |- simp (concatenating _ _ _ _) _ =>
    unfold concatenating; (* TODO restrict to head occurrence *)
    cbn;
    simp
  | _ =>
    fail "[simp_continue] expects a goal of the form [simp (concatenating ...) _]"
  end.

(* [simp_enter] expects a goal of the form [simp (call _ _) _] and steps
   into the call. It is normally used at the beginning of the proof of a
   function, that is, when reasoning about a callee. At a call site, it
   is normally not used, unless the user wants to logically inline the
   called function. *)

Ltac simp_enter :=
  with_strategy transparent [call] unfold call; simp.

(* TODO do something about [Stop CFlip _ _] *)
(* TODO simplify [eval η e] even when it is not at the head,
        e.g. [simp (x ← eval η e ; _) _]. *)

(* -------------------------------------------------------------------------- *)
