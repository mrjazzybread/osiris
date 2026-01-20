From stdpp Require Import relations.
From osiris Require Import base.
From osiris.semantics Require Import code pure step.

(* This file exists to back up claims from the paper, it is not used by the rest
of the repository, so lemmas are prefixed with 'Local' *)

(** Characterization of the "pure step" relation (called [may] in this
repository) in terms of the normal step relation *)

(** [ipure m] means that [m] is immediately pure, i.e. no impure [Stop] appears
at toplevel *)

Inductive ipure : forall {A E}, micro A E → Prop :=
  | ipure_crash A E : @ipure A E Crash (* proofs work with or without this line  *)
  | ipure_ret A E v : @ipure A E (Ret v)
  | ipure_throw A E e : @ipure A E (Throw e)
  | ipure_handle A E m (h : _ → micro A E) : ipure m → ipure (Handle m h)
  | ipure_eval A E x k : @ipure A E (Stop CEval x k)
  | ipure_loop A E x k : @ipure A E (Stop CLoop x k)
  | ipure_flip A E x k : @ipure A E (Stop CFlip x k)
  | ipure_par A E A1 A2 E' (k : outcome2 (A1 * A2) E' → micro A E) m1 m2 :
    ipure m1 → ipure m2 → ipure (Par m1 m2 k).

(** For pure computations [may m m'] is equivalent to [∀ σ  (σ, m) → (σ, m')] *)

Ltac inv_ipure :=
  match goal with
  | h: ipure (Stop CPerf _ _) |- _ => inv h
  | h: ipure (Stop CFork _ _) |- _ => inv h
  | h: ipure (Stop CJoin _ _) |- _ => inv h
  | h: ipure (Stop CSelf _ _) |- _ => inv h
  end.

Local Lemma may_pure_step {A E} (m : micro A E) :
  ipure m ->
  ∀ m', may m m' <-> forall σ, step (σ, m) (σ, m').
Proof.
  intros P; split; intros S.
  - induction S; intros σ; try constructor; invdep P; auto.
  - specialize (S ∅).
    remember (∅, m) as c.
    remember (∅, m') as c'.
    revert m m' Heqc Heqc' P.
    induction S; intros m_ m_' [= -> <-] [= TEST] P; subst; invdep P; try constructor; eauto.
    (* [Stop CFlip] *)
    destruct b; constructor.
    (* [fork], [join], and [perform] under [Par] and [Handle]. *)
    all: try inv_ipure.
    destruct c; try contradiction H; try inv_ipure.
    destruct c; try contradiction H; try inv_ipure.
Qed.

(** For pure computations [may m m'] is equivalent to [∃ σ  (σ, m) → (σ, m')] *)

Local Lemma may_pure_step' {A E} (m : micro A E) :
  ipure m ->
  ∀ m', may m m' <-> exists σ, step (σ, m) (σ, m').
Proof.
  intros P; split; intros S.
  - exists ∅; induction S; try constructor; invdep P; eauto.
  - destruct S as (σ, S).
    remember (σ, m) as c.
    remember (σ, m') as c'.
    revert σ m m' Heqc Heqc' P.
    induction S; intros σ_ m_ m_' [= -> <-] [= TEST] P; subst; invdep P; try constructor; eauto;
      first (destruct b; constructor);
      try inv_ipure.
    destruct c; try contradiction H; try inv_ipure.
    destruct c; try contradiction H; try inv_ipure.
Qed.

Local Lemma ipure_dec {A E} (m : micro A E) : ipure m ∨ ~ipure m.
Proof.
  induction m.
  all: try solve [repeat constructor | right; intros P; inv P].
  - destruct IHm. repeat constructor; auto. right; intros P; inv P. auto.
  - destruct c; solve [repeat constructor] || right; intros P; inv P.
  - destruct IHm1, IHm2. repeat constructor; auto.
    all: right; intros P; invdep P; auto.
Qed.

(** Non-immediately-pure computations can reduce to [Crash] *)

Local Lemma not_ipure_crash {A E} (m : micro A E) : ~ipure m → rtc may m (Crash).
Proof.
  induction m; intros N.
  - destruct N. constructor.
  - destruct N. constructor.
  - constructor.
  - ospecialize (IHm _). by intros P; destruct N; constructor.
    apply rtc_r with (Handle (Crash) h). 2:constructor.
    clear -IHm. induction IHm; econstructor; eauto with may.
  - destruct c.
    all: try (destruct N; constructor).
    all: apply rtc_once; destruct x; constructor.
  - destruct (ipure_dec m1) as [P1 | N1].
    + destruct (ipure_dec m2) as [P2 | N2].
      * destruct N; constructor; auto.
      * specialize (IHm2 N2).
        apply rtc_r with (Par m1 (Crash) k). 2:constructor.
        clear -IHm2. induction IHm2; econstructor; eauto with may.
    + specialize (IHm1 N1).
      apply rtc_r with (Par (Crash) m2 k). 2:constructor.
      clear -IHm1. induction IHm1; econstructor; eauto with may.
Qed.
