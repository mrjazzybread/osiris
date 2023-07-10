From osiris.lang Require Import lang.
From osiris Require Import base.
From osiris.semantics Require Import code eval step.
From stdpp Require Import relations.

(* This file defines the relations [steps] and [produces]
   and establishes some of their properties. *)

(* -------------------------------------------------------------------------- *)

(* [steps n m m'] means that [m] reduces to [m'] in at most [n] steps. *)

Inductive steps {A} : nat → config A → config A → Prop :=
| StepsZero:
    ∀ n m,
    steps n m m
| StepsSucc:
    ∀ n m1 m2 m3,
    step m1 m2 →
    steps n m2 m3 →
    steps (S n) m1 m3.

Global Hint Constructors steps : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [steps]. *)

(* [step] implies [steps 1]. *)

Lemma one_step {A} (m m' : config A) :
  step m m' →
  steps 1 m m'.
Proof.
  eauto with steps.
Qed.

(* [steps] is monotonic in [n]. *)

Lemma steps_monotonic {A} :
  ∀ n (m m' : config A),
  steps n m m' →
  ∀ n',
  n ≤ n' →
  steps n' m m'.
Proof.
  induction 1; intros.
  { eauto with steps. }
  { destruct n'; [ lia |]. eauto with lia steps. }
Qed.

(* [steps] is transitive. *)

Lemma steps_transitive {A} :
  ∀ n1 (m1 m2 : config A),
  steps n1 m1 m2 →
  ∀ n2 m3,
  steps n2 m2 m3 →
  steps (n1 + n2) m1 m3.
Proof.
  induction 1; intros; simpl.
  (* Base case. *)
  { eauto using steps_monotonic with lia. }
  (* Step case. *)
  { eauto with steps. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [produces n m a] means that [m] reduces to [Ret a] in at most [n] steps. *)

Definition produces {A} n (m : free A) σ (a : A) :=
  steps n (σ, m) (σ, Ret a).

Global Hint Unfold produces : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [produces]. *)

(* [step] and [produces] can be composed. *)

Lemma step_produces {A} n (m m' : free A) σ a :
  step (σ, m) (σ, m') →
  produces n m' σ a →
  produces (S n) m σ a.
Proof.
  unfold produces. eauto with steps.
Qed.

Global Hint Resolve step_produces : steps.

(* -------------------------------------------------------------------------- *)

(* Inversion lemma. *)

Lemma nsteps_S_inv {T} R n (e e' : T) :
  nsteps R (S n) e e' → ∃ e'', R e e'' ∧ nsteps R n e'' e'.
Proof. inversion_clear 1. eauto. Qed.
