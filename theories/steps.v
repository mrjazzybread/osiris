Require Import lang base free eval step.

(* This file defines the relations [steps] and [produces]
   and establishes some of their properties. *)

(* -------------------------------------------------------------------------- *)

(* [steps n m m'] means that [m] reduces to [m'] in at most [n] steps. *)

Inductive steps {A} : nat → free A → free A → Prop :=
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

Lemma one_step {A} (m m' : free A) :
  step m m' →
  steps 1 m m'.
Proof.
  eauto with steps.
Qed.

(* [steps] is monotonic in [n]. *)

Lemma steps_monotonic {A} :
  ∀ n (m m' : free A),
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
  ∀ n1 (m1 m2 : free A),
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

(* [steps] can be taken under a [Par] constructor. *)

Lemma steps_par_left :
  ∀ {A1 A2 A} n m1 m'1,
  steps n m1 m'1 →
  ∀ m2 (k : A1 * A2 → free A) ko,
  steps n (Par m1 m2 k ko) (Par m'1 m2 k ko).
Proof.
  induction n; intros m1 m'1 Hsteps;
  dependent destruction Hsteps;
  eauto with step steps.
Qed.

Lemma steps_par_right :
  ∀ {A1 A2 A} n m2 m'2,
  steps n m2 m'2 →
  ∀ m1 (k : A1 * A2 → free A) ko,
  steps n (Par m1 m2 k ko) (Par m1 m'2 k ko).
Proof.
  induction n; intros m2 m'2 Hsteps;
  dependent destruction Hsteps;
  eauto with step steps.
Qed.

(* -------------------------------------------------------------------------- *)

(* [produces n m a] means that [m] reduces to [Ret a] in at most [n] steps. *)

Definition produces {A} n (m : free A) (a : A) :=
  steps n m (Ret a).

Global Hint Unfold produces : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [produces]. *)

(* [step] and [produces] can be composed. *)

Lemma step_produces {A} n (m m' : free A) a :
  step m m' →
  produces n m' a →
  produces (S n) m a.
Proof.
  unfold produces. eauto with steps.
Qed.

Global Hint Resolve step_produces : steps.
