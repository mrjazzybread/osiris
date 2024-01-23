From osiris.lang Require Import lang.
From osiris Require Import base.
From osiris.semantics Require Import code eval step.
From stdpp Require Import relations.

(* This file defines the relations [steps] and [produces]
   and establishes some of their properties. *)

(* TODO remove; just use [nsteps] from stdpp everywhere *)

(* -------------------------------------------------------------------------- *)

(* [steps n m m'] means that [m] reduces to [m'] in at most [n] steps. *)

Inductive steps {A E} : nat → config A E → config A E → Prop :=
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

(* [produces n m a] means that [m] reduces to [Ret a] in at most [n] steps. *)

Definition produces {A E} n (m : micro A E) σ a :=
  steps n (σ, m) (σ, Ret a).

Global Hint Unfold produces : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [produces]. *)

(* [step] and [produces] can be composed. *)

Lemma step_produces {A E} n (m m' : micro A E) σ a :
  step (σ, m) (σ, m') →
  produces n m' σ a →
  produces (S n) m σ a.
Proof.
  unfold produces. eauto with steps.
Qed.

Global Hint Resolve step_produces : steps.

(* -------------------------------------------------------------------------- *)

(* Inversion lemma. *) (* TODO remove *)

Lemma nsteps_S_inv {T} R n (e e' : T) :
  nsteps R (S n) e e' → ∃ e'', R e e'' ∧ nsteps R n e'' e'.
Proof. inversion_clear 1. eauto. Qed.

(* -------------------------------------------------------------------------- *)

(* Relation between [steps] and its stdpp version ([nsteps]). *)

Lemma steps_nsteps {A E n} :
  forall {σ1 σn} {m1 mn : micro A E},
  steps n (σ1, m1) (σn, mn) → ∃ n', nsteps step n' (σ1, m1) (σn, mn).
Proof.
  induction n as [|n IHn] => σ1 σn m1 mn Hsteps.

  (* Base case. *)
  { inversion Hsteps. eexists; apply nsteps_O. }

  (* Inductive case. *)
  { inversion Hsteps; simplify_eq/=.

    (* No step has been taken. *)
    { eexists; apply nsteps_O. }

    (* At least one step has been taken. *)
    { destruct m2 as [σn' mn'].
      pose proof (IHn _ _ _ _ H1) as [n' Hn'].
      exists (S n').
      by apply nsteps_l with (σn', mn'). } }
Qed.
