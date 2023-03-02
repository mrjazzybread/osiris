From ITree Require Import ITree.
Require Import lang monads free eval handle div spec.

(* This file establishes that the [spec] monad offers a sound abstract
   interpretation of the [div] monad. *)

(* A computation [m] is safe with respect to a postcondition [φ] if
   1- [m] does not fail; and 2- if [m] produces a value [v] then [φ v]
   holds. This is a partial correctness interpretation: divergence is
   permitted. *)

(* We first define what it means to be safe for [n] steps. Then, we
   universally quantify over [n]. *)

Fixpoint initially_safe {A} (n : nat) (m : div A) (φ : A → Prop) : Prop :=
  match n, observe m with
  | 0, _ =>
      (* Every computation is safe for zero steps. *)
      True
  | _, RetF v =>
      (* The computation produces a value [v]. *)
      φ v
  | S n, TauF m =>
      (* The computation performs a step and continues. *)
      initially_safe n m φ
  | _, VisF _tt _k =>
      (* The computation fails. *)
      False
  end.

Definition safe {A} (m : div A) (φ : A → Prop) :=
  ∀ n, initially_safe n m φ.

(* TODO it should be possible to give an alternative definition of [safe] as
   a coinductive predicate. Do it and prove the equivalence. *)

(* We now define a relation between a computation [m] in the [div] monad
   and a specification [s] in the [spec] monad. This relation should
   express the soundness of a program logic: that is, if the logic states
   that a postcondition [φ] holds, then the computation actually satisfies
   this postcondition. In other words, [s ∋ φ] implies [safe m φ]. *)
