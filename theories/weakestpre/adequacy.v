From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import safe wp.

(* This module proves the adequacy (i.e. the soundness) of our logic. *)

(* ------------------------------------------------------------------------ *)

(* Boilerplate. *)

(* It would be nice if someone could explain to me what this means. *)

Class osirisPre Σ := OsirisPre {

  (* This gives us fancy updates. *)
  osiris_invGpreS  :> invGpreS Σ;

  (* This gives us a heap, which maps locations to values. *)
  osiris_heapGpreS :> gen_heapGpreS loc val Σ;

}.

(* This is our closed-world Σ. *)

Local Definition osirisΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc val].

(* These instance declarations are (implicitly) used in the proof of the
   adequacy lemma that follows. *)

Local Instance subG_osirisPre {Σ} :
  subG osirisΣ Σ -> osirisPre Σ.
Proof. solve_inG. Qed.

Local Instance osirisPre_osirisΣ : osirisPre osirisΣ.
Proof. eauto with typeclass_instances. Qed.

(* ------------------------------------------------------------------------ *)

(* A first adequacy lemma. *)

Lemma preliminary_adequacy_open
  {A} Σ `{!osirisPre Σ} s (m : free A) (φ : A → Prop) :
  (∀ `{!osirisGS_gen Σ}, ⊢ WP m @ s; ⊤ {{ a, ⌜ φ a ⌝ }}) ->
  safe (∅, m) (λ _ a, φ a).
Proof.
  intros Hwp.
Abort.
