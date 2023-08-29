From iris.prelude Require Import options.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import base proofmode classes.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe.

(* This file defines the predicate [WP]. *)

(* It is heavily inspired from [iris/{bi,program_logic}/weakestpre.v]. *)

(* -------------------------------------------------------------------------- *)

(* For details about these incantations, see
   [iris.base_logic.lib.fancy_updates] and
   [iris.base_logic.lib.gen_heap]. *)

Class osirisGS (Σ: gFunctors) := OsirisG {

  (* This gives us fancy updates (without allowing Later Credits). *)
  osiris_invGS :> invGS_gen HasNoLc Σ;

  (* This gives us a heap, which maps locations to values. *)
  osiris_heapGS :> gen_heapGS loc val Σ;

}.

(* Definition of the state interpretation predicate. *)

(* For the moment, it is set to [gen_heap_interp σ], which is the standard state
   interpretation of Iris. *)

Definition state_interp {Σ H} (σ : store) :=
  @gen_heap_interp loc _ _ val Σ H σ.

(* -------------------------------------------------------------------------- *)

(* This is the definition of the predicate [WP]. *)

Section definition.

Context (A: Type).
Context `{!osirisGS Σ}.

(* The (open) recursive definition of [wp]. *)

Definition wp_pre
  (s : stuckness)
  (wp: coPset -d> micro A -d> (A -d> iPropO Σ) -d> iPropO Σ) :
       coPset -d> micro A -d> (A -d> iPropO Σ) -d> iPropO Σ
  :=
  λ E m φ,
    (∀ σ,
       (* Give, the state of the heap [σ] and under the modality [|={E,∅}=>], *)
       state_interp σ ={E,∅}=∗
       match is_ret m with
       | Some v =>
           (* If the term is a value, it satisfies the postcondition and the
              state interpretation can be returned after giving back the
              invariants in [E]. *)
           |={∅,E}=> state_interp σ ∗ φ v
       | None =>
           (* Otherwise, the term [m] is not a value. The [wp] states that:
              (1) the configuration [σ, m] is not stuck, and *)
           ⌜can_step (σ, m)⌝ ∗
           (* (2) for any step this configuration can take, the state
                  interpretation can be given back and the [wp] holds.
              Using [ ={∅}▷=∗ ] allows the adequacy theorem to hold. The
              proofs of [theories/program_logic/adequacy.v] use this modality.
              Using [ |={∅, E}=> ] ask invariants in [E] to hold in the
              conclusion. *)
           ∀ σ' m', ⌜step (σ, m) (σ', m')⌝ ={∅}▷=∗
                    |={∅,E}=> (state_interp σ' ∗ wp E m' φ)
     end
    )%I.

Local Instance wp_pre_contractive s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E m Φ.
  repeat (f_contractive || f_equiv).
  apply Hwp.
Qed.

(* The following definition is intended to ensure that the usual Iris
   notation is available, e.g.:
     [WP _ @ _ {{ _ }}]
     [WP _ @ _ ?{{ _ }}]).

  The stuckness bit is not used at the moment. *)

Definition wp_def : Wp (iProp Σ) (micro A) A stuckness :=
  λ (s : stuckness), fixpoint (wp_pre s).

(* Standard boilerplate to seal the definition of [wp]. *)

Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Σ _ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal: wp = wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End definition.

(* -------------------------------------------------------------------------- *)

(* More boilerplate, once again inspired by
   [iris/{bi,program_logic}/weakestpre.v] *)

Section boilerplate.

Context {A : Type}.
Context `{!osirisGS Σ}.
Implicit Type s : stuckness.
Implicit Type P : iProp Σ.
Implicit Type φ : A → iProp Σ.
Implicit Type a : A.
Implicit Type m : micro A.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma wp_unfold {s E} m {φ} :
  WP m @ s; E {{ φ }} ⊣⊢ wp_pre A s (wp s) E m φ.
Proof.
  rewrite wp_unseal.
  apply (@fixpoint_unfold _ _ _ (wp_pre A s)).
Qed.

Local Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

Global Instance wp_ne s E m n :
  Proper
    (pointwise_relation _ (dist n) ==> dist n)
    (wp s E m).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
  wp_unfold_all.
  repeat ((by rewrite IH; [done|lia|];
              intros v; eapply dist_le; [apply HΦ|lia])
          + (f_contractive || f_equiv)).
Qed.

Global Instance wp_proper s E m :
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (wp s E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance wp_contractive s E m n :
  TCEq (is_ret m) None →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (wp s E m).
Proof.
  intros He Φ Ψ HΦ. wp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
Qed.
End boilerplate.
