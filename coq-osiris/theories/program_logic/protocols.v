(** *Protocols

    Protocols (following Vilhena and Pottier's [A Separation Logic for Effect
    Handlers]), describe what effects a computation may perform. *)

From iris.base_logic.lib Require Import iprop.

From osiris Require Export semantics.
From osiris Require Import util.order.

(* We characterize protocols abstractly, with a carrier type [A], paired with
   primitive operations [protocol_op]. *)

(* Operations over protocols of carrier [A] *)
Class protocol_op {A} :=
  { (* Operation on protocols *)
    prot_abort : A;
    prot_sum : A -> A -> A;
  (* LATER: Support for [f # Ψ] (see Vilhena & Pottier) *)}.

(* The three-place predicate [prot_spec] (analogous to Ψ allows do v {Φ} in
    Vilhena & Pottier) describes the behavior of a protocol.

   Quoting Vihena & Pottier,

   [prot_spec Ψ v Φ] means that: the "protocol Ψ allows making the request v"
    and additionally "the protocol Ψ guarantee(s) that every permitted reply
    satisfies the postcondition Φ."

    Additionally, we require with [prot_spec_ne] that the predicate respects the
    equivalences for the step-indexed logic of Iris. *)
Class protocol_spec Σ {A} `{@protocol_op A} :=
  { prot_spec : A -d> C.eff -d> (syntax.val -d> iProp Σ) -d> iProp Σ ;
    prot_spec_ne :: forall a e n, Proper ((dist n) ==> (dist n)) (prot_spec a e) }.

Arguments protocol_spec {_ _ _}.
Arguments prot_spec {_ _ _ _} _ _ _.

(* Protocols, with operations and protocol predicate with carrier type [A] and
    preorder relation. *)
Class protocol (Σ : gFunctors) {A} :=
  { protocol_operations :: @protocol_op A;
    protocol_specification :: @protocol_spec Σ A _;
    protocol_preorder :: preorder Σ A }.

Notation "P + Q" := (prot_sum P Q).
Notation "Ψ 'allows' 'do' v { Φ }" := (prot_spec Ψ v Φ) (at level 40).

(* Axiomatic characterization of protocols. *)
Section protocol_spec_properties.

  Variable (Σ : gFunctors).
  Context {A : Type}.
  Context {Protocol : @protocol Σ A}.

  (* The protocol is monotone over the postcondition and the ordering on protocols. *)
  Class protocol_monotone :=
    prot_mono v Ψ1 Ψ2 Φ1 Φ2 :
      prot_spec Ψ1 v Φ1 ∗ (∀ w, Φ1 w -∗ Φ2 w) ∗ Ψ1 ⊆ Ψ2 ⊢
        prot_spec Ψ2 v Φ2.

  (* [prot_abort] is logically equivalent to [False]. *)
  Class protocol_abort :=
    prot_abort_absurd v Φ :
      (prot_spec prot_abort v Φ ⊣⊢ ⌜False⌝)%I.

  (* [prot_sum] corresponds to logical or [∨]. *)
  Class protocol_sum_or :=
    prot_sum_or v Ψ1 Ψ2 Φ :
      prot_spec (Ψ1 + Ψ2) v Φ ⊣⊢
        prot_spec Ψ1 v Φ ∨ prot_spec Ψ2 v Φ.

  (* The set of axiomatic properties that we support on protocols.

     N.B. the [A2; A3; A5] corresponds to the labelling of laws in Vilhena &
      Pottier. *)
  Class protocol_properties :=
  { (* [A2] *)
    prot_prop_abort :: protocol_abort;
    (* [A3] *)
    prot_prop_sum :: protocol_sum_or;
    (* [A5] *)
    prot_prop_mono :: protocol_monotone;
  }.

End protocol_spec_properties.

(* Definition of well-formed protocols, i.e. protocol operations and spec
   that satisfies certain axiomatic properties. *)
Class protocol_wf Σ {A} :=
  { protocol_def :: @protocol Σ A;
    protocol_wf_properties :: protocol_properties Σ }.

From iris.proofmode Require Import proofmode.

Lemma prot_mono_post {Σ P} `{protocol_wf Σ P}:
  ∀ Ψ v Φ1 Φ2,
    ⊢ prot_spec Ψ v Φ1 ∗ (∀ w, Φ1 w -∗ Φ2 w) -∗ prot_spec Ψ v Φ2.
Proof.
  iIntros (????) "[HΨ Hmono]".
  iApply prot_mono; iFrame. iApply refl.
Qed.
