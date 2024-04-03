(** *Protocols

    Protocols (following Vilhena and Pottier's [A Separation Logic for Effect
    Handlers]), describe what effects a computation may perform. *)

From iris.base_logic.lib Require Import iprop.

From osiris Require Export semantics.
From osiris Require Import util.order.

(* -------------------------------------------------------------------------- *)
(** *Abstract protocols  *)
(* We characterize protocols abstractly, with a carrier type [A], paired with
   primitive operations [protocol_op]. *)

(* Operations over protocols of carrier [P] and assertions of type [A]. *)
Class protocol_op {P A} :=
  { (* Primitive for protocols that takes in a precondition and postcondition
       assertion, with request and answers between the Player and Opponent *)
    prot_req_ans : ∀ X Y,
        (X -> syntax.val * A * (Y -> outcome2 syntax.val exn * A)) -> P;
    (* Bottom protocol *)
    prot_bottom : P;
    (* Sum of protocols *)
    prot_sum : P -> P -> P;
    (* f # Ψ *)
    prot_app : forall (f : syntax.val -> syntax.val) {Inj_f : Inj eq eq f}, P -> P;}.

(* -------------------------------------------------------------------------- *)
(* The three-place predicate [prot_spec] (analogous to Ψ allows do v {Φ} in
    Vilhena & Pottier) describes the behavior of a protocol.

   Quoting Vihena & Pottier,
   [prot_spec Ψ v Φ] means that: the "protocol Ψ allows making the request v"
    and additionally "the protocol Ψ guarantee(s) that every permitted reply
    satisfies the postcondition Φ."

    Additionally, we require with [prot_spec_ne] that the predicate respects the
    equivalences for the step-indexed logic of Iris. *)
(* We fix the type of assertions to [iProp]. *)
Class protocol_spec Σ {P} `{@protocol_op P (iProp Σ)} :=
  { prot_spec : P -d> C.eff -d> (outcome2 syntax.val exn -d> iProp Σ) -d> iProp Σ ;
    prot_spec_ne :: forall a e n, Proper ((dist n) ==> (dist n)) (prot_spec a e) }.

Arguments protocol_spec {_ _ _}.
Arguments prot_spec {_ _ _ _} _ _ _.

(* Protocols, with operations and protocol predicate with carrier type [A] and
    preorder relation. *)
Class protocol (Σ : gFunctors) {P} :=
  { protocol_operations :: @protocol_op P (iProp Σ);
    protocol_specification :: @protocol_spec Σ P protocol_operations;
    protocol_preorder :: preorder Σ P }.

(* Notations *)
Notation "λ! x , v <{ P }> λ? y , w <{ Q }>" :=
  (prot_req_ans _ _ (λ x , (v x, P x, λ y, (w x y, Q x y))))
    (left associativity,
      P at level 200, Q at level 200, at level 13,
      format "'[' 'λ!'  x ','  v  '<{'  P  '}>'  'λ?'  y ','  w  '<{'  Q  '}>' ']'").
Notation "P + Q" := (prot_sum P Q).
Notation "Ψ 'allows' 'perform' v << Φ >>" :=
  (prot_spec Ψ v Φ)
  (left associativity, Φ at level 200, at level 12,
    format "'[' Ψ  'allows'  'perform'  v  '<<'  '[' Φ  ']' '>>' ']'") : bi_scope.
Notation "f # Ψ" :=
  (prot_app f Ψ)
  (at level 11, format "'[' f  '#'  Ψ ']'").

(* -------------------------------------------------------------------------- *)
(** *Axiomatic characterization of protocols. *)

Section protocol_spec_properties.

  Variable (Σ : gFunctors).
  Context {P : Type}.
  Context {Protocol : @protocol Σ P}.

  (* [A1] TODO Comment *)
  Class protocol_req_ans :=
    prot_req_ans_allows A X (v : A -> syntax.val) (v' : C.eff)
      (w : A -> X -> outcome2 syntax.val exn)
      (P : A -> iProp Σ) (Q : A -> X -> iProp Σ) Φ :
      (λ! x , v <{ P }> λ? y , w <{ Q }>)
      allows perform v' << Φ >> ⊣⊢
      (* LATER: see if there is a better way to deal with binders *)
      ∃ (x' : A), ⌜v' = v x'⌝ ∗ P x' ∗ ∀ y', (Q x' y' -∗ Φ (w x' y')).

  (* The protocol is monotone over the postcondition and the ordering on protocols. *)
  Class protocol_monotone :=
    prot_mono v Ψ1 Ψ2 Φ1 Φ2 :
      Ψ1 allows perform v << Φ1 >> ∗ (∀ w, Φ1 w -∗ Φ2 w) ∗ Ψ1 ⊆ Ψ2 ⊢
        Ψ2 allows perform v << Φ2 >>.

  (* [prot_bottom] is logically equivalent to [False]. *)
  Class protocol_bottom :=
    prot_bottom_absurd v Φ :
      (prot_bottom allows perform v << Φ >> ⊣⊢ ⌜False⌝)%I.

  (* [A4] TODO Comment *)
  Class protocol_apply :=
    prot_apply f {Inj_f : Inj eq eq f} Ψ v' Φ :
      f # Ψ allows perform f (v') << Φ >> ⊢ Ψ allows perform v' << Φ >>.

  (* [prot_sum] corresponds to logical or [∨]. *)
  Class protocol_sum_or :=
    prot_sum_or v Ψ1 Ψ2 Φ :
      (Ψ1 + Ψ2) allows perform v << Φ >> ⊣⊢
        Ψ1 allows perform v << Φ >> ∨ Ψ2 allows perform v << Φ >>.

  (* The set of axiomatic properties that we support on protocols.

     N.B. the [A *] corresponds to the labelling of laws in Vilhena &
      Pottier. *)
  Class protocol_properties :=
  { (* [A1] *)
    prot_prop_req_ans :: protocol_req_ans;
    (* [A2] *)
    prot_prop_bottom :: protocol_bottom;
    (* [A3] *)
    prot_prop_sum :: protocol_sum_or;
    (* [A4] *)
    prot_prop_apply :: protocol_apply;
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
    ⊢ Ψ allows perform v << Φ1 >> ∗ (∀ w, Φ1 w -∗ Φ2 w) -∗
    Ψ allows perform v << Φ2 >>.
Proof.
  iIntros (????) "[HΨ Hmono]".
  iApply prot_mono; iFrame. iApply refl.
Qed.

Arguments prot_bottom : simpl never.
