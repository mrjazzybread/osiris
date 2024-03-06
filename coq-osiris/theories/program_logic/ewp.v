From iris.base_logic.lib Require Import own gen_heap.

From osiris Require Export syntax.

(* LATER: import [semantics] after [eval, pure] compiles *)
From osiris.semantics Require Export code micro step.


(** *Basic resource algebra for Osiris
  (store can be represented as an authoritative gmap, for now.) *)
From iris.algebra Require Import gmap_view.

From iris.algebra Require Export dfrac.
From iris.program_logic Require Export weakestpre.

Section ghost_instances.

  Context (Σ : gFunctors).

  Class osirisGpreS := {
      #[global] osirisGpreS_iris :: invGpreS Σ;
      #[global] osirisGpreS_inG :: gen_heapGpreS locations.loc step.block Σ
    }.

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_heapGS :: gen_heapGS locations.loc step.block Σ; }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _} : assert.

Definition state_interp {Σ H} (σ : store) :=
  @gen_heap_interp locations.loc _ _ step.block Σ H σ.

(* -------------------------------------------------------------------------- *)
(* Computations that can be handled by a match-expression;
      a [ret _] [throw _] or [perform _ _]. *)
Inductive handleable (A E : Type) : Type :=
  HRet : A → handleable A E
| HThrow : E → handleable A E
| HPerform : C.eff -> (outcome2 syntax.val exn -> micro A E) → handleable A E.

Arguments handleable {A E}.

Arguments HRet {A E}.
Arguments HThrow {A E}.
Arguments HPerform {A E}.

(* Check whether a computation is [handleable]. *)
Definition is_handleable {A X} (m : micro A X) : option handleable :=
  match m with
  | Ret v => Some (HRet v)
  | Throw e => Some (HThrow e)
  | Stop CPerform e k => Some (HPerform e k)
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)
(* Protocols, following Vilhena and Pottier's [A Separation Logic for Effect
    Handlers]. *)
Notation Val := syntax.val.
Notation Eff := C.eff.
Notation Outcome := (outcome2 syntax.val exn).

(* Operations over protocols of carrier [A] *)
Class protocol_op {A} :=
  { (* Operation on protocols *)
    prot_abort : A;
    prot_sum : A -> A -> A;
  (* LATER: Support for [f # Ψ] (see Vilhena & Pottier) *)}.

Class protocol_spec Σ {A} `{@protocol_op A} :=
  { prot_spec : A -d> Eff -d> (Outcome -d> iProp Σ) -d> iProp Σ ;
    prot_spec_ne :: forall a e n, Proper ((dist n) ==> (dist n)) (prot_spec a e) }.

Arguments protocol_spec {_ _ _}.
Arguments prot_spec {_ _ _ _} _ _ _.

Class protocol Σ {A} :=
  { protocol_operations :: @protocol_op A;
    protocol_specification :: @protocol_spec Σ A _ }.

Notation "P + Q" := (prot_sum P Q).
Notation "Ψ 'allows' 'do' v { Φ }" := (prot_spec Ψ v Φ) (at level 40).

(* Axiomatic characterization of protocols *)
Section protocol_spec_properties.

  Variable (Σ : gFunctors).
  Context {A : Type}.
  Context {Protocol : @protocol Σ A}.

  Class protocol_monotone :=
    prot_mono v' Ψ Φ1 Φ2 :
      prot_spec Ψ v' Φ1 ∗ (∀ w, Φ1 w -∗ Φ2 w) ⊢
        prot_spec Ψ v' Φ2.

  Class protocol_abort :=
    prot_abort_absurd v Φ :
      (prot_spec prot_abort v Φ ⊣⊢ ⌜False⌝)%I.

  Class protocol_sum_or :=
    prot_sum_or v' Ψ1 Ψ2 Φ :
      prot_spec (Ψ1 + Ψ2) v' Φ ⊣⊢
        prot_spec Ψ1 v' Φ ∨ prot_spec Ψ2 v' Φ.

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

(* -------------------------------------------------------------------------- *)

Section ewp.

  Context {A X : Type}.

  (* Carrier type of protocols *)
  Context {P : Type}.

  Context `{!osirisGS Σ}
           `{protocol_wf Σ P}.

  Definition ewp_pre
    (ewp: coPset -d> micro A X -d> P -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> micro A X -d> P -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    λ E m Ψ φ,
    (match is_handleable m with
      (* [EWP1] *)
      | Some (HRet v) => |={E}=> φ (O2Ret v)
      | Some (HThrow v) => |={E}=> φ (O2Throw v)
      (* [EWP2] *)
      | Some (HPerform v k) =>
         |={E}=> prot_spec Ψ v (fun w : outcome2 syntax.val exn => ▷ ewp E (k w) Ψ φ)
      (* [EWP3] *)
      | None =>
          ∀ σ, state_interp σ ={E, ∅}=∗
                ⌜can_step (σ, m)⌝ ∗
                (∀ σ' m', ⌜step.step (σ, m) (σ', m')⌝ ={∅}=∗ ▷ |={∅,E}=>
                  (state_interp σ' ∗ ewp E m' Ψ φ))
      end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n wp wp' Hwp E m Φ.
    repeat intro.
    do 2 (f_contractive || f_equiv); cycle 1.
    { repeat (f_contractive || f_equiv);
        apply Hwp. }

    repeat (f_contractive || f_equiv).
    intro.
    repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  Definition ewp_def := fixpoint ewp_pre.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e Ψ Φ} : rename.

End ewp.

(* -------------------------------------------------------------------------- *)

(** Notation. *)

Notation "'EWP' e @ E <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ Φ)
    (at level 20, e, Ψ, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'")
    : bi_scope.

(* -------------------------------------------------------------------------- *)
From iris.proofmode Require Import proofmode.

Section ewp_properties.

Context {A X P : Type}.
Context `{!osirisGS Σ} `{protocol_wf Σ P}.
Implicit Type P : iProp Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : A.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {E} m Ψ {φ} :
  EWP m @ E <| Ψ |> {{ φ }} ⊣⊢ ewp_pre ewp_def E m Ψ φ.
Proof. rewrite /ewp_def; apply (@fixpoint_unfold _ _ _ ewp_pre). Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n Ψ:
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m Ψ).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ' HΦ.
  ewp_unfold_all.
  repeat ((by rewrite IH; [done|lia|];
          let v := fresh "v" in
          intros v; eapply dist_le; [apply HΦ|lia])
          + (f_contractive || f_equiv)).
  intro.

  (f_contractive || f_equiv). eapply IH; auto.
  intros v; eapply dist_le; [apply HΦ|lia].
Qed.

Global Instance ewp_proper E m Ψ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m Ψ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m n Ψ:
  TCEq (is_handleable m) None →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m Ψ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  do 23 (f_contractive || f_equiv).
Qed.

End ewp_properties.

Section lift_specs.

  Context {Σ : gFunctors}.

  Notation iProp := (iProp Σ).

  (* Lifting specifications in Iris logic. *)

  (* [lift_ret_spec] is especially useful for lifting specifications over pure
      results to specifications which may handle exceptional results. *)
  Definition lift_ret_spec {A E} (ϕ : A -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Ret r => ϕ r
    | _ => False
    end.

  Definition lift_exn_spec {A E} (ψ : E -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Throw e => ψ e
    | _ => False
    end.

  Definition ilift {A E} (ϕ : A -> iProp) (ψ : E -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Ret r => ϕ r
    | O2Throw e => ψ e
    end.

End lift_specs.

Notation "ϕ ↑" := (lift_ret_spec ϕ) (at level 20).
Notation "ψ ⤉ " := (lift_exn_spec ψ) (at level 30).
Notation "'|' 'RET' x '=>' e ';' '|' 'EXN' y '=>' f " :=
  (ilift (fun x => e) (fun y => f))
    (at level 200, right associativity, format
    "'[v ' '['  '|'  'RET'  x  '=>'  e ';' ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation *)
Notation "'EWP' e @ E  <| Ψ '|' '>' {{ 'RET' v , Q } }" :=
  (ewp_def E e%E Ψ (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' '/' <| Ψ '|' '>' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EWP' e <| Ψ '|' '>' {{ 'RET' v , Q } }" :=
  (ewp_def NotStuck ⊤ e%E Ψ (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|' '>' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
