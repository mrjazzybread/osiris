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

(* TODO *)
Definition is_outcome2 {A X} (m : micro A X) : option (outcome2 A X):=
  match m with
  | Ret v => Some (O2Ret v)
  | Throw e => Some (O2Throw e)
  | _ => None
  end.

(* TODO *)
Definition is_eff {A X} (m : micro A X) : option _:=
  match m with
  | Stop CPerform e k => Some (e, k)
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)
(* TODO *)
Class protocol {Σ} :=
  { eff_p : syntax.val -d> iPropO Σ;
    ans_p : syntax.val -d> iPropO Σ }.
(* -------------------------------------------------------------------------- *)

(* TODO *)
Section ewp.

Context `{!osirisGS Σ} `{protocol Σ}.

Context {A X : Type}.

(* TODO *)
Definition ewp_pre
  (ewp: coPset -d> micro A X -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> micro A X -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
  λ E m φ,
  (match is_outcome2 m with
    | Some v =>
        |={E}=> φ v
    | None =>
      ∀ σ, state_interp σ ={E, ∅}=∗
        ⌜can_step (σ, m)⌝ ∗
        (∀ σ' m', ⌜step.step (σ, m) (σ', m')⌝ ={∅}=∗ ▷ |={∅,E}=>
            match is_eff m with
            | Some (v, k) =>
                state_interp σ' ∗ eff_p v ∗
                (∀ σ'' w, state_interp σ'' ∗ ans_p w ==∗ ▷ ewp E (k (O2Ret w)) φ)
            | None =>
                (state_interp σ' ∗ ewp E m' φ)
      end)
  end)%I.

Local Instance ewp_pre_contractive : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre /= => n wp wp' Hwp E m Φ.
  do 16 (f_contractive || f_equiv);
  repeat f_equiv; apply Hwp.
Qed.

Definition ewp_def : Wp (iProp Σ) (micro A X) (outcome2 A X) stuckness :=
  λ (_ : stuckness), fixpoint ewp_pre.

Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
Definition ewp' := ewp_aux.(unseal).


Global Arguments ewp' {Σ _ _}.
Global Existing Instance ewp'.
Local Lemma ewp_unseal: wp = ewp_def.
Proof. rewrite -ewp_aux.(seal_eq) //. Qed.

End ewp.

(* -------------------------------------------------------------------------- *)

Section ewp_properties.

Context {A X : Type}.
Context `{!osirisGS Σ} `{protocol Σ}.
Implicit Type s : stuckness.
Implicit Type P : iProp Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : A.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {s E} m {φ} :
  WP m @ s; E {{ φ }} ⊣⊢ ewp_pre (wp s) E m φ.
Proof.
  rewrite ewp_unseal.
  apply (@fixpoint_unfold _ _ _ ewp_pre).
Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne s E m n :
  Proper
    (pointwise_relation _ (dist n) ==> dist n)
    (wp s E m).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
  ewp_unfold_all.
  repeat ((by rewrite IH; [done|lia|];
          let v := fresh "v" in
              intros v; eapply dist_le; [apply HΦ|lia])
         + (f_contractive || f_equiv)).
Qed.

Global Instance ewp_proper s E m :
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (wp s E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive s E m n :
  TCEq (is_outcome2 m) None →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (wp s E m).
Proof.
  intros He Φ Ψ HΦ. ewp_unfold_all. rewrite He /=.
  do 23 (f_contractive || f_equiv).
  repeat f_equiv.
Qed.
End ewp_properties.
