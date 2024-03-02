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

From iris.proofmode Require Import proofmode.

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

Lemma ewp_strong_mono s1 s2 E1 E2 e Φ φ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ φ v) -∗ WP e @ s2; E2 {{ φ }}.
Proof.
  iIntros (? HE) "H HΦ".
  iLöb as "IH" forall (e E1 E2 HE Φ φ).
  rewrite !ewp_unfold /ewp_pre /=.
  destruct (is_outcome2 e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|].
  iIntros (σ2 ? Hstep).
  destruct H1, x.
  iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H".
  iMod "Hclose".
  iModIntro.
  destruct (is_eff e); cycle 1.
  { iDestruct "H" as "[$ H]";
      iApply ("IH" with "[//] H HΦ"). }
  destruct p.
  iDestruct "H" as "[$ [$ H]]".
  iIntros (??) "HSA".
  iSpecialize ("H" with "HSA"). iMod "H".
  iIntros "!> !>".
  iApply ("IH" with "[] H"); auto.
Qed.

End ewp_properties.

(* TODO Comment *)
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

End lift_specs.


(* Custom notation for hoare triples which state a postcondition only over the
    return continuation *)
Notation "'WP' e @ s ; E {{ 'RET' v , Q } }" :=
  (wp s E e%E (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e {{ 'RET' v , Q } }" :=
  (wp NotStuck ⊤ e%E (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[hv' 'WP'  e  '/' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
(* N.B.: we don't use [bi_scope] here to avoid a notation conflict with
  pre-existing notation; might be brittle *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat  ;  Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ NotStuck; ⊤ {{ RET v , Φ v }}).
