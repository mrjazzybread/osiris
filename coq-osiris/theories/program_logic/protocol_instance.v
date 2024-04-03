(** *Concrete instance of protocols *)
From iris.base_logic.lib Require Import iprop.

From iris.proofmode Require Import proofmode.

From osiris Require Import program_logic.protocols.

Section concrete_protocols.

  Context (Σ : gFunctors).

  Notation Val := syntax.val.

  (* -------------------------------------------------------------------------- *)

  (* [iEff] Concrete instance for protocols, following Vilhena & Pottier '21. *)

  Definition iEff := Val -d> (outcome2 Val exn -d> iProp Σ) -n> iProp Σ.

  Definition iEff_spec :
    iEff -d> C.eff -d> (outcome2 Val exn -d> iProp Σ) -d> iProp Σ :=
    (λ Ψ e Φ, ∃ Φ', Ψ e Φ' ∗ (∀ w, Φ' w -∗ Φ w))%I.

  (* -------------------------------------------------------------------------- *)

  (* NonExpansiveness and properness of [iEff] *)

  #[global] Instance iEff_spec_ne : NonExpansive iEff_spec.
  Proof.
    intros ??????; rewrite /iEff_spec; repeat (f_contractive || f_equiv).
    destruct x0; simpl; by repeat (f_equiv).
  Qed.

  #[global] Instance iEff_spec_proper :
      forall Ψ e n, Proper ((dist n) ==> (dist n)) (iEff_spec Ψ e).
  Proof. solve_proper. Qed.

  (* -------------------------------------------------------------------------- *)

  (* [iEff] operators *)

  Definition iEff_bottom : iEff := (λ _, λne _, ⌜False⌝)%I.

  Program Definition iEff_sum (Ψ1 Ψ2 : iEff) : iEff :=
    (λ v, λne Φ, (Ψ1 v Φ) ∨ (Ψ2 v Φ))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition iEff_prot_req_ans
    (X Y : Type)
    (f : X -> syntax.val * iProp Σ * (Y -> outcome2 syntax.val exn * iProp Σ))
    : iEff :=
    (λ v', λne Φ',
      ∃ x',
        let '(v, P, Ψ) := f x' in
        ⌜v = v'⌝ ∗
        P ∗
      ∀ y',
        let '(w, Q) := Ψ y' in
        Q -∗ Φ' w)%I.
  Next Obligation.
    cbn; repeat intro. repeat f_equiv.
    destruct (f a). destruct p; cbn.
    repeat f_equiv.
    destruct (p0 a0). repeat f_equiv.
  Qed.

  Program Definition iEff_app
    (f : syntax.val -> syntax.val) {Inj_f : Inj eq eq f} (Ψ : iEff) : iEff :=
    (λ v', λne Φ', ∃ w', ⌜v' = f (w')⌝ ∗ Ψ w' Φ')%I.
  Next Obligation. solve_proper. Qed.

  #[global] Instance iEff_op : @protocol_op iEff (iProp Σ) :=
    {| prot_req_ans := iEff_prot_req_ans;
       prot_bottom := iEff_bottom;
       prot_sum := iEff_sum;
       prot_app := iEff_app |}.

  #[global] Instance iEff_protocol_spec : protocol_spec :=
    {| prot_spec := iEff_spec; prot_spec_ne := iEff_spec_proper |}.

  (* -------------------------------------------------------------------------- *)

  (* Ordering of [iEff] protocols *)

  Definition iEff_order :=
    (λ Ψ1 Ψ2, <pers> (∀ v Φ, iEff_spec Ψ1 v Φ -∗ iEff_spec Ψ2 v Φ))%I.

  #[global] Program Instance iEff_order_preorder : order.preorder Σ iEff :=
    {| order.order := iEff_order |}.
  Next Obligation.
    (* Reflexivity *)
    iIntros (Ψ e); iModIntro; iIntros (Φ) "$".
  Qed.
  Next Obligation.
    (* Transitivity *)
    iIntros (Ψ1 Ψ2 Ψ3) "#H1 #H2".
    iIntros (e); iModIntro; iIntros (Φ) "Hspec".
    iApply "H2"; by iApply "H1".
  Qed.

  #[global] Instance iEff_protocol : @protocol Σ iEff :=
    {| protocol_operations := iEff_op ;
       protocol_specification := iEff_protocol_spec;
       protocol_preorder := iEff_order_preorder; |}.

  (* -------------------------------------------------------------------------- *)

  (* [iEff] protocol properties *)

  #[global] Instance iEff_protocol_req_ans :
    @protocol_req_ans Σ iEff iEff_protocol.
  Proof.
    iIntros (????????).
    iSplit; rewrite /prot_req_ans /= /iEff_spec /iEff_prot_req_ans.
    { iIntros "HΦ".
      iDestruct "HΦ" as (?) "HΦ"; cbn.
      iDestruct "HΦ" as "(HΦv & Hw)".
      iDestruct "HΦv" as (??) "(HP & HQΦ)"; subst.
      iExists x'; iSplitL ""; first done; iFrame.
      iIntros (?) "HQ". iSpecialize ("HQΦ" with "HQ").
      iApply ("Hw" with "HQΦ"). }
    { iIntros "HΦ".
      iDestruct "HΦ" as (??) "(HP & HQΦ)"; subst; cbn.
      iExists Φ.
      iSplitR ""; last (iIntros; done).
      iExists x'; by iFrame. }
  Qed.

  #[global] Instance iEff_protocol_mono :
    @protocol_monotone Σ iEff iEff_protocol.
  Proof.
    iIntros (?????) "[HΨ [HΦ #Ho]]".
    iAssert (prot_spec Ψ1 v Φ2)%I with "[HΨ HΦ]"as "HΨ'".
    { iDestruct "HΨ" as (?) "(HΨ & HΦ')".
      iExists Φ'; iFrame; iIntros (?) "HΦ'w".
      iSpecialize ("HΦ'" with "HΦ'w"); iApply ("HΦ" with "HΦ'"). }
    iApply ("Ho" with "HΨ'").
  Qed.

  #[global] Instance iEff_protocol_bottom :
    @protocol_bottom Σ iEff iEff_protocol.
  Proof.
    iIntros (??). rewrite /prot_bottom /= /iEff_spec.
    iSplit; [ | iIntros (?); done ].
    iIntros "[%_ [[] _]]".
  Qed.

  #[global] Instance iEff_protocol_apply :
    @protocol_apply Σ iEff iEff_protocol.
  Proof.
    iIntros (?????) "Hf"; cbn; rewrite /iEff_spec /iEff_app /=.
    iDestruct "Hf" as (?) "(Hf & HΦ)".
    iExists Φ'.
    iDestruct "Hf" as (??) "HΨ"; iFrame.
    apply Inj_f in H; by subst.
  Qed.

  #[global] Instance iEff_protocol_sum_or :
    @protocol_sum_or Σ iEff iEff_protocol.
  Proof.
    iIntros (????); iSplit; iIntros "HΨ";
      rewrite /prot_spec /= /iEff_sum /iEff_spec.
    { iDestruct "HΨ" as (?) "([HΨ1 | HΨ2] & HΦ)"; [ iLeft | iRight ];
        iExists _; iFrame. }

    { iDestruct "HΨ" as "[HΨ | HΨ]";
        iDestruct "HΨ" as (?) "(HΨ & HΦ)";
        iExists Φ'; iFrame. }
  Qed.

  #[global] Instance iEff_protocol_properties :
    @protocol_properties Σ iEff iEff_protocol.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global] Instance iEff_protocol_WF : @protocol_wf Σ iEff.
  Proof. econstructor; typeclasses eauto. Qed.

End concrete_protocols.

