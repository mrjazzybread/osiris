Require Import base lang free eval step safe.

From iris.proofmode Require Import base proofmode classes.

From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.



(* Keep the previous definition of [wp] based on [safe] for the examples using 
 * it to remain valid. *)
Definition old_wp η e φ :=
  safe (eval η e) φ.

(* -------------------------------------------------------------------------- *)
(* Definition of the meaning of being a value in [free val], as well as defining 
 * a notion of stuckness. *)

Definition to_val (m: free val) : option val :=
  match m with
  | Ret v => Some v
  | _ => None
  end.

Lemma to_val_from_Ret (m: free val) (v: val) : to_val m = Some v -> m = Ret v.
Proof.
  unfold to_val.
  by destruct m; inversion 1.
Qed.

Lemma to_val_non_Ret (m: free val) :
  to_val m = None ->
      m = Fail
    ∨ m = free.Next
    ∨ (∃ A B (c: code A B) x k, m = Stop c x k)
    ∨ (∃ A1 A2 (m1: free A1) (m2: free A2) k (ko: unit → free val),
        m = Par m1 m2 k ko).
Proof.
  destruct m; first inversion 1; intros?; eauto.
  - do 2 right. left.
    by eexists _, _, _, _, _.
  - do 3 right.
    by eexists _, _, _, _, _, _.
Qed.

(* Note: Per the lemma [only_fail_is_stuck], only fail is stuck.
 * If this lemma remains (currently in discussion), it might be used to simplify 
 * the definition below.
 *)
Definition not_stuck (m: free val): Prop :=
  ~ stuck m.



(* -------------------------------------------------------------------------- *)

Class osirisGS_gen (hlc: has_lc) (Σ: gFunctor) := OsrisG {
  osiris_invGS :> invGS_gen hlc Σ;

  (* TODO: add the state interpretation *)
}.



(* -------------------------------------------------------------------------- *)
(* Definition of the weakest precondition.
 * This is heavily inspired from [iris/{bi,program_logic}/weakestpre.v].
 *)

(* TODO: push the modality towards [-∗] in the second branch. *)
Definition wp_pre `{!osirisGS_gen hlc Σ} (s: stuckness)
  (wp: coPset -d> free val -d> (val -d> iPropO Σ) -d> iPropO Σ):
  coPset -d> free val -d> (val -d> iPropO Σ) -d> iPropO Σ :=
  λ E m φ,
    match to_val m with
    | Some v => (|={E}=> φ v)%I
    | None => (|={E}=> ⌜not_stuck m⌝
        ∗ ∀ (m': free val),
        ⌜step m m'⌝ -∗ ▷ wp E m' φ)%I
    end.

#[local]
Instance wp_pre_contractive `{!osirisGS_gen hlc Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E m Φ.
  repeat (f_contractive || f_equiv).
  apply Hwp.
Qed.

(* Keeping the stuckness bit and the following notation ensure that the usual 
 * notations will work (ie. [WP _ @ _ {{ _ }}] and [WP _@ _ ?{{ _ }}]). *)
Definition wp_def `{!osirisGS_gen hlc Σ} : Wp (iProp Σ) (free val) val stuckness :=
  λ (s: stuckness), fixpoint (wp_pre s).

Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {hlc Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!osirisGS_gen hlc Σ} : wp = @wp_def hlc Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.



(* -------------------------------------------------------------------------- *)
(* Definitions and lemmas to better work with our WP.
 * Once again, this is heavily inspired from 
 * [iris/{bi,program_logic}/weakestpre.v] *)

Section wp.
  Context `{!osirisGS_gen hlc Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types m : free val.

  Lemma wp_unfold s E m φ :
    WP m @ s; E {{ φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ) s) E m φ.
  Proof.
    rewrite wp_unseal.
    (* TODO: remove φ which should not be necessary here. *)
    apply (@fixpoint_unfold _ _ _ (wp_pre s) _ _ _ φ).
  Qed.

  Global Instance wp_ne s E m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E m).
  Proof.
    revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
    rewrite !wp_unfold /wp_pre /=.
    (* Cf. the comment in [program_logic/wp.v] for an explanation on the time 
     * taken by the following line. *)
    do 7 (f_contractive || f_equiv).
    rewrite IH; [done|lia|]. intros v. eapply dist_le; [apply HΦ|lia].
  Qed.

  Global Instance wp_proper s E m :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E m).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
  Qed.
  Global Instance wp_contractive s E m n :
    TCEq (to_val m) None →
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E m).
  Proof.
    intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
    repeat (f_contractive || f_equiv).
  Qed.



  Lemma wp_value_fupd' s E Φ m v :
    WP (Ret v) @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof.
    now rewrite wp_unfold /wp_pre /=.
  Qed.

  Lemma fupd_wp s E m (Φ: val -> iProp Σ) :
    (|={E}=> WP m @ s; E {{ Φ }}) ⊢ WP m @ s; E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val m) as [v|] eqn:?.
    { by iMod "H". }
    iMod "H". iMod "H" as "[% H]".
    iApply fupd_sep.
    iSplitR.
    { by iPureIntro. }
    by iApply "H".
  Qed.

  Lemma wp_strong_mono s1 s2 E1 E2 m Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WP m @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP m @ s2; E2 {{ Ψ }}.
  Proof.
    iIntros (? HE) "H HΦ". iLöb as "IH" forall (m E1 E2 HE Φ Ψ).
    rewrite !wp_unfold /wp_pre /=.
    destruct (to_val m) as [v|] eqn:?.
    { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod ("H") as "[% H]".
    iMod "Hclose".
    iModIntro. iSplit; [by destruct s1, s2|]. iIntros (m' Hstep).
    iPoseProof ("H" $! m' Hstep) as "H".
    iModIntro.
    iApply ("IH" with "[//]H HΦ").
  Qed.

  Lemma wp_fupd s E m Φ : WP m @ s; E {{ v, |={E}=> Φ v }} ⊢ WP m @ s; E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_strong_mono s s E with "H"); auto.
  Qed.

End wp.



(* -------------------------------------------------------------------------- *)
(* The following are lemmas about the evolutions of a term. They are designed to 
 * be used in [wp_tactics].
 * Most of these lemmas have counterparts defined for [safe] in 
 * [theories/safe.v]. (Note: as the step-indexing using [nat] is replaced by one 
 * that uses the later modality, inductions are replaced by Löb inductions.)
 *)

Section wp_lemmas.
  Context `{!osirisGS_gen hlc Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types m : free val.

  Lemma wp_ret s E v φ:
    (|={E}=> φ v)
    -∗ WP (Ret v) @ s; E {{ φ }}.
  Proof. by rewrite!wp_unfold/wp_pre/=. Qed.

  (* It might be useful to prove that there is no associate WP to [Fail] (should 
   * be trivial because Fail is stuck (ie. not a value and does not reduce)). *)
  Lemma wp_fail s E φ:
    ⊢(WP Fail @ s; E {{ φ }}) -∗ ⌜False⌝.
  Admitted.

  (* To prove [WP (Par m1 m2 k ko) φ], one should provide two post conditions φ1 
   * and φ2 and show that:
   * - m1 satisfies the post-condition φ1
   * - m2 satisfies the post-condition φ1
   * - for any values v1 and v2 satisfying φ1 and φ2 respectively,
   *     the pair (v1, v2) satisfies φ.
  *)
  Lemma wp_par s E m1 m2 k ko φ φ1 φ2:
    WP m1 @ s ; E {{ φ1 }} -∗ WP m2 @ s ; E {{ φ2 }}
    -∗ (∀ (v1 v2: val),
        (φ1 v1) -∗ (φ2 v2)
         -∗ WP (k (v1, v2)) @ s; E {{ φ }})
      (*={E}=∗*) -∗ WP (Par m1 m2 k ko) @ s ; E {{ φ }}.
  Proof.
    iLöb as "IH".
    iIntros "H1 H2 Hcomb".
    rewrite !wp_unfold/wp_pre.
    simpl.
    destruct (to_val m1) as [v1|] eqn:E1;
    destruct (to_val m2) as [v2|] eqn:E2.
    { (* case [Par (Ret _) (Ret _) _ _] *)
      apply to_val_from_Ret in E1 as ->, E2 as ->.
      iApply fupd_sep.
      iSplitR.
      { iPureIntro. intros [_ H]. apply (H (k (v1, v2))), StepParRetRet. }
      iPoseProof ("IH" with "[$H1][$H2][$Hcomb]") as "H".
      iModIntro.
      iIntros (m' Hstep).
      destruct_step.
      - admit.
      - inversion Hstep.
      - inversion Hstep. }
  Admitted.
End wp_lemmas.



(* Keep a definition based on [safe] so that [examples.v] does not break. *)
Definition wp := old_wp.
