Require Import base lang free eval step safe.

From iris.proofmode Require Import base proofmode classes.

From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.


(* TODO: add the following lemmas to [step.v] *)
Lemma step_par_ret_ret {A1 A2 A3} {v: A1} {v': A2} {k: A1 * A2 -> free A3} {ko m}:
  step (Par (ret v) (ret v') k ko) m → m = (k (v, v')).
Proof.
  intros H; destruct_step; first done.
  - inversion H.
  - inversion H.
Qed.

Lemma step_par_fail_right {A1 A2 A3} (v: A1) (k: A1 * A2 → free A3) ko m':
  step (Par (ret v) fail k ko) m' → m' = Fail.
Proof.
  intros H. destruct_step; try done.
  - inversion H.
  - inversion H.
Qed.

Lemma step_par_next_right {A1 A2 A3} (v: A1) (k: A1 * A2 → free A3) ko m':
  step (Par (ret v) free.Next k ko) m' → m' = (ko ()).
Proof.
  intros H. destruct_step; try done.
  - inversion H.
  - inversion H.
Qed.

Lemma step_par_stopeval_right {A1 A2 A3} (v: A1) η e k0 (k: A1 * A2 → free A3) ko m':
  step (Par (ret v) (Stop Eval (η, e) k0) k ko) m' →
    m' = (Par (ret v) (bind (eval η e) k0) k ko).
Proof.
  intros H. destruct_step; try done.
  - inversion H.
  - destruct_step.
    reflexivity.
Qed.



(* Keep the previous definition of [wp] based on [safe] for the examples using 
 * it to remain valid. *)
Definition old_wp η e ϕ :=
  safe (eval η e) ϕ.

(* -------------------------------------------------------------------------- *)
(* Definition of the meaning of being a value in [free val], as well as defining 
 * a notion of stuckness. *)

Definition to_val {A} (m: free A) : option A :=
  match m with
  | Ret v => Some v
  | _ => None
  end.

Lemma step_to_val {A} (m m': free A):
  step m m' → to_val m = None.
Proof.
  intros ?. by destruct_step.
Qed.

Lemma can_step_to_val {A} (m: free A):
  can_step m → to_val m = None.
Proof.
  intros [??]. by destruct_step.
Qed.

Lemma to_val_from_Ret {A} (m: free A) (v: A) : to_val m = Some v -> m = Ret v.
Proof.
  unfold to_val.
  by destruct m; inversion 1.
Qed.

Lemma to_val_non_Ret {A} (m: free A) :
  to_val m = None ->
      m = Fail
    ∨ m = free.Next
    ∨ (∃ A B (c: code A B) x k, m = Stop c x k)
    ∨ (∃ A1 A2 (m1: free A1) (m2: free A2) k (ko: unit → free A),
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
 * the definition of stuckness (eg. use [λ x. x ≠ Fail] instead of [can_step] ?).
 *)
Lemma step_can_step {A} (m m': free A):
  step m m' → can_step m.
Proof.
  intros?. by exists m'.
Qed.

Lemma not_stuck_fail {A} :
  ~ (@can_step A Fail).
Proof.
  intros H. apply (invert_can_step_Fail H).
Qed.



(* -------------------------------------------------------------------------- *)

Class osirisGS_gen (hlc: has_lc) (Σ: gFunctor) := OsrisG {
  osiris_invGS :> invGS_gen hlc Σ;
  (* TODO: add the state interpretation *)
}.



(* -------------------------------------------------------------------------- *)
(* Definition of the weakest precondition.
 * This is heavily inspired from [iris/{bi,program_logic}/weakestpre.v].
 *)

Section wp_def.
  Context (A: Type).

  (* TODO: add the required fancy update(s) to permit using invariants. *)
  Definition wp_pre `{!osirisGS_gen hlc Σ} (s: stuckness)
    (wp: coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ):
    coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ :=
    λ E m ϕ,
    match to_val m with
    | Some v => ϕ v
    | None => (⌜can_step m⌝
        ∗ ∀ (m': free A),
        ⌜step m m'⌝ -∗ ▷ wp E m' ϕ)%I
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
  Definition wp_def `{!osirisGS_gen hlc Σ} : Wp (iProp Σ) (free A) A stuckness :=
    λ (s: stuckness), fixpoint (wp_pre s).

  Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
  Definition wp' := wp_aux.(unseal).
  Global Arguments wp' {hlc Σ _ _}.
  Global Existing Instance wp'.
  Local Lemma wp_unseal `{!osirisGS_gen hlc Σ} : wp = @wp_def hlc Σ _.
  Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End wp_def.


(* -------------------------------------------------------------------------- *)
(* Definitions and lemmas to better work with our WP.
 * Once again, this is heavily inspired from 
 * [iris/{bi,program_logic}/weakestpre.v] *)

Section wp.
  Context (A: Type).
  Context `{!osirisGS_gen hlc Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types ϕ : A → iProp Σ.
  Implicit Types v : A.
  Implicit Types m : free A.

  Lemma wp_unfold s E m ϕ :
    WP m @ s; E {{ ϕ }} ⊣⊢ wp_pre A s (wp (PROP:=iProp Σ) s) E m ϕ.
  Proof.
    rewrite wp_unseal.
    (* TODO: remove ϕ which should not be necessary here. *)
    apply (@fixpoint_unfold _ _ _ (wp_pre A s) _ _ _ ϕ).
  Qed.

  Global Instance wp_ne s E m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E m).
  Proof.
    revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
    rewrite !wp_unfold /wp_pre /=.
    (* Cf. the comment in [program_logic/wp.v] for an explanation on the time 
     * taken by the following line. *)
    do 6 (f_contractive || f_equiv).
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



  (* TODO: prove the following after adding invariant support in [wp_pre]

     Lemma wp_value_fupd' s E Φ m v :
     WP (Ret v) @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.

     Lemma fupd_wp s E m (Φ: val -> iProp Σ) :
     (|={E}=> WP m @ s; E {{ Φ }}) ⊢ WP m @ s; E {{ Φ }}.

     Lemma wp_strong_mono s1 s2 E1 E2 m Φ Ψ :
     s1 ⊑ s2 → E1 ⊆ E2 →
     WP m @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP m @ s2; E2 {{ Ψ }}.

     Lemma wp_fupd s E m Φ :
     WP m @ s; E {{ v, |={E}=> Φ v }} ⊢ WP m @ s; E {{ Φ }}. *)

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

  Lemma wp_ret {A} s E (v: A) ϕ:
    ϕ v -∗ WP (Ret v) @ s; E {{ ϕ }}.
  Proof. by rewrite!wp_unfold/wp_pre/=. Qed.

  Lemma ret_wp {A} s E (v: A) ϕ:
    WP (Ret v) @ s; E {{ ϕ }}-∗ ϕ v.
  Proof. by rewrite!wp_unfold/wp_pre/=. Qed.


  (* It might be useful to prove that there is no associate WP to [Fail] (should 
   * be trivial because Fail is stuck (ie. not a value and does not reduce)). *)
  Lemma wp_fail {A} s E (ϕ: A → iProp Σ):
    ⊢(WP Fail @ s; E {{ ϕ }}) -∗ ⌜False⌝.
  Proof.
    rewrite !wp_unfold/wp_pre/=.
    iIntros "[%H _]".
    iPureIntro.
    apply (invert_can_step_Fail H).
  Qed.

  Lemma wp_next {A} s E (ϕ: A → iProp Σ):
    ⊢(WP free.Next @ s; E {{ ϕ }}) -∗ ⌜False⌝.
  Proof.
    rewrite !wp_unfold/wp_pre/=.
    iIntros "[%H _]".
    iPureIntro. apply (invert_can_step_Next H).
  Qed.


  Lemma wp_step {A} s E m (ϕ: A → iProp Σ):
    ⌜can_step m⌝ -∗
    (∀ m', ⌜step m m'⌝ -∗ WP m' @ s; E {{ ϕ }}) -∗
    WP m @ s; E {{ ϕ }}.
  Proof.
    iIntros ( (m' & Hstep) ) "H".
    rewrite !wp_unfold/wp_pre(step_to_val m m' Hstep).
    iSplitR.
    { iPureIntro. by eapply step_can_step. }
    iIntros (m'' Hstep').
    by iApply "H".
  Qed.

  Lemma step_wp {A} s E m m' (ϕ: A → iProp Σ):
    ⌜step m m'⌝ -∗
    WP m @ s; E {{ ϕ }} -∗
    ▷ WP m' @ s; E {{ ϕ }}.
  Proof.
    iIntros (Hstep) "Hwp".
    setoid_rewrite wp_unfold at 1. rewrite/wp_pre(step_to_val _ _ Hstep).
    iDestruct "Hwp" as "[_ Hwp]".
    by iApply "Hwp".
  Qed.


  Lemma wp_par_ret_ret {A1 A2 A3} s E v1 v2 (k: A1 * A2 → free A3) ko ϕ ϕ1 ϕ2:
    ϕ1 v1 -∗ ϕ2 v2
    -∗ (∀ (v1: A1) (v2: A2), (ϕ1 v1) -∗ (ϕ2 v2) -∗ WP (k (v1, v2)) @ s; E {{ ϕ }})
    -∗ WP (Par (ret v1) (ret v2) k ko) @s; E {{ ϕ }}.
  Proof.
    iIntros "H1 H2 Hcomb".
    iApply wp_step.
    { eauto with step. }
    iIntros (m' ->%step_par_ret_ret).
    iApply ("Hcomb" $! v1 v2 with "H1 H2").
  Qed.



  (* To prove [WP (Par m1 m2 k ko) ϕ], one should provide two post conditions ϕ1 
   * and ϕ2 and show that:
   * - m1 satisfies the post-condition ϕ1
   * - m2 satisfies the post-condition ϕ1
   * - for any values v1 and v2 satisfying ϕ1 and ϕ2 respectively,
   *     the pair (v1, v2) satisfies ϕ.
  *)
  Lemma wp_par {A1 A2 A3} s E m1 m2 (k: A1 * A2 → free A3) ko ϕ ϕ1 ϕ2:
    WP m1 @ s ; E {{ ϕ1 }} -∗ WP m2 @ s ; E {{ ϕ2 }}
    -∗ (∀ (v1: A1) (v2: A2),
      (ϕ1 v1) -∗ (ϕ2 v2)
         -∗ WP (k (v1, v2)) @ s; E {{ ϕ }})
    -∗ WP (Par m1 m2 k ko) @ s ; E {{ ϕ }}.
  Proof.
    iLöb as "IH" forall (m1 m2).
    iIntros "H1 H2 Hcomb".
    setoid_rewrite wp_unfold at 8.
    rewrite /wp_pre.
    simpl.
    iSplitR.
    { (* non-stuckness of Par *)
      unshelve epose proof (can_step_par (Par m1 m2 k ko) m1 m2 k ko _)
        as [??];
        first done.
      iPureIntro. by apply step_can_step with x. }

    iIntros (m' Hstep). destruct_step; simpl.
    { (* Case: [StepParRetRet] *)
      iApply ("Hcomb" with "[H1][H2]"); by iApply ret_wp. }
    { (* Case: [StepParFailLeft] *)
      by iPoseProof (wp_fail with "H1") as "?". }
    { (* Case: [StepFailRight] *)
      by iPoseProof (wp_fail with "H2") as "?". }
    { (* Case: [StepNextLeft] *)
      by iPoseProof (wp_next with "H1") as "?". }
    { (* Case: [StepNextRight] *)
      by iPoseProof (wp_next with "H2") as "?". }
    { (* Case: [StepParLeft] *)
      iPoseProof (step_wp with "[//] H1") as "H1".
      iNext.
      iApply ("IH" with "H1 H2 Hcomb"). }
    { (* Case: [StepParRight] *)
      iPoseProof (step_wp with "[//] H2") as "H2".
      iNext.
      iApply ("IH" with "H1 H2 Hcomb"). }
  Qed.


  Lemma wp_bind {A1 A2} s E (m1: free A1) (m2: A1 → free A2) ϕ:
    ⊢ WP m1 @ s; E {{ λ v, WP (m2 v) @ s; E {{ ϕ }} }}
    -∗ WP (bind m1 m2) @ s; E {{ ϕ }}.
  Proof.
    iLöb as "IH" forall (m1 m2 ϕ).
    iIntros "Hm".
    setoid_rewrite wp_unfold at 4.
    rewrite /wp_pre.
    destruct (to_val m1) as [v1|] eqn:Em1.

    { (* Case: [m] is [ret _]. *)
      by rewrite (to_val_from_Ret _ _ Em1). }

    { (* Case: [m] can step. *)
      iDestruct "Hm" as "[%Hcanstep Hm]".
      rewrite !wp_unfold/wp_pre/=.

      pose proof (can_step_bind m1 m2 Hcanstep) as ->%can_step_to_val.

      iSplit.
      { eauto using can_step_bind with step. }

      iIntros (m' Hstep).

      (* [m' = bind m'1 m2] for some [m'1] st. [step m1 m1'] *)
      assert (Hnoret: ¬ is_answer m1) by eauto using can_step_not_answer.
      pose proof (invert_step_bind' m1 m2 m' Hstep Hnoret)
        as (m'1 & Hsrtep & ->).

      iApply "IH".
      by iApply "Hm". }
  Qed.

End wp_lemmas.



(* Keep a definition based on [safe] so that [examples.v] does not break. *)
Definition wp := old_wp.
