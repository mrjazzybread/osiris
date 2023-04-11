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
Definition old_wp η e φ :=
  safe (eval η e) φ.

(* -------------------------------------------------------------------------- *)
(* Definition of the meaning of being a value in [free val], as well as defining 
 * a notion of stuckness. *)

Definition to_val {A} (m: free A) : option A :=
  match m with
  | Ret v => Some v
  | _ => None
  end.

Lemma to_val_can_step {A} (m m': free A):
  step m m' → to_val m = None.
Proof.
  intros ?. by destruct_step.
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
 * the definition below.
 *)
Definition not_stuck {A} (m: free A): Prop :=
  ~ is_answer m /\ ~ stuck m.

Lemma not_stuck_step {A} (m m': free A):
  step m m' → not_stuck m.
Proof.
  intros Hstep.
  split.
  + apply can_step_not_answer.
    by exists m'.
  + intros [_ H].
    by apply (H m').
Qed.

Lemma not_stuck_fail {A} :
  ~ (@not_stuck A Fail).
Proof.
  intros [_ H]. apply H, stuck_Fail.
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
    λ E m φ,
    match to_val m with
    | Some v => φ v
    | None => (⌜not_stuck m⌝
        ∗ ∀ (m': free A),
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
  Implicit Types φ : A → iProp Σ.
  Implicit Types v : A.
  Implicit Types m : free A.

  Lemma wp_unfold s E m φ :
    WP m @ s; E {{ φ }} ⊣⊢ wp_pre A s (wp (PROP:=iProp Σ) s) E m φ.
  Proof.
    rewrite wp_unseal.
    (* TODO: remove φ which should not be necessary here. *)
    apply (@fixpoint_unfold _ _ _ (wp_pre A s) _ _ _ φ).
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
  Context (A: Type).
  Context `{!osirisGS_gen hlc Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types φ : A → iProp Σ.
  Implicit Types v : A.
  Implicit Types m : free A.

  Lemma wp_ret s E v φ:
    φ v -∗ WP (Ret v) @ s; E {{ φ }}.
  Proof. by rewrite!wp_unfold/wp_pre/=. Qed.

  Lemma ret_wp s E v φ:
    WP (Ret v) @ s; E {{ φ }}-∗ φ v.
  Proof. by rewrite!wp_unfold/wp_pre/=. Qed.


  (* It might be useful to prove that there is no associate WP to [Fail] (should 
   * be trivial because Fail is stuck (ie. not a value and does not reduce)). *)
  Lemma wp_fail s E φ:
    ⊢(WP Fail @ s; E {{ φ }}) -∗ ⌜False⌝.
  Proof.
    rewrite !wp_unfold/wp_pre/=.
    iIntros "[%H _]".
    iPureIntro.
    apply H, stuck_Fail.
  Qed.


  Lemma wp_step s E m φ:
    ⌜can_step m⌝ -∗
    (∀ m', ⌜step m m'⌝ -∗ WP m' @ s; E {{ φ }}) -∗
    WP m @ s; E {{ φ }}.
  Proof.
    iIntros ( (m' & Hstep) ) "H".
    rewrite !wp_unfold/wp_pre(to_val_can_step m m' Hstep).
    iSplitR.
    { iPureIntro. by eapply not_stuck_step. }
    iIntros (m'' Hstep').
    by iApply "H".
  Qed.


  Lemma wp_bind s E m1 n2 φ:
    ⊢ WP m1 @ s; E {{ λ a, WP (n2 a) @ s; E {{ φ }} }}
    -∗ WP (bind m1 n2) @ s; E {{ φ }}.
  Proof.
    iIntros "H".
  Admitted.



  Lemma wp_par_ret_left s E v1 m2 k ko φ φ1 φ2:
    φ1 v1
    -∗ WP m2 @ s ; E {{ φ2 }}
    -∗ (∀ (v1 v2: A),
      (φ1 v1) -∗ (φ2 v2) -∗ WP (k (v1, v2)) @ s; E {{ φ }})
     -∗ WP (Par (ret v1) m2 k ko) @ s ; E {{ φ }}.
  Proof.
    iIntros "H1 H2 Hcomb".
    iApply wp_step.
    { eauto with step. }
    iIntros (m' Hstep).
    destruct m2.
    - iPoseProof (ret_wp with "H2") as "H2".
      rewrite (step_par_ret_ret Hstep).
      iApply ("Hcomb" with "H1 H2").
    - iPoseProof (wp_fail with "H2") as "%". intuition.
    - admit.
    - destruct c.
      + destruct x as [η e].
        rewrite (step_par_stopeval_right v1 η e k0 k ko m' Hstep).


    Restart.


    iIntros "H1 H2 Hcomb".
    iInduction m2 as [A v2 | | | | ] "IHm2".
    - rewrite!wp_unfold/wp_pre/=.
      iSplit.
      { iPureIntro. apply not_stuck_step with (k (v1, v2)), StepParRetRet. }
      iIntros (m' ->%step_par_ret_ret).
      iNext. iApply ("Hcomb" with "H1 H2").
    - rewrite!wp_unfold/wp_pre/=.
      iSplit.
      { iPureIntro. apply not_stuck_step with Fail, StepParFailRight. }
      iIntros (m' ->%step_par_fail_right).
      iPoseProof "H2" as "[%H _]".
      exfalso. apply H, stuck_Fail.
    - rewrite!wp_unfold/wp_pre/=.
      iSplit.
      { iPureIntro. apply not_stuck_step with (ko()), StepParNextRight. }
      iIntros (m' ->%step_par_next_right).
      iPoseProof "H2" as "[%H _]".
      exfalso. destruct H as [H1 H2]. by apply H1.
    - rewrite!wp_unfold/wp_pre/=.
      iSplit.
      { iPureIntro. admit. }
      iIntros (m' Hstep).
      destruct_step.
      + inversion Hstep.
      + iPoseProof "H2" as "[%H2 H2]".
        iSpecialize ("H2" $! m'2 Hstep).
        iNext.
        (* Same as below, I would like to use [wp_step], but cannot. *)
        admit.
    - admit.
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
    -∗ (∀ (v1 v2: A),
      (φ1 v1) -∗ (φ2 v2)
         -∗ WP (k (v1, v2)) @ s; E {{ φ }})
         -∗ WP (Par m1 m2 k ko) @ s ; E {{ φ }}.
  Proof.
    (*
     * Using Löb induction cannot work here as there would be a later in 
     * a hypothesis that cannot be eliminated (Cf the restarted proof below).
     *
     * The current approach is to use usual induction on [m1].
     *)

    iInduction (m1) as [] "IHm1";
      iIntros "H1 H2 Hcomb".
    - rewrite!wp_unfold/wp_pre/=.
      triplicity m2 IHm2.
      +
      iSplit.
      { admit. }
      iIntros (m' Hstep).

      Restart.


    iLöb as "IH".
    iIntros "H1 H2 Hcomb".
    rewrite !wp_unfold/wp_pre.
    simpl.
    iSplitR.
    { (* non-stuckness of Par *)
      unshelve epose proof (can_step_par (Par m1 m2 k ko) m1 m2 k ko _)
        as [??];
        first done.
      iPureIntro. by apply not_stuck_step with x. }

    iIntros (m' Hstep). destruct_step; simpl.
    { (* Case: [StepParRetRet] *)
      iApply ("Hcomb" with "H1 H2"). }
    { (* Case: [StepParFailLeft] *)
      iPoseProof "H1" as "[%H _]".
      exfalso. apply H, stuck_Fail. }
    { (* Case: [StepFailRight] *)
      iPoseProof "H2" as "[%H _]".
      exfalso. apply H, stuck_Fail. }
    { (* Case: [StepNextRight] *)
      iPoseProof "H1" as "[[%H _] _]".
      exfalso. by apply H. }
    { (* Case: [StepNextLeft] *)
      iPoseProof "H2" as "[[%H _] _]".
      exfalso. by apply H. }
    { (* Case: [StepParLeft] *)
      rewrite (to_val_can_step m1 m'1 Hstep).
      iNext.
      iPoseProof ("IH" with "H1 H2 Hcomb") as "IH'".
      iPoseProof "IH'" as "[_ JJ]".
      Fail iApply "IH'".
      (* Current issue: The induction adds a later in the hypothesis. Thus, it 
       * is impossible to use [IH] here.
       * In [safe.v], the lemma [initially_safe_monotonic] is used. I do not 
       * think that it holds in iProp Σ. *)
      admit. }
    { (* Case: [StepParRight] *)
      (* Ditto. *)
      admit. }
  Admitted.

End wp_lemmas.



(* Keep a definition based on [safe] so that [examples.v] does not break. *)
Definition wp := old_wp.
