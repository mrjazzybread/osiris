From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
From iris Require Import base_logic.lib.gen_heap.
Import uPred.

From iris.algebra Require Import gmap.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.



(* -------------------------------------------------------------------------- *)
(* Definition of the meaning of being a value in [free val]. *)

Definition is_ret {A} (m: free A) : option A :=
  match m with
  | Ret v => Some v
  | _ => None
  end.

Lemma can_step_is_ret {A} (m: free A) σ:
  can_step (σ, m) → is_ret m = None.
Proof.
  intros [??]. by destruct_step.
Qed.

Lemma is_ret_from_Ret {A} (m: free A) (v: A) : is_ret m = Some v -> m = Ret v.
Proof.
  unfold is_ret.
  by destruct m; inversion 1.
Qed.

(* -------------------------------------------------------------------------- *)

Class osirisGS_gen (hlc: has_lc) (Σ: gFunctor) := OsrisG {
  osiris_invGS :> invGS_gen hlc Σ;

  osiris_heapGS :> gen_heapGS loc val Σ;
}.



(* -------------------------------------------------------------------------- *)
(* Definition of the weakest precondition.
   This is heavily inspired from [iris/{bi,program_logic}/weakestpre.v]. *)

Section wp_def.
  Context (A: Type).
  Context `{!osirisGS_gen hlc Σ}.

  Definition state_interp σ :=
    gen_heap_interp σ.

  (* TODO: add the required fancy update(s) to permit using invariants. *)
  Definition wp_pre  (s: stuckness)
    (wp: coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ):
    coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ :=
    λ E m ϕ,
      (∀ σ, state_interp σ -∗
           match is_ret m with
           | Some v => state_interp σ ∗ ϕ v
           | None =>
               ⌜can_step (σ, m)⌝ ∗
                ∀ (σ': store) (m': free A),
                  ⌜step (σ, m) (σ', m')⌝ ==∗
                  ▷ (state_interp σ' ∗
                     wp E m' ϕ)
           end)%I.

  #[local]
  Instance wp_pre_contractive s : Contractive (wp_pre s).
  Proof.
    rewrite /wp_pre /= => n wp wp' Hwp E m Φ.
    repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  (* Keeping the stuckness bit and the following notation ensure that the usual
     notations will work (ie. [WP _ @ _ {{ _ }}] and [WP _@ _ ?{{ _ }}]). *)
  Definition wp_def : Wp (iProp Σ) (free A) A stuckness :=
    λ (s: stuckness), fixpoint (wp_pre s).

  Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
  Definition wp' := wp_aux.(unseal).
  Global Arguments wp' {hlc Σ _ _}.
  Global Existing Instance wp'.
  Local Lemma wp_unseal: wp = wp_def.
  Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End wp_def.


(* -------------------------------------------------------------------------- *)
(* Definitions and lemmas to better work with our WP.
   Once again, this is heavily inspired from
   [iris/{bi,program_logic}/weakestpre.v] *)

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
    apply (@fixpoint_unfold _ _ _ (wp_pre A s)).
  Qed.

  Global Instance wp_ne s E m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E m).
  Proof.
    revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
    rewrite !wp_unfold /wp_pre /=.
    (* Cf. the comment in [program_logic/wp.v] for an explanation on the time
     * taken by the following line. *)
    repeat ((by rewrite IH; [done|lia|];
                intros v; eapply dist_le; [apply HΦ|lia])
            + (f_contractive || f_equiv)).
  Qed.

  Global Instance wp_proper s E m :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E m).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
  Qed.
  Global Instance wp_contractive s E m n :
    TCEq (is_ret m) None →
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
   be used in [wp_tactics]. *)

Section wp_lemmas.
  Context `{!osirisGS_gen hlc Σ}.

  Lemma wp_covariant {A} s E m (ϕ: A -> iProp Σ) (ϕ': A -> iProp Σ) :
    WP m @ s; E {{ ϕ }} -∗
    (∀ v, (ϕ v) -∗ (ϕ' v)) -∗
    WP m @ s; E {{ ϕ' }}.
  Proof.
    iLöb as "IH" forall (ϕ ϕ' m).
    iIntros "Hwp Himpl".
    rewrite!wp_unfold/wp_pre.
    destruct (is_ret m).

    { (* Case [m] is [ret _]. *)
      iIntros(?) "H".
      iDestruct ("Hwp" with "H") as "[$ H]".
      iApply ("Himpl" with "H"). }

    (* Other cases *)
    { iIntros (σ) "Hsi".
      iPoseProof ("Hwp" $! σ with "Hsi") as "[$ Hwp]";
      iIntros (σ' m' Hstep).
      iPoseProof ("Hwp" with "[//]") as ">[$ Hwp]".
      iModIntro. iNext.
      iApply ("IH" with "Hwp Himpl"). }
  Qed.

  Lemma strong_mono {A} P m s E (ϕ: A → iProp Σ):
    (P ∗ WP m @ s; E {{ ϕ }}) -∗ WP m @ s; E {{ λ v, P ∗ ϕ v }}.
  Proof.
    iStartProof.
    rewrite wp_unfold/wp_pre/=.
    iLöb as "IH" forall (m).
    destruct (is_ret m) as [a|]eqn:Em.
    { iIntros"[? Hwp]". rewrite wp_unfold/wp_pre Em/=.
      iIntros (σ)"Hsi".
      iPoseProof ("Hwp" with "Hsi") as "Hwp".
      by iFrame. }
    iIntros "(HP & Hwp)".
    rewrite wp_unfold/wp_pre Em/=.
    iIntros (σ) "Hsi".
    iPoseProof ("Hwp" with "Hsi") as "[$Hwp]".
    iIntros (σ' m' Hstep).
    iPoseProof ("Hwp" with "[//]") as ">[$Hwp]".
    iModIntro. iNext.
    iApply ("IH" with "[$HP Hwp]").
    { by rewrite!wp_unfold/wp_pre/=. }
  Qed.

  Lemma wp_ret {A} s E (v: A) ϕ:
    ϕ v -∗ WP (Ret v) @ s; E {{ ϕ }}.
  Proof.
    rewrite!wp_unfold/wp_pre/=.
    iIntros. iFrame.
  Qed.

  Lemma ret_wp {A} s E (v: A) σ ϕ:
    state_interp σ -∗
    WP (Ret v) @ s; E {{ ϕ }} ==∗
    state_interp σ ∗ ϕ v.
  Proof.
    rewrite wp_unfold/wp_pre/=.
    iIntros "Hsi H".
    iSpecialize ("H" $! σ with "Hsi").
    iAssumption.
  Qed.


  (* It might be useful to prove that there is no associate WP to [Crash]. *)
  Lemma wp_crash {A} s E σ ϕ:
    state_interp σ -∗ WP (@crash A) @ s; E {{ϕ}} -∗ ⌜False⌝.
  Proof.
    rewrite !wp_unfold/wp_pre/=.
    iIntros "Hsi Hwp".
    iPoseProof ("Hwp" with "Hsi") as "[% _]".
    exfalso. inversion H as [s' H']. inversion H'.
  Qed.

  Lemma wp_next {A} s E σ (ϕ: A → iProp Σ):
    state_interp σ -∗ (WP Next @ s; E {{ ϕ }}) -∗ ⌜False⌝.
  Proof.
    rewrite !wp_unfold/wp_pre/=.
    iIntros "Hsi Hwp".
    iPoseProof ("Hwp" with "Hsi") as "[% _]".
    exfalso. inversion H as [s' H']. inversion H'.
  Qed.


  (* [bind]-related lemmas. *)
  Lemma wp_bind {A1 A2} s E (m1: free A1) (m2: A1 → free A2) ϕ:
    WP m1 @ s; E {{ λ v, WP (m2 v) @ s; E {{ ϕ }} }} -∗
    WP (bind m1 m2) @ s; E {{ ϕ }}.
  Proof.
    iLöb as "IH" forall (m1 m2 ϕ).
    iIntros "Hm".
    setoid_rewrite wp_unfold at 4.
    rewrite /wp_pre.
    destruct (is_ret m1) as [v1|] eqn:Em1.
    { (* Case: [m] is [ret _]. *)
      rewrite (is_ret_from_Ret _ _ Em1).
      iApply wp_unfold. unfold wp_pre.
      iIntros (σ) "Hsi".
      iDestruct ("Hm" with "Hsi") as "[Hsi Hwp]".
      iDestruct (wp_unfold with "Hwp") as "Hwp". unfold wp_pre.
      iApply ("Hwp" with "Hsi"). }
    { (* Case: [m] can step. *)
      iApply wp_unfold. unfold wp_pre.
      iIntros (σ) "Hsi".
      iDestruct ("Hm" with "Hsi") as "[%Hcanstep Hm]".
      pose proof (can_step_bind _ m1 m2 Hcanstep) as ->%can_step_is_ret.
      iSplit.
      { iPureIntro. eauto using can_step_bind with step. }


      iIntros (σ' m') "%Hstep".
      (* [m' = bind m'1 m2] for some [m'1] st. [step m1 m1'] *)
      assert (Hnoret: ¬ is_answer m1).
      { intros?.
        unfold is_answer in H.
        destruct m1 eqn:E'; try assumption;
        destruct_step. }
      pose proof (invert_step_bind' Hstep Hnoret) as (σ'1 & m'1 & Hsrtep & a).
      simplify_eq/=.
      iPoseProof ("Hm" with "[//]") as ">[$Hm]".
      iModIntro. iNext.
      iApply "IH". iApply "Hm". }
  Qed.

  Lemma wp_try_ret {A B} s E (v: A) (k: A -> free B) ko ϕ :
    WP bind (ret v) k @ s; E {{ ϕ }} -∗ WP try (ret v) k ko @s; E {{ ϕ }}.
  Proof.
    by iIntros "H".
  Qed.


  (* [Par]-related lemmas. *)
  (* To prove [WP (Par m1 m2 k ko) ϕ], one should provide two post conditions ϕ1
   * and ϕ2 and show that:
   * - m1 satisfies the post-condition ϕ1
   * - m2 satisfies the post-condition ϕ1
   * - for any values v1 and v2 satisfying ϕ1 and ϕ2 respectively,
   *     the pair (v1, v2) satisfies ϕ.
  *)
  Lemma wp_par {A1 A2 A3} s E m1 m2 (k: A1 * A2 → free A3) ko ϕ ϕ1 ϕ2:
    WP m1 @ s ; E {{ ϕ1 }} -∗
    WP m2 @ s ; E {{ ϕ2 }} -∗
    ▷ (∀ (v1: A1) (v2: A2),
        ϕ1 v1 -∗ ϕ2 v2 -∗
        WP (k (v1, v2)) @ s; E {{ ϕ }})
    -∗ WP (Par m1 m2 k ko) @ s ; E {{ ϕ }}.
  Proof.
    iLöb as "IH" forall (m1 m2).
    iIntros "H1 H2 Hcomb".
    (* TODO: make the prof more robust. *)
    setoid_rewrite wp_unfold at 8.
    rewrite /wp_pre/=.
    iIntros (σ) "Hsi".
    iSplitR.
    { iPureIntro. eapply can_step_par. reflexivity. }
    iIntros (σ' m' Hstep).
    (* TODO: cleanup hypotheses at this point *)

    destruct_step; simpl.
    { (* Case: [StepParRetRet] *)
      iDestruct (ret_wp with "Hsi H1") as ">[Hsi H1]".
      iDestruct (ret_wp with "Hsi H2") as ">[Hsi H2]".
      iModIntro. iFrame. iNext. iApply ("Hcomb" with "H1 H2"). }
    { (* Case: [StepParCrashLeft] *)
      iModIntro. iNext.
      iPoseProof (wp_crash with "Hsi H1") as "%".
      exfalso. assumption. }
    { (* Case: [StepCrashRight] *)
      iModIntro. iNext.
      iPoseProof (wp_crash with "Hsi H2") as "%".
      exfalso. assumption. }
    { (* Case: [StepNextLeft] *)
      iModIntro. iNext.
      iPoseProof (wp_next with "Hsi H1") as "%".
      exfalso. assumption. }
    { (* Case: [StepNextRight] *)
      iModIntro. iNext.
      iPoseProof (wp_next with "Hsi H2") as "%".
      exfalso. assumption. }
    { (* Case: [StepParLeft] *)
      setoid_rewrite wp_unfold at 5. rewrite /wp_pre/=.
      assert (is_ret m1 = None) as ->.
      { eauto using can_step_is_ret with step. }
      iDestruct ("H1" with "Hsi") as "[%Hstep1 H1]".
      iPoseProof
        ("H1" $! σ' with "[//]")
        as ">[$H1]".
      iModIntro. iNext.
      iApply ("IH" with "H1 H2 Hcomb"). }
    { (* Case: [StepParLeft] *)
      setoid_rewrite wp_unfold at 6. rewrite /wp_pre/=.
      assert (is_ret m2 = None) as ->.
      { eauto using can_step_is_ret with step. }
      iDestruct ("H2" with "Hsi") as "[%Hstuck2 H2]".
      iPoseProof
        ("H2" $! σ' with "[//]")
        as ">[$H2]".
      iModIntro. iNext.
      iApply ("IH" with "H1 H2 Hcomb"). }
  Qed.

  Lemma wp_par_ret_right {A1 A2 A} s E m1 a2
    (k : A1 * A2 → free A) ko
    (ϕ : A → iProp Σ) :
    WP m1 @ s; E {{ λ v1, WP (k (v1, a2)) @ s; E {{ ϕ }} }} -∗
    WP (Par m1 (Ret a2) k ko) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hwp".
    iApply (wp_par _ _ _ _ _ _ _ (λ v, WP (k (v, a2)) @ s; E {{ ϕ }}) (λ v, ⌜v = a2⌝)
           with "Hwp")%I.
    { by iApply wp_ret. }
    { iNext. by iIntros (??) "?->". }
  Qed.

  Lemma wp_par_ret_left {A1 A2 A} s E a1 m2
    (k : A1 * A2 → free A) ko
    (ϕ : A → iProp Σ) :
    WP m2 @ s; E {{ λ v2, WP (k (a1, v2)) @ s; E {{ ϕ }} }} -∗
    WP (Par (Ret a1) m2 k ko) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hwp".
    iApply (wp_par _ _ _ _ _ _ _ (λ v, ⌜v = a1⌝) (λ v, WP (k (a1, v)) @ s; E {{ ϕ }})
           with "[] Hwp")%I.
    { by iApply wp_ret. }
    { iNext. by iIntros (??) "->?". }
  Qed.


  Lemma wp_par_ret_ret {A1 A2 A3} s E v1 v2 (k: A1 * A2 → free A3) ko ϕ:
    ▷ WP (k (v1, v2)) @ s; E {{ ϕ }} -∗
    WP (Par (ret v1) (ret v2) k ko) @s; E {{ ϕ }}.
  Proof.
    iIntros "H".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    simpl.
    iSplit.
    { iPureIntro. eauto with step. }
    iIntros (σ' m' Hstep).
    apply step_par_ret_ret in Hstep.
    destruct Hstep; subst.
    iModIntro. iNext. iFrame.
  Qed.


  (* [Stop]-related lemmas. *)
  Lemma wp_eval {A} s E η e k (ϕ: A -> iProp Σ) :
    ▷ WP (eval η e) @ s; E {{ λ v, WP (k v) @ s; E {{ ϕ }} }} -∗
    WP (Stop CEval (η, e) k) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hwp".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iSplit.
    { iPureIntro. eauto with step. }

    iIntros(σ' m' Hstep).
    destruct_step.
    iModIntro. iNext. iFrame "Hsi".
    by iApply wp_bind.
  Qed.

  (* [wp_eval_ret] should not simply be defined as
     [λ s E η e ϕ, wp_eval s E η e ret ϕ] or it would make its premice more difficult to
     work with. *)
  Lemma wp_eval_ret s E η e ϕ :
    ▷ WP (eval η e) @ s; E {{ ϕ }} -∗
    WP (Stop CEval (η, e) ret) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hwp".
    iApply wp_eval.
    iApply (wp_covariant with "Hwp").
    iNext.
    iIntros. by iApply wp_ret.
  Qed.

  Lemma wp_flip {A} s E x (k: bool -> free A) ϕ :
    ▷ (∀ b, WP (k b) @ s; E {{ ϕ }} ) -∗
    WP (Stop CFlip x k) @ s; E {{ ϕ }}.
  Proof.
    iIntros "H".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    simpl.
    iSplit.
    { iPureIntro. eauto with step. }
    iIntros (σ' m') "%Hstep".
    destruct_step.
    iModIntro. iNext.
    iSpecialize ("H" $! b).
    iFrame.
  Qed.

  Lemma wp_ref {A} s E x (k: loc -> free A) ϕ :
    ▷ (∀ ℓ,
         mapsto ℓ (DfracOwn 1) x ∗ meta_token ℓ ⊤ -∗
         WP (k ℓ) @ s; E {{ ϕ }} ) -∗
    WP (Stop CAlloc x k) @ s; E {{ ϕ }}.
  Proof.
    iIntros "H".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    simpl.
    iSplit.
    { iPureIntro. eauto with step. }
    iIntros (σ' m') "%Hstep".
    destruct_step.
    iSpecialize ("H" $! l).
    iPoseProof (gen_heap_alloc with "Hsi") as ">[$ HH]".
    { assumption. }
    iModIntro. iNext.
    iApply ("H" with "HH").
  Qed.

  Lemma wp_store {A} s E ℓ v v' k (ϕ: A → iProp Σ) :
    mapsto ℓ (DfracOwn 1) v -∗
    ▷ (mapsto ℓ (DfracOwn 1) v' -∗ WP (k tt) @ s; E {{ ϕ }}) -∗
    WP (Stop CStore (ℓ, v') k) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hℓ Hwp".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    simpl.
    iSplit.
    { iPureIntro. eauto with step. }
    iIntros (σ' m' Hstep).
    iPoseProof (gen_heap_valid with "Hsi Hℓ")  as "%Hin".
    iMod ((gen_heap_update _ _ _ v') with "Hsi Hℓ") as "[Hsi Hℓ]".
    eapply invert_step_store in Hstep; [| eauto ].
    destruct Hstep. subst.
    iModIntro. iNext. iFrame "Hsi".
    iApply ("Hwp" with "Hℓ").
  Qed.

  Lemma wp_load {A} s E ℓ v dq (k: val -> free A) ϕ :
    mapsto ℓ dq v -∗
    ▷ (mapsto ℓ dq v -∗ WP (k v) @ s; E {{ ϕ }}) -∗
    WP (Stop CLoad ℓ k) @ s; E {{ ϕ }}.
  Proof.
    iIntros "Hℓ Hwp".
    iApply wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    simpl.
    iSplit.
    { iPureIntro. eauto with step. }
    iIntros (σ' m' Hstep).

    iPoseProof (gen_heap_valid with "Hsi Hℓ")  as "%Hin".
    eapply invert_step_load in Hstep; [| eauto ].
    destruct Hstep. subst.
    iModIntro. iNext. iFrame "Hsi".
    iApply ("Hwp" with "Hℓ").
  Qed.

End wp_lemmas.
