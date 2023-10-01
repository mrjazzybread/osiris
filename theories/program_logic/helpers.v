From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe wp.

(* This tactic is supposed to unfold all occurrences of [wp]. *)

Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

(* This tactic unfolds one occurrence of [wp] at the head of the goal. *)

Ltac wp_unfold_head :=
  iApply wp_unfold; rewrite /wp_pre /=.

(* This tactic unfolds [wp] applied to the computation [m]. *)

Ltac wp_unfold m :=
  setoid_rewrite (wp_unfold m); rewrite /wp_pre /=.

Section boilerplate.

Context {A : Type}.
Context `{!osirisGS Σ}.
Implicit Type s : stuckness.
Implicit Type P : iProp Σ.
Implicit Type φ : A → iProp Σ.
Implicit Type a : A.
Implicit Type m : micro A.

(* [fupd_wp] states that to prove a WP behind a modality is enough to prove the
   WP without modality. This is particularly useful when using invariants. *)
Lemma fupd_wp s E m (φ: A -> iProp Σ) :
  (|={E}=> WP m @ s; E {{ φ }}) ⊢ WP m @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_all.
  by destruct (is_ret m);
  iIntros (?)"?";
  iMod ("H" with "[$]") as "H".
Qed.

Lemma wp_strong_mono s1 s2 E1 E2 m Φ Ψ :
  E1 ⊆ E2 →
  WP m @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP m @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (HE).
  iLöb as "IH" forall (m).
  iIntros "H1 Himpl".
  wp_unfold_all.
  iIntros (?)"?". iSpecialize ("H1" with "[$]").
  iMod (fupd_mask_subseteq E1) as "H"; first assumption.
  iMod "H1".
  iModIntro.
  destruct (is_ret m).
  { iMod "H1" as "[$?]". iMod "H" as "_".
    iApply ("Himpl" with "[$]"). }
  { iDestruct "H1" as "[% H1]".
    iSplit; first done.
    iIntros(? m' ?).
    iSpecialize ("H1" with "[//]").
    (iMod "H1"; iModIntro).
    iModIntro.
    iMod "H1".
    iDestruct "H1" as "[$H1]".
    iMod "H" as "_".
    iPoseProof (@fupd_mask_subseteq _ _ E2 E1) as "H"; first assumption.
    do 2 iMod "H".
    iApply ("IH" $! m' with "H1 Himpl"). }
Qed.

Lemma wp_fupd s E m Φ :
  WP m @ s; E {{ v, |={E}=> Φ v }} ⊢ WP m @ s; E {{ Φ }}.
Proof.
  iLöb as "IH" forall (m).
  iIntros "Hwp".
  wp_unfold_all.
  iIntros(σ) "Hsi".
  iSpecialize ("Hwp" with "Hsi").
  iMod "Hwp". iModIntro.
  destruct (is_ret m).
  { iMod "Hwp" as "[$$]". }
  { iDestruct "Hwp" as "[%Hcan_step Hwp]". iSplit; first done.
    iIntros (σ' m' Hstep).
    iSpecialize ("Hwp" with "[//]").
    iMod "Hwp".
    do 2 iModIntro.
    iMod "Hwp"; iModIntro.
    iDestruct "Hwp" as "[$Hwp]".
    iApply ("IH" with "Hwp"). }
Qed.

End boilerplate.

(* -------------------------------------------------------------------------- *)

(* Local tactics. *)

(* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
   of the form [ret a], or it is not. In the second branch, the equality
   [is_ret m = None] appears under the name [Hret]. *)

Ltac wp_case_is_ret m Hret :=
  case_eq (is_ret m); [
    intros ? Hret;
    apply invert_is_ret_Some in Hret; subst m
  | intros Hret
  ].

(* The following tactics corresponds to the branch [is_ret _ = Some _] in
   the definition of [wp]. This branch is a conjunction
     state_interp σ ∗ φ v
   [destruct_wp_ret] is used when this form appears in the hypothesis "Hwp". *)

Ltac destruct_wp_ret :=
  iMod "Hwp"; iModIntro;
  iMod "Hwp" as "[Hsi Hwp]"; iModIntro.

(* The following two tactics correspond to the branch [is_ret _ = None] in
   the definition of [wp]. This branch is a conjunction
     ⌜can_step (σ, m)⌝ ∗ ∀ σ' m', ...
   [construct_wp_nonret] is used when this form appears in the goal.
   [destruct_wp_nonret] is used when it appears in the hypothesis "Hwp". *)

Ltac construct_wp_nonret :=
  iSplitR; [
    (* Prove [can_step]: *)
    iPureIntro; eauto with step can_step
  | (* Introduce a hypothetical step: *)
    iIntros (σ' m') "%Hstep"
  ].

Ltac destruct_wp_nonret :=
  iMod "Hwp" as "[%Hcanstep Hwp]".

(* Working with the state interpretation invariant. *)

(* [intro_state] introduces [σ] and [state_interp σ]. *)
(* [spec_state H] specializes the hypothesis H with [state_interp σ]. *)
(* [release_state] abandons [state_interp σ]. *)

Ltac intro_state :=
  iIntros (σ) "Hsi".

Ltac spec_state H :=
  iSpecialize (H with "Hsi").

Ltac release_state :=
  iFrame "Hsi".

(* [tick_wp] is used when the goal is
   [|==> ▷ (state_interp σ' ∗ wp E m' φ)]. *)

Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro;
  iMod "Hwp" as "[$ Hwp]";
  iModIntro.

(* [step_wp] is used when the hypothesis "Hwp" has the form
     ∀ σ' m', ⌜step (σ, m) (σ', m')⌝ ==∗ ...
              ▷ (state_interp σ' ∗ wp E m' φ)

   It applies this hypothesis to a fact of the form [step (σ, m) _],
   which must appear in the context, and destructs the result. *)

Ltac step_wp :=
  iMod ("Hwp" with "[//]") as "Hwp".

(* -------------------------------------------------------------------------- *)

(* The following contains low-level reasoning rules of our program logic. *)

(* These rules are applied in [rules.v]. *)

Section rules.

Context `{!osirisGS Σ}.

(* This technical lemma allows grabbing the state invariant when the
   goal is a [WP] assertion. *)

Lemma wp_grab {A} (m : micro A) s E φ :
  (∀ σ, state_interp σ -∗
        |={E,∅}=> |={∅,E}=> state_interp σ ∗ WP m @ s; E {{ φ }}
  ) -∗
  WP m @ s; E {{ φ }}.
Proof.
  iIntros "Hwp". wp_unfold m.
  intro_state. spec_state "Hwp".
  iMod "Hwp". iMod "Hwp" as "[Hsi Hwp]".
  spec_state "Hwp". eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Preservation. *)

(* The assertion [WP m @ s; E {{ φ }}] is preserved by a reduction step. *)

Lemma wp_step {A σ σ'} {m m' : micro A} {s E φ} :
  step (σ, m) (σ', m') →
  state_interp σ -∗
  WP m @ s; E {{ φ }} ={E,∅}=∗
  |={∅}▷=> |={∅,E}=> (
    state_interp σ' ∗
    WP m' @ s; E {{ φ }}
  ).
Proof.
  intro Hstep.
  iIntros "Hsi Hwp".
  wp_unfold m. spec_state "Hwp".
  assert (is_not_ret m) as -> by eauto using can_step_is_not_ret with step.
  destruct_wp_nonret.
  step_wp.
  eauto.
Qed.

(* [wp_preservation] is an iterated version of [wp_step]. *)
Lemma wp_preservation n :
  forall {A σ1 σn} {m1 mn : micro A} {s E φ},
  nsteps step n (σ1, m1) (σn, mn) →
  state_interp σ1 -∗
  wp s E m1 φ ={E,∅}=∗
  |={∅}▷=>^n |={∅,E}=> state_interp σn ∗ wp s E mn φ.
Proof.
  induction n as [ | n IHn] => A σ1 σn m1 mn s E φ /=.
  { iIntros ([->->]%invert_nsteps_0%pair_equal_spec) "$$".
    iApply fupd_mask_subseteq; by apply empty_subseteq. }
  { iIntros (([σm mm]&Hstep&Hsteps)%nsteps_S_inv) "??".
    iPoseProof ((wp_step Hstep) with "[$][$]") as ">Hstep".
    iModIntro.
    iApply ((step_fupdN_wand _ _ 1) with "Hstep").
    iIntros "H".
    destruct n.
    { apply invert_nsteps_0 in Hsteps.
      simplify_eq/=. done. }
    { simpl. iMod "H" as "[??]".
      iPoseProof (IHn _ _ _ _ _ _ _ _ Hsteps) as "IH".
      by iMod ("IH" with "[$][$]"). } }
Qed.

(* Progress. *)

Opaque stuck. (* TODO *)

(* [wp_not_stuck] states that: The "Weakest Precondition" ensures the progress
   of computations.  *)
Lemma wp_not_stuck {A} {σ} {m : micro A} s E {φ} :
  state_interp σ -∗
  WP m @ s; E {{ φ }} -∗
  |={E,∅}=> ⌜ ¬ stuck (σ, m) ⌝.
Proof.
  iIntros "Hsi Hwp".
  wp_unfold m. spec_state "Hwp".
  wp_case_is_ret m Hret; [ iMod "Hwp" | destruct_wp_nonret ];
    iModIntro; iPureIntro.
  (* Case: [m] is [ret a]. *)
  (* [ret a] is not stuck. *)
  { eauto using invert_stuck_ret. }
  (* Case: [m] can step. *)
  (* A configuration that can step is not stuck. *)
  { eauto using can_step_not_stuck. }
Qed.

(* The following lemma state that given [wp _ m _] and a state interpretation of
   [σ], the configuration [(σ, m)] can take a step. *)
Lemma wp_can_step {A σ φ} {m: micro A} {s E}:
  state_interp σ -∗
  wp s E m φ ={E,∅}=∗ ⌜can_step (σ, m) ∨ is_ret m <> None ⌝.
Proof.
  iIntros "? Hwp".
  wp_unfold_all.
  iMod ("Hwp" with "[$]") as "Hwp".
  destruct (is_ret m).
  { iMod "Hwp". iApply fupd_mask_intro; [ set_solver | iIntros "_" ].
    iPureIntro. right; by inversion 1. }
  { iDestruct "Hwp" as "[[%x %Hstep] _]". destruct x as [σ' m'].
    iModIntro.  eauto with step. }
Qed.

(* Ditto for a different mask. *)
Lemma wp_can_step' {A σ φ} {m: micro A} {s E}:
  state_interp σ -∗
  wp s E m φ ={E}=∗ ⌜can_step (σ, m) ∨ is_ret m <> None ⌝.
Proof.
  iIntros "??";
    iPoseProof (wp_can_step with "[$][$]") as "?".
  iApply (fupd_plain_mask_empty with "[$]").
Qed.
End rules.
