From iris.prelude Require Import options.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import base proofmode classes.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import safe.

(* This file defines the predicate [WP]. *)

(* It is heavily inspired from [iris/{bi,program_logic}/weakestpre.v]. *)

(* -------------------------------------------------------------------------- *)

(* For details about these incantations, see
   [iris.base_logic.lib.fancy_updates] and
   [iris.base_logic.lib.gen_heap]. *)

Class osirisGS_gen (Σ: gFunctors) := OsirisG {

  (* This gives us fancy updates (without allowing Later Credits). *)
  osiris_invGS :> invGS_gen HasNoLc Σ;

  (* This gives us a heap, which maps locations to values. *)
  osiris_heapGS :> gen_heapGS loc val Σ;

}.

(* -------------------------------------------------------------------------- *)

(* This is the definition of the predicate [WP]. *)

Section definition.

Context (A: Type).
Context `{!osirisGS_gen Σ}.

(* This is our state interpretation predicate. *)

(* For the moment, it contains just [gen_heap_interp σ], which connects
   the physical heap with the ghost heap. *)

Definition state_interp σ :=
  gen_heap_interp σ.

(* The (open) recursive definition of [wp]. *)

Definition wp_pre
  (s : stuckness)
  (wp: coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ) :
       coPset -d> free A -d> (A -d> iPropO Σ) -d> iPropO Σ
:=
  λ E m φ, (
    ∀ σ,
      state_interp σ ={E,∅}=∗
      match is_ret m with
      | Some v =>
          |={∅,E}=> state_interp σ ∗ φ v
      | None =>
          ⌜can_step (σ, m)⌝ ∗
          ∀ σ' m',
          ⌜step (σ, m) (σ', m')⌝ ={∅}▷=∗
          |={∅,E}=> (state_interp σ' ∗ wp E m' φ)
      end
  )%I.

Local Instance wp_pre_contractive s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E m Φ.
  repeat (f_contractive || f_equiv).
  apply Hwp.
Qed.

(* The following definition is intended to ensure that the usual Iris
   notation is available, e.g.:
     [WP _ @ _ {{ _ }}]
     [WP _ @ _ ?{{ _ }}]).
 *)

Definition wp_def : Wp (iProp Σ) (free A) A stuckness :=
  λ (s : stuckness), fixpoint (wp_pre s).

(* Standard boilerplate. *)

Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Σ _ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal: wp = wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End definition.

(* -------------------------------------------------------------------------- *)

(* More boilerplate, once again inspired by
   [iris/{bi,program_logic}/weakestpre.v] *)

Section boilerplate.

Context {A : Type}.
Context `{!osirisGS_gen Σ}.
Implicit Type s : stuckness.
Implicit Type P : iProp Σ.
Implicit Type φ : A → iProp Σ.
Implicit Type a : A.
Implicit Type m : free A.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma wp_unfold {s E} m {φ} :
  WP m @ s; E {{ φ }} ⊣⊢ wp_pre A s (wp s) E m φ.
Proof.
  rewrite wp_unseal.
  apply (@fixpoint_unfold _ _ _ (wp_pre A s)).
Qed.

Local Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

Global Instance wp_ne s E m n :
  Proper
    (pointwise_relation _ (dist n) ==> dist n)
    (wp s E m).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
  wp_unfold_all.
  repeat ((by rewrite IH; [done|lia|];
              intros v; eapply dist_le; [apply HΦ|lia])
          + (f_contractive || f_equiv)).
Qed.

Global Instance wp_proper s E m :
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (wp s E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance wp_contractive s E m n :
  TCEq (is_ret m) None →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (wp s E m).
Proof.
  intros He Φ Ψ HΦ. wp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
Qed.

Lemma wp_value_fupd' s E (φ: A -> iProp Σ) m v :
  (|={E}=> φ v)%I ⊢ WP (Ret v) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_all.
  iIntros (?)"$".
  iMod "H".
  iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
  iModIntro; iMod "Hmod"; iModIntro; iFrame.
Qed.

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
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP m @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP m @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (_ HE).
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
    (iMod "H1"; iModIntro).
    iApply (fupd_trans _ E1).
    iMod "H1" as "[$H1]".
    iMod "H" as "_".
    iPoseProof (@fupd_mask_subseteq _ _ E2 E1) as "H"; first assumption.
    do 2 (iMod "H"; iModIntro).
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
    do 2 (iMod "Hwp"; iModIntro).
    iDestruct "Hwp" as "[$Hwp]".
    iApply ("IH" with "Hwp"). }
Qed.

End boilerplate.

(* This tactic is supposed to unfold all occurrences of [wp]. *)

Local Ltac wp_unfold_all :=
  rewrite !wp_unfold /wp_pre /=.

(* This tactic unfolds one occurrence of [wp] at the head of the goal. *)

Local Ltac wp_unfold_head :=
  iApply wp_unfold; rewrite /wp_pre /=.

(* This tactic unfolds [wp] applied to the computation [m]. *)

Local Ltac wp_unfold m :=
  setoid_rewrite (wp_unfold m); rewrite /wp_pre /=.

(* -------------------------------------------------------------------------- *)

(* Local tactics. *)

(* [wp_case_is_ret m Hret] performs a case analysis on [m]: either it is
   of the form [ret a], or it is not. In the second branch, the equality
   [is_ret m = None] appears under the name [Hret]. *)

Local Ltac wp_case_is_ret m Hret :=
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

Local Ltac construct_wp_nonret :=
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

Local Ltac intro_state :=
  iIntros (σ) "Hsi".

Local Ltac spec_state H :=
  iSpecialize (H with "Hsi").

Local Ltac release_state :=
  iFrame "Hsi".

(* [tick_wp] is used when the goal is
   [|==> ▷ (state_interp σ' ∗ wp E m' φ)]. *)

Local Ltac tick_wp :=
  iModIntro; iNext; iMod "Hwp"; iModIntro;
  iMod "Hwp" as "[$ Hwp]";
  iModIntro.

(* [step_wp] is used when the hypothesis "Hwp" has the form
     ∀ σ' m', ⌜step (σ, m) (σ', m')⌝ ==∗ ...
              ▷ (state_interp σ' ∗ wp E m' φ)

   It applies this hypothesis to a fact of the form [step (σ, m) _],
   which must appear in the context, and destructs the result. *)

Local Ltac step_wp :=
  iMod ("Hwp" with "[//]") as "Hwp".

(* -------------------------------------------------------------------------- *)

(* The following contains low-level reasoning rules of our program logic. *)

(* These rules are applied in [rules.v]. *)

Section rules.

Context `{!osirisGS_gen Σ}.

(* This technical lemma allows grabbing the state invariant when the
   goal is a [WP] assertion. *)

Lemma wp_grab {A} (m : free A) s E φ :
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

(* The consequence rule of Separation Logic. *)

Lemma wp_covariant {A} s E (m : free A) φ φ' :
  WP m @ s; E {{ φ }} -∗
  (∀ a, φ a -∗ φ' a) -∗
  WP m @ s; E {{ φ' }}.
Proof.
  iLöb as "IH" forall (φ φ' m).
  iIntros "Hwp Himplication".
  wp_unfold_all.
  intro_state. spec_state "Hwp".
  destruct (is_ret m); [ destruct_wp_ret | destruct_wp_nonret ].
  (* Case: [m] is [ret _]. *)
  { release_state.
    iApply ("Himplication" with "Hwp"). }
  (* Case: [m] is not [ret _]. *)
  { iModIntro.
    construct_wp_nonret.
    step_wp.
    tick_wp.
    iApply ("IH" with "Hwp Himplication"). }

Qed.

(* An alternative formulation of the previous rule. *)

Lemma wp_strong_mono' {A} P (m : free A) s E φ :
  P -∗
  WP m @ s; E {{ φ }} -∗
  WP m @ s; E {{ λ a, P ∗ φ a }}.
Proof.
  iIntros "HP Hwp".
  iApply (wp_covariant with "Hwp [HP]").
  iFrame "HP". eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Preservation. *)

(* The assertion [WP m @ s; E {{ φ }}] is preserved by a reduction step. *)

Lemma wp_step {A σ σ'} {m m' : free A} {s E φ} :
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

(* [wp_steps] is an iterated version of [wp_step]. *)
Lemma wp_steps n :
  forall {A σ1 σn} {m1 mn : free A} {s E φ},
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

Lemma wp_not_stuck {A} {σ} {m : free A} s E {φ} :
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
Lemma wp_can_step {A σ φ} {m: free A} {s E}:
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
Lemma wp_can_step' {A σ φ} {m: free A} {s E}:
  state_interp σ -∗
  wp s E m φ ={E}=∗ ⌜can_step (σ, m) ∨ is_ret m <> None ⌝.
Proof.
  iIntros "??";
    iPoseProof (wp_can_step with "[$][$]") as "?".
  iApply (fupd_plain_mask_empty with "[$]").
Qed.

Lemma wp_progress {A σ1 σn} {m1 mn : free A} {φ s E} n :
  nsteps step n (σ1, m1) (σn, mn) →
  state_interp σ1 -∗
  wp s E m1 φ ={E,∅}=∗
  |={∅}▷=>^n |={∅}=> ⌜~ stuck (σn, mn)⌝.
Proof.
  iIntros (Hsteps) "??".
  iMod ((wp_steps n Hsteps) with "[$][$]") as "H".
  iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros ">[Hsi Hwp]".
  by iPoseProof (wp_not_stuck with "[$][$]") as ">$".
Qed.

End rules.

Section Adequacy.
  Import uPred.

  (* Example of a proposition [φ]:
       match is_ret m2 with
       | Some v => φ' v ={top, ∅}=∗ ⌜φ⌝
       | None =>  ⌜ ~ stuck (σ2, m2) ⌝
       end)) → *)
  Lemma wp_strong_adequacy_gen Σ `{!invGpreS Σ}
        `{Hstore: @gen_heapGS loc val Σ loc_eq_decision loc_countable}
        s m1 σ1 n σ2 m2 (φ: Prop) :
  nsteps step n (σ1, m1) (σ2, m2) →
    (∀ `{Hinv : invGS_gen HasNoLc Σ},
      ⊢ |={⊤}=> ∃
         (φ' : val → iProp Σ),
     let _ : osirisGS_gen Σ := OsirisG Σ Hinv Hstore
     in
     state_interp σ1 ∗
     wp s top m1 φ' ∗
     ( state_interp σ2 -∗
       ⌜φ⌝)) →
  φ.
  Proof.
    intros Hsteps H.
    eapply pure_soundness.
    eapply (step_fupdN_soundness_gen _ HasNoLc n O).
    iIntros (Hinv) "_".
    iMod H as (φ') "(Hsi&Hwp&Himpl)".
    iMod ((wp_steps _ Hsteps) with "[$][$]") as "Htest".

    iAssert (|={∅}▷=>^n |={∅}=> ⌜φ⌝)%I with "[-]" as "H"; last first.
    { destruct n; first done.
      by iApply step_fupdN_S_fupd. }

    iApply (step_fupdN_wand with "Htest").
    iMod 1 as "[? Hwp]".
    destruct (is_ret m2) eqn:E2.
    { rewrite (invert_is_ret_Some E2).
      rewrite !wp_unfold/wp_pre/=.
      iMod ("Hwp" with "[$]") as ">[??]".
      iPoseProof (@fupd_mask_subseteq _ _ top ∅) as ">Hmod"; first done;
        iModIntro.
      iApply ("Himpl" with "[$]"). }
    { iApply "Himpl".
      iFrame.
      by iPoseProof (@fupd_mask_subseteq _ _ top ∅) as ">Hmod"; first done. }
  Qed.

End Adequacy.

(* Adequacy.

Lemma wp_adequate {A} {σ} {m : free A} s E {φ} :
  state_interp σ -∗
  WP m @ s; E {{ λ a, ⌜ φ a ⌝ }} -∗
  |={E,∅}=> ⌜ ∀ a, m = ret a → φ a ⌝.
Proof.
  iIntros "Hsi Hwp".
  wp_unfold m. spec_state "Hwp".
  wp_case_is_ret m Hret; [ destruct_wp_ret | destruct_wp_nonret ].
  (* Case: [m] is [ret a]. *)
  { iDestruct "Hwp" as "%". iPureIntro. intros a' ?. congruence. }
  (* Case: [m] can step. *)
  { iPureIntro. intros ? ->. simpl in *. congruence. }
Qed.

Local Open Scope nat_scope. (* TODO *)

(* TODO this iterated modality should exist somewhere in the Iris library? *)

Fixpoint tonight n (P : iProp Σ) :=
  match n with
  | 0 => P
  | S n => |==> ▷ (tonight n P)
  end%I.

Lemma now_tonight (P : iProp Σ) :
  ∀ n, P -∗ tonight n P.
Proof.
  induction n; simpl.
  { eauto. }
  { iIntros "H". iModIntro. iNext. iApply (IHn with "H"). }
Qed.

(* A combination of preservation, progress, and adequacy. *)

Lemma wp_steps {A n σ σ'} {m m' : free A} s E {φ : A → Prop} :
  steps n (σ, m) (σ', m') →
  state_interp σ -∗
  WP m @ s; E {{ a, ⌜ φ a ⌝ }} -∗
  tonight n
  ⌜ ¬ stuck (σ', m') ∧ ∀ a, m' = Ret a → φ a ⌝.
Proof.
  intros Hsteps.
  remember (σ, m) as c eqn:Hc.
  remember (σ', m') as c' eqn:Hc'.
  revert n c c' Hsteps σ m σ' m' Hc Hc'.
  induction 1; intros; simplify_eq; iIntros "Hsi Hwp".
  (* Case: zero steps are taken. *)
  { iDestruct (wp_not_stuck with "Hsi Hwp") as "%".
    iDestruct (wp_adequate with "Hsi Hwp") as "%".
    iApply now_tonight. iPureIntro. tauto. }
  (* Case: [n] is nonzero. *)
  { (* [m] steps to [m1]. *)
    match goal with h: step _ ?m |- _ => destruct m as [σ1 m1] end.
    specialize (IHHsteps _ _ _ _ eq_refl eq_refl).
    simpl.
    (* [WP m ...] implies [WP m1 ...]. *)
    iDestruct (wp_step with "Hsi Hwp") as ">[Hsi Hwp]".
    { eassumption. }
    (* Eliminate two modalities. *)
    iModIntro. iNext.
    (* The induction hypothesis can then be exploited. *)
    iApply (IHHsteps with "Hsi Hwp"). }
Qed.

(* TODO is this lemma useful? If so, move it to safe.v where it belongs. *)

Lemma prove_initially_safe {A} :
  ∀ n σ {m : free A} {φ : A → Prop},
  (
    ∀ j σ' m',
    j ≤ n →
    steps j (σ, m) (σ', m') →
    ¬ stuck (σ', m') ∧ ∀ a, m' = Ret a → φ a
  ) →
  initially_safe n (σ, m) (λ _ a, φ a).
Proof.
  induction n; intros σ m φ H.
  { eauto using initially_safe_zero. }
  triplicity σ m Hm.

  (* Case: [m] is [ret a]. *)
  { eapply initially_safe_ret.
    (* The goal is now [φ a]. *)
    eapply (H 0 σ (ret a)); eauto with lia steps. }

  (* Case: [(σ, m)] can step. *)
  { right. split; [ eauto |]. intros (σ', m') Hstep.
    eapply IHn.
    intros j σ'' m'' ? Hsteps.
    eapply (H (S j)); eauto with lia steps. }

  (* Case: [(σ, m)] is stuck. *)
  { exfalso. eapply (H 0); eauto with lia steps. }

Qed.

Lemma prove_safe {A} σ {m : free A} {φ : A → Prop} :
  (
    ∀ j σ' m',
    steps j (σ, m) (σ', m') →
    ¬ stuck (σ', m') ∧ ∀ a, m' = Ret a → φ a
  ) →
  safe (σ, m) (λ _ a, φ a).
Proof.
  unfold safe. eauto using prove_initially_safe.
Qed.

(* TODO where do we go from here? *) *)

(* -------------------------------------------------------------------------- *)

(* The parallel composition rule of Separation Logic. *)

(* To prove that [Par m1 m2 k ko] satisfies [φ], one must provide
   two postconditions [φ1] and [φ2] and *separately* prove that:
   - [m1] satisfies [φ1]
   - [m2] satisfies [φ2]
   - for all results [a1] and [a2] that satisfy [φ1] and [φ2],
     the application of the the continuation [k]
     to the pair [(a1, a2)] satisfies [φ]. *)

(* The lemma could be strengthened by placing a ▷ modality in front of the
   third premise, but I doubt that this would be useful, so I remove it.
   We do not want the user to rely on the fact that a join point counts
   as a step. *)
