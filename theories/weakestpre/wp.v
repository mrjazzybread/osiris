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
      state_interp σ -∗
      match is_ret m with
      | Some v =>
          state_interp σ ∗ φ v
      | None =>
          ⌜can_step (σ, m)⌝ ∗
          ∀ σ' m',
          ⌜step (σ, m) (σ', m')⌝ ==∗
          ▷ (state_interp σ' ∗ wp E m' φ)
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

Local Ltac destruct_wp_ret :=
  iDestruct "Hwp" as "[Hsi Hwp]".

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

Local Ltac destruct_wp_nonret :=
  iDestruct "Hwp" as "[%Hcanstep Hwp]".

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
  iModIntro; iNext; release_state.

(* [step_wp] is used when the hypothesis "Hwp" has the form
     ∀ σ' m', ⌜step (σ, m) (σ', m')⌝ ==∗ ...
              ▷ (state_interp σ' ∗ wp E m' φ)

   It applies this hypothesis to a fact of the form [step (σ, m) _],
   which must appear in the context, and destructs the result. *)

Local Ltac step_wp :=
  iDestruct ("Hwp" with "[//]") as ">[Hsi Hwp]".

(* -------------------------------------------------------------------------- *)

(* The following are the reasoning rules of our program logic. *)

(* These rules are applied by the tactics in [tactics.v]. *)

Section rules.

Context `{!osirisGS_gen Σ}.

(* This technical lemma allows grabbing the state invariant when the
   goal is a [WP] assertion. *)

Lemma wp_grab {A} (m : free A) s E φ :
  (∀ σ, state_interp σ -∗
        state_interp σ ∗ WP m @ s; E {{ φ }}
  ) -∗
  WP m @ s; E {{ φ }}.
Proof.
  iIntros "Hwp". wp_unfold m.
  intro_state. spec_state "Hwp".
  iDestruct "Hwp" as "[Hsi Hwp]".
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
  { construct_wp_nonret.
    step_wp.
    tick_wp.
    iApply ("IH" with "Hwp Himplication"). }

Qed.

(* An alternative formulation of the previous rule. *)

Lemma wp_strong_mono {A} P (m : free A) s E φ :
  P -∗
  WP m @ s; E {{ φ }} -∗
  WP m @ s; E {{ λ a, P ∗ φ a }}.
Proof.
  iIntros "HP Hwp".
  iApply (wp_covariant with "Hwp [HP]").
  iFrame "HP". eauto.
Qed.

(* The return rule. *)

Lemma wp_ret {A} s E (a : A) φ :
  φ a ⊢
  WP (Ret a) @ s; E {{ φ }}.
Proof.
  wp_unfold_all. iIntros. iFrame.
Qed.

(* The inverse return rule. *)

Lemma invert_wp_ret {A} s E (a : A) φ :
  ∀ σ, state_interp σ -∗
  WP (Ret a) @ s; E {{ φ }} -∗
  state_interp σ ∗ φ a.
Proof.
  intro_state. iIntros "Hwp".
  wp_unfold_all. spec_state "Hwp".
  eauto.
Qed.

(* The inverse crash rule. *)

Lemma invert_wp_crash {A s E φ} :
  ∀ σ, state_interp σ -∗
  WP (@crash A) @ s; E {{φ}} -∗
  False.
Proof.
  intro_state. iIntros "Hwp".
  wp_unfold_all. spec_state "Hwp".
  destruct_wp_nonret. eauto with invert_can_step.
Qed.

(* The inverse [next] rule. *)

Lemma invert_wp_next {A s E φ} :
  ∀ σ, state_interp σ -∗
  WP (@Next A) @ s; E {{ φ }} -∗
  False.
Proof.
  intro_state. iIntros "Hwp".
  wp_unfold_all. spec_state "Hwp".
  destruct_wp_nonret. eauto with invert_can_step.
Qed.

(* A reasoning rule for [try]. *)

(* Our definition of [WP] forbids [m1] from reducing to [Next], so the
   failure continuation [ko] is dead. Therefore, no proof obligation
   bears on [ko]. *)

Lemma wp_try {A1 A2} s E (m1: free A1) (m2: A1 → free A2) ko ψ :
  WP m1 @ s; E {{ λ v, WP (m2 v) @ s; E {{ ψ }} }} ⊢
  WP (try m1 m2 ko) @ s; E {{ ψ }}.
Proof.
  iLöb as "IH" forall (m1 m2 ko ψ).
  iIntros "Hwp".
  wp_unfold m1.
  wp_case_is_ret m1 Hret.

  (* Case: [m1] is [ret _]. *)
  (* The result is immediate. *)
  { by iApply wp_grab. }

  (* Case: [m1] is not [ret _]. *)
  {
    (* Unfold and simplify the goal and hypothesis. *)
    wp_unfold_all.
    intro_state.
    spec_state "Hwp".
    destruct_wp_nonret.
    (* [try m1 m2 ko] cannot be [ret _]. *)
    pose proof (is_not_ret_try m1 m2 ko Hcanstep) as ->.
    construct_wp_nonret.
    (* We must prove that every reduct of [try m1 m2 ko] is safe. *)
    (* Because [m1] can step, a reduct of [try m1 m2 ko] must be
       of the form [try m'1 m2 ko], where [m'1] is a reduct of [m1]. *)
    destruct (invert_step_try Hstep Hcanstep) as (m'1 & Hstep' & ->).
    clear Hstep. rename Hstep' into Hstep.
    (* The hypothesis can then be further exploited. *)
    step_wp. tick_wp. iApply "IH". iApply "Hwp".
  }

Qed.

(* A binary version of the previous lemma. *)

(* This version must be preferred when the proof of [m1] requires a case
   analysis. The scope of the case analysis is then limited to the first
   premise, so the proof of [m2] is not duplicated. *)

Lemma wp_try_binary {A1 A2} s E (m1: free A1) (m2: A1 → free A2) ko φ ψ :
  WP m1 @ s; E {{ φ }} ⊢
  (∀ v, φ v -∗ WP (m2 v) @ s; E {{ ψ }})-∗
  WP (try m1 m2 ko) @ s; E {{ ψ }}.
Proof.
  iIntros "Hm1 Hm2".
  iApply wp_try.
  iApply (wp_covariant with "Hm1 Hm2").
Qed.

(* The Bind rule of Separation Logic. *)

Lemma wp_bind {A1 A2} s E (m1: free A1) (m2: A1 → free A2) ψ :
  WP m1 @ s; E {{ λ v, WP (m2 v) @ s; E {{ ψ }} }} ⊢
  WP (bind m1 m2) @ s; E {{ ψ }}.
Proof.
  rewrite bind_as_try. eauto using wp_try.
Qed.

(* A binary version of the previous lemma. *)

(* This version must be preferred when the proof of [m1] requires a case
   analysis. The scope of the case analysis is then limited to the first
   premise, so the proof of [m2] is not duplicated. *)

Lemma wp_bind_binary {A1 A2} s E (m1: free A1) (m2: A1 → free A2) φ ψ :
  WP m1 @ s; E {{ φ }} ⊢
  (∀ v, φ v -∗ WP (m2 v) @ s; E {{ ψ }}) -∗
  WP (bind m1 m2) @ s; E {{ ψ }}.
Proof.
  iIntros "Hm1 Hm2".
  iApply wp_bind.
  iApply (wp_covariant with "Hm1 Hm2").
Qed.

(* -------------------------------------------------------------------------- *)

(* Preservation. *)

(* The assertion [WP m @ s; E {{ φ }}] is preserved by a reduction step. *)

Lemma wp_step {A σ σ'} {m m' : free A} {s E φ} :
  step (σ, m) (σ', m') →
  state_interp σ -∗
  WP m @ s; E {{ φ }} ==∗
  ▷ (
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
  tick_wp.
  eauto.
Qed.

(* Progress. *)

Opaque stuck. (* TODO *)

Lemma wp_not_stuck {A} {σ} {m : free A} s E {φ} :
  state_interp σ -∗
  WP m @ s; E {{ φ }} -∗
  ⌜ ¬ stuck (σ, m) ⌝.
Proof.
  iIntros "Hsi Hwp".
  wp_unfold m. spec_state "Hwp".
  wp_case_is_ret m Hret; [| destruct_wp_nonret ]; iPureIntro.
  (* Case: [m] is [ret a]. *)
  (* [ret a] is not stuck. *)
  { eauto using invert_stuck_ret. }
  (* Case: [m] can step. *)
  (* A configuration that can step is not stuck. *)
  { eauto using can_step_not_stuck. }
Qed.

(* Adequacy. *)

Lemma wp_adequate {A} {σ} {m : free A} s E {φ} :
  state_interp σ -∗
  WP m @ s; E {{ λ a, ⌜ φ a ⌝ }} -∗
  ⌜ ∀ a, m = ret a → φ a ⌝.
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

(* TODO where do we go from here? *)

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

Lemma wp_par {A1 A2 A3 s E m1 m2} {k: A1 * A2 → free A3} {ko φ} φ1 φ2:
  WP m1 @ s ; E {{ φ1 }} ⊢
  WP m2 @ s ; E {{ φ2 }} -∗
  (
    ∀ a1 a2,
    φ1 a1 -∗ φ2 a2 -∗
    WP (k (a1, a2)) @ s; E {{ φ }}
  )
  -∗ WP (Par m1 m2 k ko) @ s ; E {{ φ }}.
Proof.
  iLöb as "IH" forall (m1 m2).
  iIntros "H1 H2 Hjoin".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  destruct_step.
  (* We now examine each of the ways in which [Par m1 m2 k ko] can step. *)
  { (* Case: [StepParRetRet] *)
    iDestruct (invert_wp_ret with "Hsi H1") as "[Hsi H1]".
    iDestruct (invert_wp_ret with "Hsi H2") as "[Hsi H2]".
    tick_wp.
    iApply ("Hjoin" with "H1 H2"). }
  { (* Case: [StepParCrashLeft] *)
    iDestruct (invert_wp_crash with "Hsi H1") as "%".
    tauto. }
  { (* Case: [StepCrashRight] *)
    iDestruct (invert_wp_crash with "Hsi H2") as "%".
    tauto. }
  { (* Case: [StepNextLeft] *)
    iDestruct (invert_wp_next with "Hsi H1") as "%".
    tauto. }
  { (* Case: [StepNextRight] *)
    iDestruct (invert_wp_next with "Hsi H2") as "%".
    tauto. }
  { (* Case: [StepParLeft] *)
    (* [m1] steps to [m'1]. *)
    iDestruct (wp_step Hstep with "Hsi H1") as ">[Hsi H1]".
    tick_wp.
    iApply ("IH" with "H1 H2 Hjoin"). }
  { (* Case: [StepParRight] *)
    iDestruct (wp_step Hstep with "Hsi H2") as ">[Hsi H2]".
    tick_wp.
    iApply ("IH" with "H1 H2 Hjoin"). }
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas offer reasoning rules for each of the system calls,
   that is, for computations of the form [Stop c x y]. They are simple
   consequences of the operational behavior of these system calls. *)

(* [CEval]. *)

Lemma wp_eval {A} s E η e (k : val → free A) ko φ :
  ▷ WP (eval η e) @ s; E {{ λ v, WP (k v) @ s; E {{ φ }} }} ⊢
  WP (Stop CEval (η, e) k ko) @ s; E {{ φ }}.
Proof.
  iIntros "Hwp".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  destruct_step.
  tick_wp.
  by iApply wp_try.
Qed.

(* A special case of the previous lemma for the continuation [ret]. *)

Lemma wp_eval_ret s E η e ko φ :
  ▷ WP (eval η e) @ s; E {{ φ }} ⊢
  WP (Stop CEval (η, e) ret ko) @ s; E {{ φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_eval.
  iNext.
  iApply (wp_covariant with "Hwp").
  iIntros. by iApply wp_ret.
Qed.

(* [CFlip]. *)

(* This is the Hoare rule for a coin flip. The result can be any Boolean
   value [b], so the computation [k b] must be proved safe for every
   possible value of [b]. *)

Lemma wp_flip {A} s E x (k: bool → free A) ko φ :
  ▷ (∀ b, WP (k b) @ s; E {{ φ }}) ⊢
  WP (Stop CFlip x k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  destruct_step.
  tick_wp.
  by iApply "H".
Qed.

(* [CAlloc]. *)

(* The standard memory allocation rule of Separation Logic. *)

Lemma wp_alloc {A} s E v (k : loc → free A) ko φ :
  ▷ (
    ∀ l,
    mapsto l (DfracOwn 1) v ∗ meta_token l ⊤ -∗
     WP (k l) @ s; E {{ φ }}
  ) ⊢
  WP (Stop CAlloc v k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  destruct_step.
  (* Allocate a new location in the ghost heap. *)
  iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi HH]".
  { eassumption. }
  tick_wp.
  iApply ("H" with "HH").
Qed.

(* [CStore]. *)

(* The standard memory write rule of Separation Logic. *)

Lemma wp_store {A} s E l v v' (k : unit → free A) ko φ :
  mapsto l (DfracOwn 1) v ⊢
  ▷ (
    mapsto l (DfracOwn 1) v' -∗
    WP (k tt) @ s; E {{ φ }}
  ) -∗
  WP (Stop CStore (l, v') k ko) @ s; E {{ φ }}.
Proof.
  iIntros "Hl Hwp".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  (* Argue that [l] must be in the domain of the ghost heap. *)
  iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
  (* Thus, the reduction step must be a successful step. *)
  eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
  (* Update the ghost heap. *)
  iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  tick_wp.
  iApply ("Hwp" with "Hl").
Qed.

(* The standard memory load rule of Separation Logic. *)

Lemma wp_load {A} s E l v dq (k: val → free A) ko φ :
  mapsto l dq v ⊢
  ▷ (
    mapsto l dq v -∗
    WP (k v) @ s; E {{ φ }}
  ) -∗
  WP (Stop CLoad l k ko) @ s; E {{ φ }}.
Proof.
  iIntros "Hl Hwp".
  wp_unfold_head.
  intro_state.
  construct_wp_nonret.
  (* Argue that [l] must be in the domain of the ghost heap. *)
  iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
  (* Thus, the reduction step must be a successful step. *)
  eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.
  tick_wp.
  iApply ("Hwp" with "Hl").
Qed.

(* -------------------------------------------------------------------------- *)

(* Simplification is sound. *)

(* That is, as announced in semantics/simplification.v, if [simplify n m ms]
   holds then the safety of the simplified program [ms] implies the safety
   of the more complex original program [ms]. *)

Local Lemma wp_simplify {A} n (m ms : free A) s E φ :
  WP ms @ s ; E {{ φ }} -∗
  ⌜ simplify n m ms ⌝ -∗
  WP m  @ s ; E {{ φ }}.
Proof.
  (* Proceed by Löb induction. *)
  iLöb as "IH" forall (n m ms).
  (* Then, perform well-founded induction over [n]. *)
  iInduction n as (? & ?) "IHn"
    using (well_founded_induction lt_wf)
    forall (m ms).
  (* Introduce the hypotheses. *)
  iIntros "Hwp" (Hsimp).

  (* Examine [m]. *)
  wp_case_is_ret m Hretm.
  (* If [m] is [ret a], then [ms] is also [ret a], so we are done. *)
  { clarify_simplify. iAssumption. }
  (* Thus, in the following, we assume [m] is not [ret _]. *)

  (* Begin unfolding the definition of [WP m ...]. *)
  wp_unfold m; rewrite Hretm. intro_state.

  (* Examine [ms]. *)
  wp_case_is_ret ms Hretms.
  (* Case: [ms] is [ret _]. *)
  { (* Prove that [m] is able to step. *)
    construct_wp_nonret; [ eauto using invert_simplify_ret |].
    (* Examine one step of [m] to [m']. The simulation diagram in this case
       tells us that this reduction step takes us closer to [ret a].
       That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
    pose proof (simplify_ret_step_diagram Hsimp Hstep)
      as (n' & ? & ? & ?); subst.
    (* We are then able to use the inner induction hypothesis. *)
    tick_wp.
    iApply ("IHn" with "[//] Hwp [//]"). }
  (* Thus, in the following, we assume [ms] is not [ret _]. *)

  (* Then, [WP ms ...] implies than [ms] can step.
     This implies that [m], too, can step. *)
  iAssert (⌜ can_step (σ, m) ⌝)%I as "%".
  { wp_unfold ms. spec_state "Hwp"; rewrite Hretms. destruct_wp_nonret.
    eauto using invert_simplify_can_step. }
  construct_wp_nonret.

  (* We now examine an arbitrary step of [m] to [m']. *)
  (* Exploit the main simulation diagram. *)
  pose proof (simplify_step_diagram Hsimp Hstep)
    as (ms' & n' & i & Hstep' & Hsimp' & Hcases);
  clear Hsimp Hstep.
  destruct_simplify_step_diagram.

  (* Case: the reduction step disappears through the diagram. *)
  { tick_wp. iApply ("IHn" with "[//] Hwp [//]"). }

  (* Case: the reduction step is preserved through the diagram. *)
  (* We can now commit to stepping [ms] -- a commitment which we have
     carefully avoided up to this point. *)
  iClear "IHn".
  wp_unfold ms; rewrite Hretms. spec_state "Hwp". destruct_wp_nonret.
  step_wp. tick_wp. (* The induction hypothesis becomes usable! *)
  (* Then, the result follows from the induction hypothesis. *)
  iApply ("IH" with "Hwp [//]").
Qed. (* yes! *)

(* A corollary, for public use: [simp] is sound. *)

Lemma wp_simp {A} (m m' : free A) s E φ :
  simp m m' →
  WP m' @ s ; E {{ φ }} ⊢
  WP m  @ s ; E {{ φ }}.
Proof.
  iIntros (Hsimp) "Hwp".
  apply simp_simplify in Hsimp.
  destruct Hsimp as (n & Hsimp).
  iApply (wp_simplify with "Hwp [//]").
Qed.

(* --------------------------------------------------------------------------*)

(* The following three lemmas are special cases of [wp_simp]. *)

(* For this reason, they should not be used. TODO *)

Lemma wp_par_ret_left {A1 A2 A} s E a1 m2 (k : A1 * A2 → free A) ko φ :
  WP m2 @ s; E {{ λ v2, WP (k (a1, v2)) @ s; E {{ φ }} }} ⊢
  WP (Par (Ret a1) m2 k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_simp with "[H]").
  { eapply SimpParRetLeft. }
  by iApply wp_try.
Qed.

Lemma wp_par_ret_right {A1 A2 A} s E m1 a2 (k : A1 * A2 → free A) ko φ :
  WP m1 @ s; E {{ λ v1, WP (k (v1, a2)) @ s; E {{ φ }} }} ⊢
  WP (Par m1 (Ret a2) k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_simp with "[H]").
  { eapply SimpParRetRight. }
  by iApply wp_try.
Qed.

Lemma wp_par_ret_ret {A1 A2 A3} s E a1 a2 (k: A1 * A2 → free A3) ko φ:
  WP (k (a1, a2)) @ s; E {{ φ }} ⊢
  WP (Par (ret a1) (ret a2) k ko) @s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_simp with "[H]").
  { eapply SimpParRetRight. }
  rewrite try_ret.
  iAssumption.
Qed.

End rules.

(* --------------------------------------------------------------------------*)
(* The following part defines module specifications. *)

From iris.base_logic Require Import iprop.

Definition spec_env {Σ} : Type :=
  list (var * (val → iProp Σ)).

Definition module_spec_list {Σ} (Λ : spec_env) (η: env) : iProp Σ :=
  [∗ list] '(x, φx) ∈ Λ,
    ∃ v, ⌜lookup_name η x = Ret v⌝ ∗ φx v.

Definition module_spec {Σ} (Λ : spec_env) (v: val) : iProp Σ :=
  ∃ η, ⌜ v = VStruct η ⌝ ∗ module_spec_list Λ η.
