From iris.prelude Require Import options.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import base proofmode classes.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.

(* This file defines the predicate [WP]. *)

(* It is heavily inspired from [iris/{bi,program_logic}/weakestpre.v]. *)

(* -------------------------------------------------------------------------- *)

(* For details about these incantations, see
   [iris.base_logic.lib.fancy_updates] and
   [iris.base_logic.lib.gen_heap].
   [hlc] stands for "has later credits". *)

Class osirisGS_gen (hlc: has_lc) (Σ: gFunctor) := OsirisG {

  (* This gives us fancy updates. *)
  osiris_invGS :> invGS_gen hlc Σ;

  (* This gives us a heap, which maps locations to values. *)
  osiris_heapGS :> gen_heapGS loc val Σ;

}.

(* -------------------------------------------------------------------------- *)

(* This is the definition of the predicate [WP]. *)

Section definition.

Context (A: Type).
Context `{!osirisGS_gen hlc Σ}.

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
Global Arguments wp' {hlc Σ _ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal: wp = wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

End definition.

(* -------------------------------------------------------------------------- *)

(* More boilerplate, once again inspired by
   [iris/{bi,program_logic}/weakestpre.v] *)

Section boilerplate.

Context {A : Type}.
Context `{!osirisGS_gen hlc Σ}.
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

(* The following are the reasoning rules of our program logic. *)

(* These rules are applied by the tactics in [wp_tactics.v]. *)

Section wp_lemmas.

Context `{!osirisGS_gen hlc Σ}.

Lemma wp_covariant {A} s E m (φ: A -> iProp Σ) (φ': A -> iProp Σ) :
  WP m @ s; E {{ φ }} -∗
  (∀ v, (φ v) -∗ (φ' v)) -∗
  WP m @ s; E {{ φ' }}.
Proof.
  iLöb as "IH" forall (φ φ' m).
  iIntros "Hwp Himpl".
  wp_unfold_all.
  destruct (is_ret m).

  (* Case: [m] is [ret _]. *)
  { iIntros (?) "H".
    iDestruct ("Hwp" with "H") as "[$ H]".
    iApply ("Himpl" with "H"). }

  (* Case: [m] is not [ret _]. *)
  { iIntros (σ) "Hsi".
    iPoseProof ("Hwp" $! σ with "Hsi") as "[$ Hwp]";
    iIntros (σ' m' Hstep).
    iPoseProof ("Hwp" with "[//]") as ">[$ Hwp]".
    iModIntro. iNext.
    iApply ("IH" with "Hwp Himpl"). }

Qed.

Lemma strong_mono {A} P m s E (φ: A → iProp Σ):
  (P ∗ WP m @ s; E {{ φ }}) -∗ WP m @ s; E {{ λ v, P ∗ φ v }}.
Proof.
  iIntros "[HP Hwp]".
  iApply (wp_covariant with "Hwp [HP]").
  iFrame "HP".
  eauto.
Qed.

Lemma wp_ret {A} s E (v: A) φ:
  φ v -∗ WP (Ret v) @ s; E {{ φ }}.
Proof.
  wp_unfold_all. iIntros. iFrame.
Qed.

Lemma ret_wp {A} s E (v: A) σ φ:
  state_interp σ -∗
  WP (Ret v) @ s; E {{ φ }} ==∗
  state_interp σ ∗ φ v.
Proof.
  wp_unfold_all.
  iIntros "Hsi Hwp".
  iSpecialize ("Hwp" with "Hsi").
  iAssumption.
Qed.


Lemma wp_crash {A s E σ φ} :
  state_interp σ -∗
  WP (@crash A) @ s; E {{φ}} -∗
  False.
Proof.
  wp_unfold_all.
  iIntros "Hsi Hwp".
  iDestruct ("Hwp" with "Hsi") as "[% _]".
  eauto with invert_can_step.
Qed.

Lemma wp_next {A s E σ φ} :
  state_interp σ -∗
  WP (@Next A) @ s; E {{ φ }} -∗
  False.
Proof.
  wp_unfold_all.
  iIntros "Hsi Hwp".
  iDestruct ("Hwp" with "Hsi") as "[% _]".
  eauto with invert_can_step.
Qed.

Lemma wp_grab_state_invariant {A} (m : free A) s E φ :
  (∀ σ, state_interp σ -∗ state_interp σ ∗ WP m @ s; E {{ φ }}) -∗
  WP m @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold m.
  iIntros (σ) "Hsi".
  iDestruct ("H" with "Hsi") as "[Hsi H]".
  iSpecialize ("H" with "Hsi").
  eauto.
Qed.

(* The Bind rule of Separation Logic. *)
Lemma wp_bind {A1 A2} s E (m1: free A1) (m2: A1 → free A2) φ :
  WP m1 @ s; E {{ λ v, WP (m2 v) @ s; E {{ φ }} }} -∗
  WP (bind m1 m2) @ s; E {{ φ }}.
Proof.
  iLöb as "IH" forall (m1 m2 φ).
  iIntros "Hm1".
  wp_unfold m1.
  destruct (is_ret m1) as [a1|] eqn:Hret.

  (* Case: [m1] is [ret a1]. *)
  (* The result is immediate. *)
  { rewrite (invert_is_ret_Some Hret). simpl.
    by iApply wp_grab_state_invariant. }

  (* Case: [m1] is not [ret _]. *)
  {
    (* Therefore, [bind m1 m2] is not [ret _] either. *)
    eapply (is_ret_bind_None _ m2) in Hret.
    (* Unfold and simplify the goal. *)
    wp_unfold_all.
    iIntros (σ) "Hsi".
    rewrite Hret; clear Hret.
    (* Simplify and destruct the hypothesis. *)
    iDestruct ("Hm1" with "Hsi") as "[%Hcanstep Hm1]".
    assert (Hnotanswer: ¬ is_answer m1) by eauto using can_step_not_answer.

    iSplit.
    (* Subgoal: [bind m1 m2] can step. *)
    { eauto using can_step_bind. }
    (* Subgoal: every reduct of [bind m1 m2] is safe. *)
    { clear Hcanstep.
      iIntros (σ' m') "%Hstep".
      (* Because [m1] is not an answer, a reduct of [bind m1 m2] must be
         of the form [bind m'1 m2], where [m'1] is a reduct of [m1]. *)
    destruct (invert_step_bind' Hstep Hnotanswer) as (m'1 & Hstep' & ?).
    subst. clear Hstep. rename Hstep' into Hstep.
    (* The hypothesis can then be further exploited. *)
    iPoseProof ("Hm1" with "[//]") as ">[$Hm1]".
    iModIntro. iNext.
    iApply "IH". iClear "IH".
    iApply "Hm1". }
  }

Qed.

(* This tactic is used when the goal is the [None] branch in the definition
 of [wp], that is, when the computation at hand is not [ret _]. *)
Local Ltac construct_wp :=
iSplitR; [
  (* Prove [can_step]: *)
  iPureIntro; eauto with step
| (* Introduce a hypothetical step: *)
  iIntros (σ' m') "%Hstep"
].

(* [Par]-related lemmas. *)
(* To prove [WP (Par m1 m2 k ko) φ], one should provide two post conditions φ1
 * and φ2 and show that:
 * - m1 satisfies the post-condition φ1
 * - m2 satisfies the post-condition φ1
 * - for any values v1 and v2 satisfying φ1 and φ2 respectively,
 *     the pair (v1, v2) satisfies φ.
*)
Lemma wp_par {A1 A2 A3 s E m1 m2} {k: A1 * A2 → free A3} {ko φ} φ1 φ2:
  WP m1 @ s ; E {{ φ1 }} -∗
  WP m2 @ s ; E {{ φ2 }} -∗
  ▷ (
    ∀ a1 a2,
    φ1 a1 -∗ φ2 a2 -∗
    WP (k (a1, a2)) @ s; E {{ φ }}
  )
  -∗ WP (Par m1 m2 k ko) @ s ; E {{ φ }}.
Proof.
  iLöb as "IH" forall (m1 m2).
  iIntros "H1 H2 Hjoin".
  wp_unfold (Par m1 m2 k ko).
  iIntros (σ) "Hsi".
  construct_wp.
  destruct_step.

  { (* Case: [StepParRetRet] *)
    iDestruct (ret_wp with "Hsi H1") as ">[Hsi H1]".
    iDestruct (ret_wp with "Hsi H2") as ">[Hsi H2]".
    iModIntro. iNext. iFrame "Hsi".
    iApply ("Hjoin" with "H1 H2"). }
  { (* Case: [StepParCrashLeft] *)
    iModIntro. iNext.
    iPoseProof (wp_crash with "Hsi H1") as "%".
    tauto. }
  { (* Case: [StepCrashRight] *)
    iModIntro. iNext.
    iPoseProof (wp_crash with "Hsi H2") as "%".
    tauto. }
  { (* Case: [StepNextLeft] *)
    iModIntro. iNext.
    iPoseProof (wp_next with "Hsi H1") as "%".
    tauto. }
  { (* Case: [StepNextRight] *)
    iModIntro. iNext.
    iPoseProof (wp_next with "Hsi H2") as "%".
    tauto. }
  { (* Case: [StepParLeft] *)
    wp_unfold m1.
    assert (is_ret m1 = None) as ->.
    { eauto using can_step_is_not_ret with step. }
    iDestruct ("H1" with "Hsi") as "[%Hcanstep1 H1]".
    iPoseProof ("H1" with "[//]") as ">[$H1]".
    iModIntro. iNext.
    iApply ("IH" with "H1 H2 Hjoin"). }
  { (* Case: [StepParRight] *)
    wp_unfold m2.
    assert (is_ret m2 = None) as ->.
    { eauto using can_step_is_not_ret with step. }
    iDestruct ("H2" with "Hsi") as "[%Hcanstep2 H2]".
    iPoseProof ("H2" with "[//]") as ">[$H2]".
    iModIntro. iNext.
    iApply ("IH" with "H1 H2 Hjoin"). }
Qed.

Lemma wp_par_ret_right {A1 A2 A} s E m1 a2 (k : A1 * A2 → free A) ko φ :
  WP m1 @ s; E {{ λ v1, WP (k (v1, a2)) @ s; E {{ φ }} }} -∗
  WP (Par m1 (Ret a2) k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_par
      (λ a1, WP (k (a1, a2)) @ s; E {{ φ }})
      (λ a', ⌜a' = a2⌝)
    with "H []")%I.
  { by iApply wp_ret. }
  { iNext. by iIntros (??) "? ->". }
Qed.

Lemma wp_par_ret_left {A1 A2 A} s E a1 m2 (k : A1 * A2 → free A) ko φ :
  WP m2 @ s; E {{ λ v2, WP (k (a1, v2)) @ s; E {{ φ }} }} -∗
  WP (Par (Ret a1) m2 k ko) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_par
      (λ a', ⌜a' = a1⌝)
      (λ a2, WP (k (a1, a2)) @ s; E {{ φ }})
    with "[] H")%I.
  { by iApply wp_ret. }
  { iNext. by iIntros (??) "-> ?". }
Qed.

Lemma wp_par_ret_ret {A1 A2 A3} s E a1 a2 (k: A1 * A2 → free A3) ko φ:
  ▷ WP (k (a1, a2)) @ s; E {{ φ }} -∗
  WP (Par (ret a1) (ret a2) k ko) @s; E {{ φ }}.
Proof.
  iIntros "H".
  iApply (wp_par
      (λ a', ⌜a' = a1⌝)
      (λ a', ⌜a' = a2⌝)
    with "[] []")%I.
  { by iApply wp_ret. }
  { by iApply wp_ret. }
  { iNext. by iIntros (??) "-> ->". }
Qed.

(* [Stop]-related lemmas. *)

Lemma wp_eval {A} s E η e (k : val → free A) φ :
  ▷ WP (eval η e) @ s; E {{ λ v, WP (k v) @ s; E {{ φ }} }} -∗
  WP (Stop CEval (η, e) k) @ s; E {{ φ }}.
Proof.
  iIntros "Hwp".
  wp_unfold_head.
  iIntros (σ) "Hsi".
  construct_wp.
  destruct_step.
  iModIntro. iNext. iFrame "Hsi".
  by iApply wp_bind.
Qed.

Lemma wp_eval_ret s E η e φ :
  ▷ WP (eval η e) @ s; E {{ φ }} -∗
  WP (Stop CEval (η, e) ret) @ s; E {{ φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_eval.
  iNext.
  iApply (wp_covariant with "Hwp").
  iIntros. by iApply wp_ret.
Qed.

Lemma wp_flip {A} s E x (k: bool -> free A) φ :
  ▷ (∀ b, WP (k b) @ s; E {{ φ }}) -∗
  WP (Stop CFlip x k) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_head.
  iIntros (σ) "Hsi".
  construct_wp.
  destruct_step.
  iModIntro. iNext.
  iSpecialize ("H" $! b).
  iFrame.
Qed.

Lemma wp_ref {A} s E x (k: loc -> free A) φ :
  ▷ (∀ ℓ,
       mapsto ℓ (DfracOwn 1) x ∗ meta_token ℓ ⊤ -∗
       WP (k ℓ) @ s; E {{ φ }} ) -∗
  WP (Stop CAlloc x k) @ s; E {{ φ }}.
Proof.
  iIntros "H".
  wp_unfold_head.
  iIntros (σ) "Hsi".
  construct_wp.
  destruct_step.
  iSpecialize ("H" $! l).
  iPoseProof (gen_heap_alloc with "Hsi") as ">[$ HH]".
  { assumption. }
  iModIntro. iNext.
  iApply ("H" with "HH").
Qed.

Lemma wp_store {A} s E ℓ v v' k (φ: A → iProp Σ) :
  mapsto ℓ (DfracOwn 1) v -∗
  ▷ (mapsto ℓ (DfracOwn 1) v' -∗ WP (k tt) @ s; E {{ φ }}) -∗
  WP (Stop CStore (ℓ, v') k) @ s; E {{ φ }}.
Proof.
  iIntros "Hℓ Hwp".
  wp_unfold_head.
  iIntros (σ) "Hsi".
  construct_wp.
  iPoseProof (gen_heap_valid with "Hsi Hℓ")  as "%Hin".
  iMod ((gen_heap_update _ _ _ v') with "Hsi Hℓ") as "[Hsi Hℓ]".
  eapply invert_step_store in Hstep; [| eauto ].
  destruct Hstep. subst.
  iModIntro. iNext. iFrame "Hsi".
  iApply ("Hwp" with "Hℓ").
Qed.

Lemma wp_load {A} s E ℓ v dq (k: val -> free A) φ :
  mapsto ℓ dq v -∗
  ▷ (mapsto ℓ dq v -∗ WP (k v) @ s; E {{ φ }}) -∗
  WP (Stop CLoad ℓ k) @ s; E {{ φ }}.
Proof.
  iIntros "Hℓ Hwp".
  wp_unfold_head.
  iIntros (σ) "Hsi".
  construct_wp.
  iPoseProof (gen_heap_valid with "Hsi Hℓ")  as "%Hin".
  eapply invert_step_load in Hstep; [| eauto ].
  destruct Hstep. subst.
  iModIntro. iNext. iFrame "Hsi".
  iApply ("Hwp" with "Hℓ").
Qed.

End wp_lemmas.
