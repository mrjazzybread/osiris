From Coq.Logic Require Import FunctionalExtensionality.
From iris.prelude Require Import options.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import base proofmode classes.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import safe wp helpers.


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

Section Rules.

  Context `{!osirisGS Σ}.

  (* The return rule. *)

  Lemma wp_ret {A} s E (a : A) φ :
    φ a ⊢
    WP (Ret a) @ s; E {{ φ }}.
  Proof.
    wp_unfold_all. iIntros. iFrame.
    iMod (@fupd_mask_subseteq _ _ E ∅); [set_solver | eauto].
  Qed.

  (* The inverse return rule. *)

  Lemma invert_wp_ret {A} s E (a : A) φ :
    ∀ σ, state_interp σ -∗
         WP (Ret a) @ s; E {{ φ }} -∗
         |={E}=> state_interp σ ∗ φ a.
  Proof.
    intro_state. iIntros "Hwp".
    wp_unfold_all. spec_state "Hwp".
    iApply (fupd_trans with "Hwp").
  Qed.

  (* The inverse crash rule. *)

  Lemma invert_wp_crash {A s E φ} :
    ∀ σ, state_interp σ -∗
         WP (@crash A) @ s; E {{φ}} -∗
         |={E}=> False.
  Proof.
    intro_state. iIntros "Hwp".
    wp_unfold_all. spec_state "Hwp".
    destruct_wp_nonret. exfalso; eauto with invert_can_step.
  Qed.

  (* The inverse [next] rule. *)

  Lemma invert_wp_next {A s E φ} :
    ∀ σ, state_interp σ -∗
         WP (@Next A) @ s; E {{ φ }} -∗
         |={E}=> False.
  Proof.
    intro_state. iIntros "Hwp".
    wp_unfold_all. spec_state "Hwp".
    destruct_wp_nonret. exfalso; eauto with invert_can_step.
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
      iModIntro; construct_wp_nonret.
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

  (* ------------------------------------------------------------------------ *)

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
     We do not want the user to rely on the fact that a join point counts as a
     step. *)

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
    (* We proceed by Löb-Induction after generalizing [m1] and [m2]. *)
    iLöb as "IH" forall (m1 m2); iIntros "H1 H2 Hjoin".

    (* As for the other rules, proof starts by stepping in the WP:
       (1) unfold the wp, (2) introduce a valid state, (3) introduce the head
       modality and (4) enter in the second branch of the WP. *)
    wp_unfold_head; intro_state;
      iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod";
      [ set_solver | iModIntro; construct_wp_nonret ].

    (* Make a case study over the possible step. In each case, use FupTrans to
       add the modality [ |={E,∅}=> ] in front of the goal. *)
    destruct_step; iMod "Hmod" as "_".

    (* We now examine each of the ways in which [Par m1 m2 k ko] can step. *)

    { (* Case: [StepParRetRet].
         Both [m1] and [m2] represent values [v1] and [v2]. One can consume [H1]
         and [H2] to learn that the values respect their postconditions.
         The inversion does not consume the state-interpretation, which can be
         framed behind the modalities. *)
      iMod (invert_wp_ret with "[$][$]") as "[Hsi H2]".
      iMod (invert_wp_ret with "[$][$]") as "[$ H1]".

      (* Introduce the modality [ |={E,∅}=> ]. *)
      iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod";
        [ set_solver | iModIntro ].
      (* The later is not exposed in this rule. Hence, it can simply be
         introduced together with the remaining modalities. *)
      do 2 iModIntro; iMod "Hmod" as "_"; iModIntro.

      (* Finally, use the hypothesis on [k] to finish the proof. *)
      iApply ("Hjoin" with "H1 H2"). }

    (* In the four following cases, one of the branches of the [Par] is either a
       [Crash] or a [Next]. Hence, one can consume the corresponding [WP]
       hypothesis to get [ |={E}=> False ]. As the goal is of the form
       [ |={E,∅}=> G ], by FupTrans, it suffices to show [|={E}=> |={E,∅}=> G].
       Then, by monotony of [ |={E}=> ], one can eliminate [False] and finish
       the proof. *)
    1,2 : by iMod (invert_wp_crash with "Hsi [$]") as "%".
    1,2 : by iMod (invert_wp_next with "Hsi [$]") as "%".

    { (* Case: [StepParLeft] *)
      (* [m1] steps to [m'1]. Steps preserve the conjunction of the [WP] and the
         state interpretation. Some modalities need to be stripped from the
         result. *)
      iMod (wp_step Hstep with "Hsi H1") as ">H1".
      do 2 iModIntro. iMod "H1"; iModIntro;
      iMod "H1" as "[$?]"; iModIntro. (* After stripping modalities, one can
                                         frame the state interpretation. *)

      (* The induction hypothesis ends the proof. *)
      iApply ("IH" with "[$]H2 Hjoin"). }

    { (* Case: [StepParRight]
         This case is similar to the previous one. *)
      iMod (wp_step Hstep with "Hsi H2") as ">H2".
      do 2 iModIntro. iMod "H2"; iModIntro. iMod "H2" as "[$?]"; iModIntro.
      iApply ("IH" with "H1 [$] Hjoin"). }
  Qed.

  (* ------------------------------------------------------------------------ *)

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
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro.
    construct_wp_nonret.
    destruct_step.
    iModIntro; iNext; iModIntro; iMod "Hmod" as "_"; iModIntro.
    iFrame.
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
    iMod (@fupd_mask_subseteq  _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro.
    construct_wp_nonret.
    destruct_step.
    iModIntro; iNext; iMod "Hmod" as "_".
    iFrame.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hmod"; iMod "Hmod" as "_"; iModIntro.
    by iApply "H".
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* [CLoop] *)

  (* The following lemmas help reason on loops. *)

  (* The following lemma is inspired by the corresponding CFML rule. *)
  Lemma wp_loop {A} s E
        (η : env) (x : var) (i1 i2 : int) (e : expr)
        (k : val → free A) (ko : unit → free A) (φ : A → iProp Σ) :
    (* If *)
    (▷ (* Either: *)
       if int.lt i2 i1
       then
         (* - i2 < i1,
              and the rest of the program satisfies the postcondition. *)
         wp s E (k #()) φ
       else
         (* - i1 <= i2,
              and the evaluation of the body succeeds and the remaining
              iterations satisfy the postcondition. *)
         wp s E (eval (EnvCons x (VInt i1) η) e)
               (λ _,
                  wp s E (
                       Stop CLoop
                            (η, x, int.add i1 int.one, i2, e)
                            k ko) φ)) ⊢
    (* Then the loop (with the rest of the program as continuation) satisfies
       the postcondition. *)
    wp s E (Stop CLoop (η, x, i1, i2, e) k ko) φ.
  Proof.
    iIntros "H".

    (* We proceed by case analysis on the comparison of [i1] and [i2]. *)
    destruct (lt i2 i1) eqn:Hlt; (* In each case: *)
      (* we enter into the WP of the goal, eliminate modalities, use the fact
         that the [Stop CLoop _ _ _] can step (in a unique way) and frame the
         state interp. *)
      wp_unfold (Stop CLoop (η, x, i1, i2, e) k ko);
      intro_state; (iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod";
                    [ set_solver | iModIntro ]);
      construct_wp_nonret; destruct_step;
      do 3 iModIntro; iMod "Hmod" as "_"; iModIntro; iFrame;

      (* Finally, expand the definition of the helper function [loop]. *)
      rewrite/loop Hlt.

    { (* In the base case, the loop is over. One can use the hypothesis to end
         the proof. *)
      iApply wp_try; iApply wp_ret; iApply "H". }

    { (* Otherwise,  [loop] reduces to a [try (bind _ _) _ _].
         In order to be able to use the hypothesis, it is important to replace
         the [Stop _ _ ret next] by [Stop _ _ k ko] by pushing the try in the
         bind, and the stop. *)
      rewrite try_bind. (* <- push the [try] in the [bind]. *)

      (* use the hypothesis about the behavior of the body of the loop. *)
      iApply (wp_try_binary with "H").
      iIntros(_) "H".

      rewrite try_stop. (* <- push the [try] in the [Stop]. *)
      change (λ y : val, try (ret y) k ko) with k.
      change (λ _ : (), try Next k ko) with (λ _ : (), ko ()).
      assert ((λ _ : (), ko ()) = ko) as ->; last iExact "H".
      (* Is it possible to get a proof without functional extentionality?  *)
      extensionality v; destruct v; reflexivity. }
  Qed.

  (* [wp_loop_inv_pos_aux] is a helper lemma to prove that:
     for any predicate [P : nat → iProp Σ],
     If - [P n1],
        - [P] is preserved by the body [e] of the loop
          (ie. [P i -∗ WP (eval (η with i) e) {{ P (S i) }}]),
        - [P (S nn) -∗ rest of the program satisfies φ]
     Then, [for i = n1 to nn do e done; rest of the program] satisfies [φ].

     Additionally, the lemma requires that [n1] and [S nn] are representable.
     Note that [P] is quantified after every other variables, so the invariant
     might depend on [η], [n1], ...

     This helper lemma takes an argument [n = S (i2 - i1)] explicitly to ease
     the induction. Another lemma [wp_loop_inv_pos] is defined below. It is
     essentially the same lemma, except that [n] is no longer present in the
     statement. *)
  Local Lemma wp_loop_inv_pos_aux {A} s E
        (η : env) (x : var) (n i1 i2 : nat) (e : expr)
        (k : val → free A) (ko : unit → free A) (φ : A → iProp Σ)
        (Hinv : nat → iProp Σ) :
    representable i1 →
    representable (S i2) →
    le i1 i2 →
    n = S (i2 - i1)%nat →
    (Hinv i1) ⊢
    (□ ∀ (i: nat), ⌜le i1 i⌝ →
                   ⌜le i i2⌝ →
                   Hinv i -∗ wp s E
                                (eval (EnvCons x (VInt $ repr i) η) e)
                                (λ _, Hinv (S i))) -∗
    (Hinv (S i2) -∗ wp s E (k #()) φ) -∗
    wp s E (Stop CLoop (η, x, repr i1, repr i2, e) k ko) φ.
  Proof.
    generalize dependent i1 ; generalize dependent i2.
    induction n;
      iIntros(i2 i1 Hrepr1 Hrepr2 Hle Hn) "Hinit #Hpreservation Hccl";

      (* Three cases: either the loop is over, or the loop is entered one last
         time, or it is entered. *)
      last (destruct (decide (i1 = i2)) as [ -> | Hneq ]; last first);

      (* First, we take a step in the WP and frame the state interp. *)
      wp_unfold_head; intro_state;
      (iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod";
       [set_solver | iModIntro ]);
      construct_wp_nonret;
      do 3 iModIntro; iMod "Hmod" as "_"; iModIntro;
      destruct_step; iFrame.

    { (* The loop is over. *)
      assert (i1 = S i2) as -> by lia.
      iApply wp_try.
      rewrite/loop lt_repr_repr; try representable.
      replace (i2 <? S i2) with true by lia.
      iApply wp_ret.
      iApply ("Hccl" with "Hinit"). }


    { (* The body of the loop will be executed (not for the last time). *)
      assert (Hlt: lt (repr i2) (repr i1) = false).
      { rewrite lt_repr_repr; try assumption.
        - lia.
        - unfold representable in *; lia. }

      (* The loop is really a try... *)
      rewrite/loop Hlt.
      rewrite try_bind.

      (* ...which leads to a bind.
         The first element of the bind is the evaluation of the body of the
         loop. The assumption ["Hpreservation"] prove that this evaluation
         preserves the loop invariant predicate. It takes the invariant at i1
         and gives back the invariant at [S i1]. *)
      iApply (wp_try_binary with "[Hinit Hpreservation]");
        first iApply ("Hpreservation" $! i1 with "[//][//]Hinit").
      iIntros(_)"Hinit".

      (* The goal is the proof of a WP for [for x = S i1 to i2 do e done]. The
         induction hypothesis can take care of it.
         Note: it is to use ["Hpreservation"] a second time that it needs to be
               persistent.  *)
      iPoseProof (IHn i2 (S i1)) as "IH".
      { unfold representable in *. lia. }
      { assumption. }
      { lia. }
      { lia. }
      { iSpecialize ("IH" with "Hinit[]Hccl").
        { iIntros "!>" (i Hi Hi').
          iApply ("Hpreservation"); iPureIntro; lia. }

        replace (add (repr i1) int.one) with (repr (S i1)); last first.
        { rewrite add_repr_repr. f_equal. lia. }

        rewrite try_stop.
        change (λ y : val, try (ret y) k ko) with k.
        change (λ _ : (), try Next k ko) with (λ _ : (), ko ()).
        assert ((λ _ : (), ko ()) = ko) as ->; last iExact "IH".
        extensionality v; destruct v; reflexivity. } }

    { (* Last run of the loop. *)
      iApply wp_try.
      rewrite/loop lt_repr_repr; try assumption.
      rewrite Z.ltb_irrefl.
      iApply (wp_bind_binary with "[Hinit Hpreservation]");
        first iApply ("Hpreservation" with "[//][//]Hinit").
      iIntros(_)"Hinit".
      iSpecialize ("Hccl" with "Hinit").
      clear σ'.

      assert (Hlt: lt (repr i2) (add (repr i2) int.one) = true).
      { rewrite add_repr_repr lt_repr_repr; unfold representable in *; lia. }

      wp_unfold (Stop CLoop (η, x, add (repr i2) int.one, repr i2, e) ret next).
      intro_state.
      iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; [ set_solver | iModIntro ].
      construct_wp_nonret; destruct_step.
      do 3 iModIntro. iMod "Hmod" as "_"; iModIntro.
      iFrame.
      iApply wp_try.
      rewrite/loop Hlt.
      do 2 iApply wp_ret.
      iExact "Hccl". }
  Qed.
  Definition wp_loop_inv_pos {A} s E
        (η : env) (x : var) (i1 i2 : nat) (e : expr)
        (k : val → free A) (ko : unit → free A) (φ : A → iProp Σ)
        (Hinv : nat → iProp Σ) :
    representable i1 →
    representable (S i2) →
    le i1 i2 →
    (Hinv i1) ⊢
    (□ ∀ (i: nat), ⌜le i1 i⌝ →
                 ⌜le i i2⌝ →
                 Hinv i -∗ wp s E
                              (eval (EnvCons x (VInt $ repr i) η) e)
                              (λ _, Hinv (S i))) -∗
    (Hinv (S i2) -∗ wp s E (k #()) φ) -∗
    wp s E (Stop CLoop (η, x, repr i1, repr i2, e) k ko) φ :=
    let n := S (i2 - i1)%nat in
    fun repr1 repr2 Hle =>
      wp_loop_inv_pos_aux s E η x n i1 i2 e k ko φ Hinv
                          repr1 repr2 Hle eq_refl.

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
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro.
    construct_wp_nonret.
    destruct_step.
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi HH]".
    { eassumption. }
    iModIntro; iNext; iMod "Hmod" as "_".
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro; iMod "Hmod" as "_"; iModIntro.
    iFrame.
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
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro.
    construct_wp_nonret.
    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_store in Hstep; [ destruct Hstep | eauto ]. subst.
    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iModIntro; iNext; iMod "Hmod" as "_".
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro; iMod "Hmod" as "_"; iModIntro.
    iFrame.
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
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro.
    construct_wp_nonret.
    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    eapply invert_step_load in Hstep; [ destruct Hstep | eauto ]. subst.
    iModIntro; iNext; iMod "Hmod" as "_".
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro; iMod "Hmod" as "_"; iModIntro.
    iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* ------------------------------------------------------------------------ *)

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
      iApply fupd_frame_l; iSplit; first by eauto using invert_simplify_ret.
      iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
      iModIntro.
      iIntros (σ' m' Hstep).
      iMod "Hmod" as "_".

      (* Examine one step of [m] to [m']. The simulation diagram in this case
       tells us that this reduction step takes us closer to [ret a].
       That is, we get [simplify n' m' (ret a)] where [n' < n] holds. *)
      pose proof (simplify_ret_step_diagram Hsimp Hstep)
        as (n' & ? & ? & ?); subst.
      (* We are then able to use the inner induction hypothesis. *)
      iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
      iModIntro.
      do 2 iModIntro.
      iMod "Hmod"; iModIntro.
      iFrame.
      iApply ("IHn" with "[//] Hwp [//]"). }
    (* Thus, in the following, we assume [ms] is not [ret _]. *)

    (* Then, [WP ms ...] implies than [ms] can step.
     This implies that [m], too, can step. *)
    iAssert (|={E}=> ⌜ can_step (σ, m) ⌝
                     ∗ wp s E ms φ
                     ∗ state_interp σ)%I
      with "[Hwp Hsi]"
      as ">(%&Hwp&Hsi)".
    { iApply ((fupd_plain_keep_l E ⌜can_step (σ, m)⌝
                                 (wp s E ms φ ∗ state_interp σ))%I
               with "[$Hwp $Hsi]").
      iIntros "[??]";
        iMod (wp_can_step' with "[$][$]") as "%Hdisj".
      iModIntro; iPureIntro; destruct Hdisj.
      { eauto using invert_simplify_can_step. }
      { exfalso; eauto. } }
    iApply fupd_frame_l; iSplit; first done.
    iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
    iModIntro. iIntros (σ' m' Hstep).
    iMod "Hmod" as "_".

    (* We now examine an arbitrary step of [m] to [m']. *)
    (* Exploit the main simulation diagram. *)
    pose proof (simplify_step_diagram Hsimp Hstep)
      as (ms' & n' & i & Hstep' & Hsimp' & Hcases);
      clear Hsimp Hstep.
    destruct_simplify_step_diagram.

    (* Case: the reduction step disappears through the diagram. *)
    { iMod (@fupd_mask_subseteq _ _ E ∅) as "Hmod"; first set_solver.
      do 3 iModIntro.
      iMod "Hmod"; iModIntro.
      iFrame. iApply ("IHn" with "[//] Hwp [//]"). }

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

  (* -------------------------------------------------------------------------*)

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

End Rules.
