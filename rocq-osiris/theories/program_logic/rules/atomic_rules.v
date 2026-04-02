From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.

From osiris.lang Require Import lang.
From osiris.tactics Require Import osiris_utils.
From osiris.program_logic Require Import thread_step ewp tactics.
From osiris.program_logic.rules Require Import impure_rules stop_rules.

Import ewp_rules_tactics.

(** This file provides atomicity instances for memory operations and derived [imp] rules for atomic access. *)

Instance crash_atomic {V X} :
  thread_step.Atomic (@Crash V X).
Proof. constructor. inversion H; subst. inversion H1. Qed.

Global Instance load_atomic l :
  thread_step.Atomic (load l).
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_load_2.
  destruct (σ' !! l) as [ [| |] | ]; by econstructor.
Qed.

Global Instance eload_atomic η p :
  thread_step.Atomic (eval η (ELoad (EPath p))).
Proof.
  simpl_eval.
  destruct (lookup_path η p); last apply _.
  destruct v; simpl; try (rewrite bind_crash; apply _).
  apply _.
Qed.

Global Instance exchange_atomic l v' :
  thread_step.Atomic (exchange l v').
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_exchange_2.
  destruct (σ !! l0) as [ [| |] | ]; by econstructor.
Qed.

Global Instance store_atomic l v :
  thread_step.Atomic (code.store l v).
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_exchange_2.
  destruct (σ !! l0) as [ [| |] | ]; by econstructor.
Qed.

Global Instance cas_atomic l seen v' :
  thread_step.Atomic (cas l seen v').
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_cas_2.
  destruct (σ !! l0) as [ [| |] | ]; try by econstructor.
  destruct (phys_eq_val _ _) as [ [|] | ]; by econstructor.
Qed.

Global Instance faa_atomic l i :
  thread_step.Atomic (faa l i).
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_faa_2.
  destruct (σ !! l0) as [ [| |] | ]; try by econstructor.
  rewrite /continue /=.
  destruct v; try by constructor.
  by econstructor.
Qed.

Section imp_atomic_rules.

  Context `{!osirisGS Σ}.
  Context {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Lemma imp_store_atomic `{Encode A} (E2 E1 : coPset) η e1 e2 (Φ1 : loc → _) (Φ2 : A → _) (Φ : () → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (|={E1,E2}=>
         ∀ l x, Φ1 l -∗ Φ2 x -∗
                ∃ v, ▷ l ↦ v ∗
                     ▷ (l ↦ #x -∗ |={E2,E1}=> Φ ())) -∗
    impure E1 (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 Hstore".
    simpl_eval.
    iApply (imp_bind (A1:=loc * A) with "[-]").
    set_postcondition
      (λ '((l, x) : loc * A),
         |={E1,E2}=> ∃ v, ▷ l ↦ v ∗
                          ▷ (l ↦ #x -∗ |={E2,E1}=> Φ ()))%I.
    { iApply (imp_Par with "[He1] He2").
      { iApply (imp_as_loc with "He1"). }
      iSplit.
      - iIntros (e) "He !>". iApply (imp_throw with "He").
      - iIntros (l x) "HΦ1 HΦ2 !>".
        iApply imp_ret. instantiate (1:=(_,_)). encode.
        iMod "Hstore". iModIntro.
        iDestruct ("Hstore" with "HΦ1 HΦ2") as "(%v & $ & $)". }
    iIntros ((l & x)) "Hl /=".
    iApply (imp_atomic' E1 E2).
    iMod "Hl" as "(%v & Hl & Hstore)".
    iApply (imp_store' with "Hl").
    iApply "Hstore".
  Qed.

  Lemma imp_cas_atomic `{PhysEqDec A} (E2 E1 : coPset) η e1 e2 e3 (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    impure E1 (eval η e3) Ψ ζ Φ3 -∗
    ▷ (|={E1,E2}=>
         ∀ l seen v',
         Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
         ∃ v, ▷ l ↦ #v ∗
              ▷ (l ↦ (if phys_eq_val_ v seen then #v' else #v) -∗
                 |={E2,E1}=> Φ (phys_eq_val_ v seen))) -∗
    impure E1 (eval η (ECAS e1 e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 He3 Hcas".
    simpl_eval.
    iApply (imp_bind (A1:=loc * A * A) with "[-]").
    set_postcondition
      (λ '((l, seen, v') : loc * A * A),
         |={E1,E2}=> ∃ v, ▷ l ↦ #v ∗
                          ▷ (l ↦ (if phys_eq_val_ v seen then #v' else #v) -∗
                             |={E2,E1}=> Φ (phys_eq_val_ v seen)))%I.
    { iApply (imp_Par (A1:=loc * A) with "[He1 He2] He3").
      { iApply (imp_Par with "[He1] He2").
        { iApply (imp_as_loc with "He1"). }
        iSplit.
        - iIntros (e) "He !>". iApply (imp_throw with "He").
        - iIntros (l x) "HΦ1 HΦ2 !>".
          set_postcondition (λ '(l, x), Φ1 l ∗ Φ2 x)%I.
          iApply imp_ret. instantiate (1:=(_,_)). encode.
          iFrame. }
      iSplit.
      - iIntros (e) "He !>". iApply (imp_throw with "He").
      - iIntros ((l & seen) x) "(HΦ1 & HΦ2) HΦ3".
        iApply imp_ret. instantiate (1:=((_,_),_)). encode.
        iNext. iMod "Hcas". iModIntro.
        iDestruct ("Hcas" with "HΦ1 HΦ2 HΦ3") as "(%v & $ & $)". }
    iIntros (((l & seen) & x)) "Hcas /=".
    iApply (imp_atomic' E1 E2).
    iMod "Hcas" as "(%v & Hl & Hcas)".
    iApply (imp_cas with "Hl Hcas").
  Qed.

End imp_atomic_rules.

Section imp_inv_rules.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.
  Context {N : namespace} {P : iProp Σ}.

  Lemma imp_store_inv `{Encode A} η e1 e2 (Φ1 : loc → _) (Φ2 : A → _) (Φ : () → _) :
    ↑N ⊆ E →
    inv N P -∗
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (▷ ∀ l x, Φ1 l -∗ Φ2 x -∗
              ▷ P -∗
              ∃ v, ▷ l ↦ v ∗
                   ▷ (l ↦ #x -∗ ▷ P ∗ Φ ())) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv He1 He2 Hstore".
    iApply (imp_store_atomic (E ∖ ↑N) with "He1 He2").
    iNext.
    iPoseProof (inv_acc with "Hinv") as ">[HP HClose]". assumption.
    iIntros "!>" (l x) "HΦ1 HΦ2".
    iDestruct ("Hstore" with "HΦ1 HΦ2 HP") as "(% & $ & Hstore)".
    iIntros "!> Hl".
    iDestruct ("Hstore" with "Hl") as "[HP HΦ]".
    iMod ("HClose" with "HP").
    iApply "HΦ".
  Qed.

  Lemma imp_CAS_inv `{PhysEqDec A} η e1 e2 e3 (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    ↑N ⊆ E →
    inv N P -∗
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    impure E (eval η e3) Ψ ζ Φ3 -∗
    (▷ ∀ l seen v',
       Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
       ▷ P -∗
       ∃ v, ▷ l ↦ #v ∗
            ▷ (l ↦ (if phys_eq_val_ v seen then #v' else #v) -∗
               ▷ P ∗ Φ (phys_eq_val_ v seen))) -∗
    impure E (eval η (ECAS e1 e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv He1 He2 He3 Hcas".
    iApply (imp_cas_atomic (E ∖ ↑N) with "He1 He2 He3").
    iNext.
    iPoseProof (inv_acc with "Hinv") as ">[HP HClose]". assumption.
    iIntros "!>" (l seen v') "HΦ1 HΦ2 HΦ3".
    iDestruct ("Hcas" with "HΦ1 HΦ2 HΦ3 HP") as "(% & $ & Hcas)".
    iIntros "!> Hl".
    iDestruct ("Hcas" with "Hl") as "[HP HΦ]".
    iMod ("HClose" with "HP").
    iApply "HΦ".
  Qed.

End imp_inv_rules.
