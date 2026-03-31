From iris.base_logic.lib Require Import invariants token.
From osiris Require Import osiris.
From osiris.proofmode Require Import proofmode.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_spinlock.

(** * Invariant-based spinlock specification

    We follow the CMRA from Iris' [spin_lock] example, where we have:

    – [lock_inv γ l R]: the physical lock bit together with the user
      resource [R] and an exclusive token; the resource lives behind [▷].
    – [is_lock γ l R ≔ inv N (lock_inv γ l R)]: a *persistent* handle
      handed to every caller.
    – [locked γ ≔ token γ]: the exclusive ghost token held by the holder.
 *)

Definition spinlock_N : namespace := nroot .@ "spinlock".

Section spinlock_inv_proof.

Context `{!osirisGS Σ, !na_invG Σ}.

(* ------------------------------------------------------------------ *)
(* Ghost predicates *)


(** Invariant content.  When the lock is free ([b = false]) it stores
    [token γ ∗ ▷R]; the [▷] absorbs the later introduced by [iInv]. *)
Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  l ↦ #true ∨ (l ↦ #false ∗ token γ ∗ ▷R).

Definition is_lock (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  inv spinlock_N (lock_inv γ l R).

Definition locked (γ : gname) : iProp Σ := token γ.

(* ------------------------------------------------------------------ *)
(* Specifications *)


(* [create ()] allocates [ref false] and exposes the lock.  The caller
   may initialise it with any [▷R] to receive [is_lock γ l R]. *)
Definition create_spec (u : unit) (m : microvx) : iProp Σ :=
  imp m {{ λ (l : loc), ∀ (R : iProp Σ), ▷R ={⊤}=∗ ∃ γ, is_lock γ l R }}.

(* Acquiring the lock transfers ownership of [locked γ] and [▷R]. *)
Definition acquire_spec (l : loc) (m : microvx) : iProp Σ :=
  ∀ γ (R : iProp Σ), is_lock γ l R -∗ imp m {{ λ (_ : unit), locked γ ∗ ▷R }}.

(* Releasing requires the holder to give back [locked γ] and [▷R]. *)
Definition release_spec (l : loc) (m : microvx) : iProp Σ :=
  ∀ γ (R : iProp Σ), is_lock γ l R -∗ locked γ -∗ ▷R -∗ imp m {{ λ (_ : unit), True }}.

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

Global Instance store_atomic l v :
  thread_step.Atomic (code.store l v).
Proof.
  unfold thread_step.Atomic. intros.

  destruct_thread_step.
  unfold step_store_2.
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


Lemma imp_store_atomic `{Encode A} (E1 E2 : coPset) η e1 e2 Ψ ζ (Φ1 : loc → _) (Φ2 : A → _) (Φ : () → _) :
  impure E1 (eval η e1) Ψ ζ Φ1 -∗
  impure E1 (eval η e2) Ψ ζ Φ2 -∗
  ▷ (|={E1,E2}=>
       ∀ l x, Φ1 l -∗ Φ2 x -∗
              ∃ v, ▷ l ↦ v ∗
                   ▷ (l ↦ #x -∗ |={E2,E1}=> Φ ())) -∗
  impure E1 (eval η (EStore e1 e2)) Ψ ζ Φ.
Proof.
  iIntros "He1 He2 Hstore".
  simpl_eval. fold (as_loc (eval η e1)).
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

Lemma imp_store_inv `{Encode A} (E : coPset) N η e1 e2 Ψ ζ (Φ1 : loc → _) (Φ2 : A → _) (Φ : () → _) P :
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
  iApply (imp_store_atomic E (E ∖ ↑N) with "He1 He2").
  iNext.
  iPoseProof (inv_acc with "Hinv") as ">[HP HClose]". assumption.
  iIntros "!>" (l x) "HΦ1 HΦ2".
  iDestruct ("Hstore" with "HΦ1 HΦ2 HP") as "(% & $ & Hstore)".
  iIntros "!> Hl".
  iDestruct ("Hstore" with "Hl") as "[HP HΦ]".
  iMod ("HClose" with "HP").
  iApply "HΦ".
Qed.

Lemma imp_CAS_atomic `{PhysEqDec A} N (E : coPset) η e1 e2 e3 Ψ ζ (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) P :
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
  simpl_eval. fold (as_loc (eval η e1)).
  iApply (imp_bind (A1:=loc * A * A) with "[-]").
  set_postcondition
    (λ '((l, seen, v') : loc * A * A),
       |={E,E ∖ ↑N}=> ∃ v, ▷ l ↦ #v ∗
       ▷ (l ↦ (if phys_eq_val_ v seen then #v' else #v) -∗ |={E ∖ ↑N,E}=> Φ (phys_eq_val_ v seen)))%I.
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
      iNext.
      iPoseProof (inv_acc with "Hinv") as ">[Hopen Hclose]". assumption.
      iModIntro.
      iDestruct ("Hcas" with "HΦ1 HΦ2 HΦ3 Hopen") as "(%v & $ & Hcas)".
      iIntros "!> Hl".
      iDestruct ("Hcas" with "Hl") as "(HP & HΦ)".
      iMod ("Hclose" with "HP").
      iApply "HΦ". }
  iIntros (((l & seen) & x)) "Hcas /=".
  iApply (imp_atomic' E (E ∖ ↑N)).
  iMod "Hcas" as "(%v & Hl & Hcas)". iModIntro.
  iApply (imp_cas with "Hl Hcas").
Qed.

(* ------------------------------------------------------------------ *)
(* Module-level theorem *)

Lemma spinlock_inv_proof :
  ⊢ imp (eval_mexpr stdlib_env __main)
    {{ context [
         var_spec "create"  (λ create,  □ iSpec τ[unit] create create_spec);
         var_spec "acquire" (λ acquire, □ iSpec τ[loc]  acquire acquire_spec);
         var_spec "release" (λ release, □ iSpec τ[loc]  release release_spec)
       ] {["create"; "acquire"; "release"]} }}.
Proof.
  iApply imp_module.

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let create () = ref false] *)

  iApply (imp_sitems_let (λ create : val, □ iSpec τ[unit] create create_spec)%I).
  { iApply (imp_EAnon_pers τ[unit]).
    iIntros "!>" ([]).
    iApply imp_please; iNext.
    iApply (imp_EMatch (A':=unit)).
    { imp_path. }
    iIntros (? ->) "!>".
    iApply deep_handle_cons.
    { iPureIntro; ltac2:(let _ := specify_cpattern () in ()). pattern_match. apply eq_refl. }
    iSplit; last iIntros ([]).
    iIntros (?) "<-".
    (* After [ref false] we have [l ↦ #false]; use it to build the invariant. *)
    iApply (imp_wand).
    { imp_ref false. }
    iIntros (l) "Hl".
    (* Goal: ∀ R, ▷R ={⊤}=∗ ∃ γ, is_lock γ l R *)
    iIntros (R) "HR".
    iMod token_alloc as "(%γ & Htok)".
    iMod (inv_alloc spinlock_N _ (lock_inv γ l R) with "[Hl Htok HR]") as "#Hinv".
    { (* Provide ▷ (lock_inv γ l R) with b = false via [later_intro]. *)
      iNext. iRight. iFrame. }
    iModIntro. iExists γ. iExact "Hinv". }

  iIntros (create) "#Hcreate".

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let acquire lk = while !lk do () done; lk := true] *)

  iApply (imp_sitems_let (λ acquire : val, □ iSpec τ[loc] acquire acquire_spec)%I).
  { iApply (imp_EAnon_pers τ[loc]).
    (* After introducing [l : loc], the spec universally quantifies over [γ] and
       [R]; we introduce them here. *)
    iIntros "!>" (l). unfold acquire_spec.
    iIntros (γ R) "#Hinv".
    iApply imp_please; iNext.

    (* Subgoal: [while not (Atomic.set_and_compare lk false true) do () done] *)
    iApply (imp_EWhile (λ b, if b then True else locked γ ∗ ▷ R)%I).
    - (* I true *)
      done.
    - (* Condition: load [!lk] directly from [l ↦ #b'] *)
      iIntros "!> _".
      iApply imp_EBoolNeg.

      iApply (imp_CAS_atomic (A:=bool) with "Hinv"); try imp_step. set_solver.
      iIntros "!>" (???) "-> -> -> [Hl | (Hl & Htok & HR) ]".

      + (* Subcase: the CAS returned true. *)
        iFrame.
        iIntros "!> Hl".
        iSplitL. { iLeft. iApply "Hl". } done.

      + (* Subcase: the CAS returned false. *)
        iFrame.
        iIntros "!> Hl".
        simpl. iFrame.

    - (* Evaluating the body. *)
      iIntros "!> _".
      by iApply imp_EUnit. }

  iIntros (acquire) "#Hacquire".

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let release lk = lk := false] *)
  iApply (imp_sitems_let (λ release : val, □ iSpec τ[loc] release release_spec)%I).
  { iApply (imp_EAnon_pers τ[loc]).
    iIntros "!>" (l).
    iIntros (γ R) "#Hinv Htok HR".
    iApply imp_please; iNext.
    (* Open invariant non-atomically: get [l ↦ #b] in hand, store [false],
       then close with [l ↦ #false ∗ token γ ∗ ▷R]. *)
    iApply (imp_store_inv (A:=bool) with "Hinv"); try imp_step. set_solver.
    iIntros "!>" (??) "-> -> Hopened".
    iDestruct "Hopened" as "[ $ | ($ & >Htok' & HR') ]".
    - iIntros "!> Hl".
      iSplitL. { iRight. iFrame. }
      done.
    - (* This case is impossible: we own [token γ],
         so the lock cannot have been open. *)
      iPoseProof (token_exclusive with "Htok Htok'") as "[]". }

  iIntros (release) "#Hrelease".

  (* ------------------------------------------------------------------ *)
  (* Conclude                                                            *)
  iApply imp_sitems_nil.
  iFrame "#"; simpl. auto.
Qed.

End spinlock_inv_proof.
