From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_exception.

Context `{!osirisGS Σ}.

(* TODO: We manually add exceptions to the environment. *)

Definition stdlib_with_notfound :=
  ("Not_found", (VLoc (Loc 0))) :: stdlib_env.

(* Calling [head #l] either returns [#h] when [l = h :: t],
   or throws an exception when [l = []]. *)

Definition head_spec head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    ⊢ ewp_def top (call head #l) ⊥
      (| RET x => ∃ h t, ⌜l = h :: t /\ x = #h⌝ ;
       | EXN e => ⌜e = VXData (Loc 0) [] /\ l = []⌝ )%I.

(* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
   or returns [None] when [l = []]. *)

Definition catch_head_spec catch_head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    ⊢ ewp_def top (call catch_head #l) ⊥
      (RET #hopt, ⌜match l with
                  | [] => hopt = None
                  | h :: _ => hopt = Some h
                  end⌝)%I.

Lemma example :
  eval_module stdlib_with_notfound __main (λ η, True).
Proof.
  unfold __main.
  apply module_struct.

  (* Struct item: [let head l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := head_spec).
    pure_simp; unfold head_spec; intros.
    iIntros.
    destruct l; Simp.
    { iApply ewp_throw. simpl. equality. }
    { Ret. simpl. eauto. } }
  intros [??] (head & Hhead & -> & ->); simpl.

  (* Struct item: [let catch_head l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    iIntros. iApply ewp_call_nonrec.
    iModIntro.
    prove_match.
    { (* Call to [head]. *)
      Simp. iApply Hhead. }
    iIntros ([h|e]).
    { (* Value case. *)
      iIntros "(%h0 & %t & -> & ->)".
      iModIntro.
      next_branch.
      next_branch.
      { Simp. iApply ewp_value. simpl.
        iExists (Some h0). equality. } }
    { (* Exception case. *)
      iIntros "[-> ->]".
      next_branch; fold eval.
      iApply ewp_EConstant.
      iExists (None). done. } }

  intros [??] (catch_head & Hcatch_head & -> & ->); simpl.

  (* Struct item: [let catch_head2 l = ...] *)
  eapply structs_cons.
  { apply struct_let_single with (spec := catch_head_spec).
    pure_simp; unfold catch_head_spec; intros.
    iIntros. iApply ewp_call_nonrec.
    iModIntro.
    Simp. Simp.
    (* Reshape the goal to get [EWP try (o ← call head #l; ...)] *)
    iApply ewp_try.
    (* Call to head. *)
    iApply ewp_mono. { iApply Hhead. }
    iIntros ([]) "Ho"; cbn.
    { iApply ewp_value. cbn.
      iDestruct "Ho" as "(%h & %t & -> & ->)".
      iPureIntro. exists (Some h). eauto.  }
    { iDestruct "Ho" as "(-> & ->)".
      Simp. iApply ewp_value. 
      iPureIntro. exists None. eauto. } }
  intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

  (* We have gone though all of the struct items, time to conclude. *)
  eapply structs_nil.
  done.
Qed.
