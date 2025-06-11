From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_exception.

(* TODO: We manually add exceptions to the environment. *)

Definition stdlib_with_notfound :=
  ("Not_found", (VLoc (Loc 0))) :: stdlib_env.

Section proof.

Context `{!osirisGS Σ}.

(* Calling [head #l] either returns [#h] when [l = h :: t],
   or throws an exception when [l = []]. *)

Definition head_spec head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    ⊢ ewp_def top (call head #l) ⊥
      (  RET x => ∃ h t, ⌜l = h :: t /\ x = #h⌝ ;
       | EXN e => ⌜e = VXData (Loc 0) [] /\ l = []⌝ )%I.

(* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
   or returns [None] when [l = []]. *)

Definition catch_head_spec catch_head :=
  ∀ (A : Type) (H : Encode A) (l : list A),
    ⊢ ewp_def top (call catch_head #l) ⊥
      (ensures #hopt, ⌜match l with
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
    prove_match.
    { Simp. iApply ewp_bind_exn.
      iApply ewp_mono. { iApply Hhead. }
      iIntros ([ v | ex ]) "Houtcome".
      - simpl.
        iApply (ewp_value _ _ (RET v => bi_pure(_ v); | EXN e => bi_pure(_ e))%I).
        iDestruct "Houtcome" as "(%h & %t & -> & ->)".
        iPureIntro.
        instantiate (1 := (λ v, ∃ h t, l = h :: t ∧ v = (#(Some h)))).
        simpl. eexists; eauto.
      - simpl.
        iDestruct "Houtcome" as "(%Hex & %Hl)".
        iPureIntro.
        instantiate (1 := (λ e, e = VXData {| address := 0 |} [] ∧ l = [])).
        simpl; eauto. }

    iIntros ([h|e]).
    { (* Value case. *)
      iIntros "(%h0 & %t & -> & ->)".
      iModIntro.
      next_branch.
      iApply ewp_EPath. iApply ewp_value. iPureIntro. eauto. }
    { (* Exception case. *)
      iIntros "[-> ->]".
      next_branch. next_branch.
      iApply ewp_EConstant.
      iExists (None). done. } }

  intros [??] (catch_head2 & Hcatch_head2 & -> & ->); simpl.

  (* We have gone though all of the struct items, time to conclude. *)
  eapply structs_nil.
  done.
Qed.

End proof.
