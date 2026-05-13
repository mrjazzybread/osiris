From osiris Require Import osiris.
From iris.proofmode Require Import ltac_tactics.

From osiris.examples Require Import og_record_test.

Open Scope Z.

Section verification.

  Context `{!osirisGS Σ}.

  Definition length_spec r (m : microvx) : iProp Σ :=
    ∀ dq t (x y : Z),
      ▷ @ownRecord Σ _ τ[Z; Z] r dq t (x, y) -∗
      imp m {{ λ (i : Z), ⌜i = (x*x + y*y)%Z⌝ ∗ @ownRecord _ _ τ[Z; Z] r dq t (x, y) }}.

  Definition elength := EAnonFun __fun0.

  Lemma imp_length η :
    ⊢ imp (eval η elength) {{ λ length, □ iSpec τ[record] length length_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r dq t x y) "Hown".

    iApply imp_please; iNext.

    (* TODO: split ownership of record here. *)

    (* Goal: [(v.x * v.x) + (v.y * v.y)] *)
    imp_arith with "[Hown]".
    - (* Subgoal: [(v.x * v.x)] *)
      admit.
    - (* Subgoal: [(v.y * v.y)] *)
      admit.
  Admitted.


  Definition update_x_spec r x (m : microvx) : iProp Σ :=
    ∀ t (x0 y : Z),
      ▷ @ownRecord Σ _ τ[Z;Z] r (DfracOwn 1) t (x0, y) -∗
      imp m {{ λ (_ : unit), @ownRecord Σ _ τ[Z;Z] r (DfracOwn 1) t (x, y) }}.

  Definition eupdate_x := EAnonFun __fun2.

  Lemma imp_update_x η :
    ⊢ imp (eval η eupdate_x) {{ λ update_x, □ iSpec τ[record; Z] update_x update_x_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r x t x0 y) "Hown".
    iApply imp_please; iNext.
    iApply imp_mono_val; last first.

    iApply (imp_ERecordSet with "[%] Hown"). split; simpl; lia.
    imp_path.
    imp_path.
    iIntros ([]) "(% & -> & $)".
  Qed.

  Lemma module_proof η :
    2 ≤ max_array_length →
    ⊢ imp (eval_mexpr η __main)
      {{ context
           [ var_spec "length" (λ length, iSpec τ[record] length length_spec);
             var_spec "update_x" (λ update, iSpec τ[record;Z] update update_x_spec) ]
           {[ "vec"; "length"; "update_x" ]} }}.
  Proof.
    intros Hmax_array.
    iApply imp_module.

    iApply (imp_sitems_let (A:=record)).
    { iApply (imp_ERecord (τ:=τ[Z; Z])).
      { iPureIntro. simpl. lia. }
      set_postcondition (λ '(x, y), ⌜x = 1⌝ ∗ ⌜y = 1⌝)%I. simpl.
      admit. }

    iIntros (r) "H /=". fold eval_sitems.
    iDestruct "H" as "(% & Hown & Heq)".
    destruct xs. iDestruct "Heq" as "(-> & ->)".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_length. }

    iIntros (length) "#Hlength".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_update_x. }

    iIntros (update_x) "#Hupdate_x".
    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Admitted.
