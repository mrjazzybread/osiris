From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_incr.

Local Transparent eval. (* TODO. *)


Context `{!osirisGS Σ}.

(* --------------------------------------------------------------------------- *)
(* Definition of the specifications of the [get] and [upd] functions returned by
   [new_counter ()]. *)

Definition is_counter l (i: Z) : iProp Σ :=
  ∃ v, ⌜ v = #i ⌝ ∗ l ↦ v.

Definition get_spec l get : iProp Σ :=
  ∀ i s E,
  {{{ is_counter l i }}}
    call get VUnit @ s; E
  {{{ v, RET v; ⌜ v = #i ⌝ ∗ is_counter l i }}}.

Definition upd_spec l upd : iProp Σ :=
  ∀ s E i i',
    {{{ is_counter l i }}}
      call upd #i' @ s; E
    {{{ RET VUnit; is_counter l i' }}}.

Definition new_counter_spec v : iProp Σ :=
  {{{ ⌜ True ⌝ }}}
    call v VUnit
  {{{ vget vupd,
      RET #(vget, vupd);
      ∃ l,
        is_counter l 0 ∗
        get_spec l vget ∗
        upd_spec l vupd }}}.

Definition thirteen_spec v : iProp Σ :=
  ⌜ v = #13 ⌝.

Lemma Incr__spec:
  let Λ :=
    [
      ("new_counter", new_counter_spec);
      ("_test", thirteen_spec)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  ⊢ WP eval_mexpr η _Incr {{ module_spec Λ }}.
Proof.
  iIntros.
  wp until "new_counter" !.

  (* Prove that [new_counter] matches its specification (defined above). *)
  oSpecify "new_counter" new_counter_spec vnew_counter "#Hnew_counter".
  { iIntros (φ) "!>_ Hφ".
    iClear "Hnew_counter". (* TODO [new_counter] is not recursive! *)
    wp. wp_continue.
    wp_alloc l "[Hl _]". wp_bind.
    wp_continue. wp_continue. wp_continue.
    wp_use "Hφ". clear φ.
    iExists l.
    iSplitL; last iSplit.
    { (* Proof of the [is_counter] predicate. *)
      unfold is_counter. iExists _. by iFrame. }

    { (* Proving the specification of [get]. *)
      unfold get_spec. iIntros.
      iIntros(φ)"!>(%&->&Hl) Hφ".
      wp. wp_continue.

      wp_load "Hl".
      iApply "Hφ".
      iSplit; first done.
      iExists _; by iFrame. }

    { (* Proof of the specification of [upd]. *)
      unfold upd_spec. iIntros.
      iIntros (φ) "!>(%&->&Hl) Hφ".
      wp.
      wp_store "Hl".
      iApply "Hφ".
      iExists _. by iFrame. }
  }

  (* The interpreter stops at the first call of [new_counter]. *)
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget vupd) "(%l&Hl&#Hget&#Hupd)".
  wp_bind. (* TODO seems slow *)
  do 4 wp_continue. (* TODO also slow *)

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp_bind.
  wp_continue.
  wp_bind.

  wp_use ("Hupd" with "Hl").
  iNext. iIntros "Hl".
  wp_bind.
  wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp. wp_continue. wp_bind.


  iClear "Hget Hupd Hl". clear l.


  (* The interpreter stops at the second call of [new_counter], which occurs in
     the definition of [_test]. *)
  wp_continue.
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget' vupd') "(%l&Hl&#Hget&#Hupd)".
  wp_bind.
  wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp_bind.
  wp_continue. wp_bind.

  wp_use ("Hupd" with "Hl").
  iNext. iIntros "Hl".
  wp_bind.
  wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".

  wp.
  wp_continue. wp_bind.

  wp_continue.


  (* As all the required specifications have already been proven,
     [wp_module_spec] will finish the proof. *)
  wp_module_spec.
Time Qed.
