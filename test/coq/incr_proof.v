From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import incr.


Context `{!osirisGS_gen hlc Σ}.



(* --------------------------------------------------------------------------- *)
(* Definition of the specifications of the [get] and [upd] functions returned by
   [new_counter ()]. *)

Definition is_counter l i : iProp Σ :=
  ∃ v, ⌜ v = VInt (int.repr i) ⌝ ∗ l ↦ v.

Definition get_spec l get : iProp Σ :=
  ∀ i s E,
  {{{ is_counter l i }}}
    call get VUnit @ s; E
  {{{ v, RET v; ⌜ v = VInt (int.repr i) ⌝ ∗ is_counter l i }}}.

Definition upd_spec l upd : iProp Σ :=
  ∀ s E i i',
    {{{ is_counter l i }}}
      call upd (VInt (int.repr i')) @ s; E
    {{{ RET VUnit; is_counter l i' }}}.

Definition new_counter_spec v : iProp Σ :=
  {{{ ⌜ True ⌝ }}}
    call v VUnit
  {{{ vget vupd,
      RET (VTuple (VCons vget (VCons vupd VNil)));
      ∃ l,
        is_counter l 0 ∗
        get_spec l vget ∗
        upd_spec l vupd }}}.

Definition thirteen_spec v : iProp Σ :=
  ⌜ v = encode 13 ⌝.


Lemma Incr__spec:
  let Λ :=
    [
      ("new_counter", new_counter_spec);
      ("_test", thirteen_spec)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Incr {{ module_spec Λ }}.
Proof.
  iIntros.
  wp.

  (* Prove that [new_counter] matches its specification (defined above). *)
  wp_specify "new_counter" new_counter_spec.
  { iIntros (φ) "!>_ Hφ".
    wp_call. wp_continue.
    iApply wp_covariant; first by iApply Stdlib__ref__spec.
    iIntros (?) "(%l&Hl&->)".
    wp_autocontinue. wp_use "Hφ". clear φ.
    iExists l.
    iSplitL; last iSplit.
    { (* Proof of the [is_counter] predicate. *)
      unfold is_counter. iExists _. by iFrame. }

    { (* Proving the specification of [get]. *)
      unfold get_spec. iIntros.
      iIntros(φ)"!>(%&->&Hl) Hφ".
      wp_call. wp_autocontinue.

      iApply (Stdlib__load__spec_tac $! φ with "[//]Hl").

      iIntros "Hl".
      iApply "Hφ".
      iSplit; first done.
      iExists _; by iFrame. }

    { (* Proof of the specification of [upd]. *)
      unfold upd_spec. iIntros.
      iIntros (φ) "!>(%&->&Hl) Hφ".
      wp_call. wp_continue.
      iApply (Stdlib__store__spec_tac with "Hl[Hφ]").
      iNext. iIntros "Hl".
      iApply "Hφ".
      iExists _. by iFrame. }
  }
  iIntros(new_counter) "#Hnew_counter". wp_continue.

  (* The interpreter stops at the first call of [new_couter]. This call can be
     found in the [let () = ...] of the OCaml file. *)
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget vupd) "(%l&Hl&#Hget&#Hupd)".
  wp_continue. wp. do 2 wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp_continue.

  wp_use ("Hupd" with "Hl").
  iNext. iIntros "Hl".
  wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp. wp_continue.


  iClear "Hget Hupd Hl". clear l.


  (* The interpreter stops at the second call of [new_counter], which occurs in
     the definition of [_test]. *)
  wp_continue.
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget' vupd') "(%l&Hl&#Hget&#Hupd)". wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".
  wp_continue.

  wp_use ("Hupd" with "Hl").
  iNext. iIntros "Hl".
  wp_continue.

  wp_use ("Hget" with "Hl").
  iNext. iIntros (?)"[->Hl]".

  wp. wp_continue.

  wp_specify "_test" thirteen_spec; first trivial.
  iIntros(_test)"#H_test". wp_continue.


  (* As all the required specifications have already been proven,
     [wp_module_spec] will finish the proof. *)
  wp_module_spec.
Time Qed.
