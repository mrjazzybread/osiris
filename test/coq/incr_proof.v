From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics notations.
From osiris.libs Require Import Stdlib.
From test Require Import incr.


Context `{!osirisGS_gen hlc Σ}.



(* --------------------------------------------------------------------------- *)
(* Definition of the specifications of the [get] and [upd] functions returned by
   [new_counter ()]. *)

Definition is_counter ℓ i : iProp Σ :=
  ∃ v, ⌜ v = VInt (int.repr i) ⌝ ∗ ℓ ↦ v.

Definition get_spec ℓ get : iProp Σ :=
  ∀ i s E,
  {{{ is_counter ℓ i }}}
    call get VUnit @ s; E
  {{{ v, RET v; ⌜ v = VInt (int.repr i) ⌝ ∗ is_counter ℓ i }}}.

Definition upd_spec ℓ upd : iProp Σ :=
  ∀ s E i i',
    {{{ is_counter ℓ i }}}
      call upd (VInt (int.repr i')) @ s; E
    {{{ RET VUnit; is_counter ℓ i' }}}.

Definition new_counter_spec v : iProp Σ :=
  {{{ ⌜ True ⌝ }}}
    call v VUnit
  {{{ vget vupd,
      RET (VTuple (VCons vget (VCons vupd VNil)));
      ∃ ℓ,
        is_counter ℓ 0 ∗
        get_spec ℓ vget ∗
        upd_spec ℓ vupd }}}.

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
    iIntros (?) "(%ℓ&Hℓ&->)".
    wp_autocontinue. wp_use "Hφ". clear φ.
    iExists ℓ.
    iSplitL; last iSplit.
    { (* Proof of the [is_counter] predicate. *)
      unfold is_counter. iExists _. by iFrame. }

    { (* Proving the specification of [get]. *)
      unfold get_spec. iIntros.
      iIntros(ϕ)"!>(%&->&Hℓ) Hϕ".
      wp_call. wp_autocontinue.

      iApply (Stdlib__load__spec_tac $! ϕ with "[//]Hℓ").

      iIntros "Hℓ".
      iApply "Hϕ".
      iSplit; first done.
      iExists _; by iFrame. }

    { (* Proof of the specification of [upd]. *)
      unfold upd_spec. iIntros.
      iIntros (ϕ) "!>(%&->&Hℓ) Hϕ".
      wp_call.
      iApply (Stdlib__store__spec_tac with "Hℓ[Hϕ]").
      iNext. iIntros "Hℓ".
      iApply "Hϕ".
      iExists _. by iFrame. }
  }
  iIntros(new_counter) "#Hnew_counter". wp_continue.

  (* The interpreter stops at the first call of [new_couter]. This call can be
     found in the [let () = ...] of the OCaml file. *)
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget vupd) "(%ℓ&Hℓ&#Hget&#Hupd)".
  wp_continue.

  wp_use Stdlib__fst__spec_tac; first done. iNext. wp_continue.
  wp_use Stdlib__snd__spec_tac; first done. iNext. wp_continue.

  wp_use ("Hget" with "Hℓ").
  iNext. iIntros (?)"[->Hℓ]".
  wp_continue.

  wp_use ("Hupd" with "Hℓ").
  iNext. iIntros "Hℓ".
  wp_continue.

  wp_use ("Hget" with "Hℓ").
  iNext. iIntros (?)"[->Hℓ]".
  wp_continue.

  wp_use Stdlib__sub__spec;
    [ done | done | ].
  iIntros (vsub)"Hsub". iApply (wp_covariant with "Hsub").
  iIntros (?->).

  iClear "Hget Hupd Hℓ". clear ℓ.


  (* The interpreter stops at the second call of [new_counter], which occurs in
     the definition of [_test]. *)
  wp_continue.
  wp_use ("Hnew_counter" with "[//][]"). iNext.
  iIntros (vget' vupd') "(%ℓ&Hℓ&#Hget&#Hupd)". wp_continue.

  wp_use ("Hget" with "Hℓ").
  iNext. iIntros (?)"[->Hℓ]".
  wp_continue.

  wp_use ("Hupd" with "Hℓ").
  iNext. iIntros "Hℓ".
  wp_continue.

  wp_use ("Hget" with "Hℓ").
  iNext. iIntros (?)"[->Hℓ]".

  wp_use Stdlib__sub__spec;
    [ done | done | ].
  iIntros (vsub')"Hsub". iApply (wp_covariant with "Hsub").
  iIntros (?->). wp_continue.

  wp_specify "_test" thirteen_spec; first trivial.
  iIntros(_test)"#H_test". wp_continue.


  (* As all the required specifications have already been proven,
     [wp_module_spec] will finish the proof. *)
  wp_module_spec.
Time Qed.
(* With iApply everywhere 8.057 *)
