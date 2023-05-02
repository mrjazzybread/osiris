From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

Require Import base lang sugar locations free eval step wp wp_tactics encode notations incr Stdlib.

Context `{!osirisGS_gen hlc Σ}.


Definition pleasedontclash (*This is not a name. *) :=
  (* *** START OF A MODIFICATION TO THE TRANSLATION *** *)
  (* The current translator assumes that the user will provide the correct
     environment to work with previously-defined symbols. Nonetheless, as
     translations are in fact expressions and not values (at least for now), it
     would be tedious to do so. An alternative is to use the trick described in
     [traduction/lib/Pp.ml]: translate a single file as a huge let:
     let a, b, c, ... =
         let a_at_top-level := ... in
         let _ = ... in
         let b_at_top-level := ... in
         let c_at_top-level := ... in
         (a_at_top-level, ...).
     Notes:
       - this would also solve the issue of taking into account the
         [let _ = ...] and [let () = ...] that appear at top-level.
       - use structures instead of an enclosing let.

     For now, I add this let by hand, but the above trick will be directly
     applied by the translator in the futur. *)
  ELet
    (BiCons
       (Binding (PVar "new_counter")
                new_counter)
       BiNil) $
  (* ***  END OF A MODIFICATION TO THE TRANSLATION  *** *)
  incr.pleasedontclash.


Definition _test :=
  (* *** START OF A MODIFICATION TO THE TRANSLATION *** *)
  (* The current translator assumes that the user will provide the correct
     environment to work with previously-defined symbols. Nonetheless, as
     translations are in fact expressions and not values (at least for now), it
     would be tedious to do so. An alternative is to use the trick described in
     [traduction/lib/Pp.ml]: translate a single file as a huge let:
     let a, b, c, ... =
         let a_at_top-level := ... in
         let _ = ... in
         let b_at_top-level := ... in
         let c_at_top-level := ... in
         (a_at_top-level, ...).
     Notes:
       - this would also solve the issue of taking into account the
         [let _ = ...] and [let () = ...] that appear at top-level.
       - use structures instead of an enclosing let.

     For now, I add this let by hand, but the above trick will be directly
     applied by the translator in the futur. *)
  ELet
    (BiCons
       (Binding (PVar "new_counter")
                new_counter)
       BiNil) $
  (* ***  END OF A MODIFICATION TO THE TRANSLATION  *** *)
  incr._test.




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

Lemma new_counter__spec s E :
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval η new_counter @ s; E
       {{ λ v, {{{ ⌜ True ⌝ }}}
                 call v VUnit
               {{{ vget vupd,
                     RET (VTuple (VCons vget (VCons vupd VNil)));
                   ∃ ℓ,
                   is_counter ℓ 0 ∗
                   get_spec ℓ vget ∗
                   upd_spec ℓ vupd }}} }}.
Proof.
  intros. wp.
  iIntros (ϕ) "!> _ Hϕ".
  wp_call.
  iApply wp_covariant; first by iApply Stdlib__ref__spec.
  iIntros (?) "(%ℓ&Hℓ&->)".
  wp. iApply "Hϕ". clear ϕ.
  iExists ℓ.
  iSplitL; last iSplit.

  { (* Proof of the [is_counter] predicate. *)
    unfold is_counter. iExists _. by iFrame. }

  { (* Proving the specification of [get]. *)
    unfold get_spec. iIntros.
    iIntros(ϕ)"!>(%&->&Hℓ) Hϕ".
    wp_call. wp.

    iApply (wp_covariant with "[Hℓ]"); last first.
    { iIntros (v) "Hv".
      iApply "Hϕ". iAssumption. }

    { iApply (Stdlib__load__spec_tac with "[//]Hℓ").
      iIntros "Hℓ".
      iSplit; first done.
      iExists _; by iFrame. } }

  { (* Proof of the specification of [upd]. *)
    unfold upd_spec. iIntros.
    iIntros (ϕ) "!>(%&->&Hℓ) Hϕ".
    wp_call.
    iApply (Stdlib__store__spec_tac with "Hℓ[Hϕ]").
    iNext.
    iIntros "Hℓ".
    iApply "Hϕ".
    iExists _. by iFrame. }
Qed.


(* The following example shows issues in the standart library :
   - arithmetic operators should *not* require user interactions at all.
     TODO: write clean lemmas about totally applied ["Stdlib"."+"] and al. and
           add them to a hint database.
*)
Opaque new_counter.
Lemma pleasedontclash__spec :
  let η :=
    EnvCons "Stdlib" Stdlib $
    EnvNil in
  {{{ ⌜ True ⌝ }}}
    eval η pleasedontclash
  {{{ v, RET v; ⌜ v = VInt (int.repr 13) ⌝ }}}.
Proof.
  iIntros (η ϕ)"_ Hϕ".
  wp.

  (* Fetch the specification of [new_counter] proven above.
     TODO: better handle the use of recent definitions. *)
  pose proof (new_counter__spec) as Hspec; simpl in Hspec;
    iPoseProof Hspec as "#Hspec". clear Hspec.

  (* Use the aforementioned specification to get the value to which
     [new_counter] evaluates and its specification. *)
  iApply (wp_covariant with "Hspec").
  iIntros (vnew_counter)"#Hnew_counter_spec".

  (* I avoid using tactics from [wp_tactics.v] not to reduce under
     continuations anymore. *)
  iApply wp_par_ret_right.
  iApply wp_par_ret_ret.
  iNext.
  iApply wp_bind.
  iApply wp_ret.

  iApply ("Hnew_counter_spec" with "[//][Hϕ]").

  iNext. iIntros (vget vupd) "(%ℓ&Hcounter&#Hget&#Hupd)".
  iApply wp_try_ret.
  iApply wp_bind. iApply wp_ret.

  wp.
  iPoseProof (Stdlib__fst__spec_tac with "[//][Hϕ Hcounter]") as "H"; last iAssumption.
  wp.
  iPoseProof (Stdlib__snd__spec_tac with "[//][Hϕ Hcounter]") as "H"; last iAssumption.

  iNext.
  iApply wp_par_ret_right.
  iApply wp_par_ret_ret.
  iApply wp_bind.
  iApply wp_ret.

  iApply ("Hget" $! 0 NotStuck top with "Hcounter").
  do 2 iNext.
  iIntros (?)"(->&Hℓ)".

  iApply wp_try_ret.
  iApply wp_bind.
  iApply wp_ret.
  unfold concatenating.

  iApply wp_bind; fold eval.
  iApply wp_bind. iApply wp_par_ret_right.
  simpl (eval _ _).
  do 2 iApply wp_ret.

  iApply ("Hupd" with "Hℓ").
  iNext. iIntros "Hℓ".

  wp.

  iApply ("Hget" with "Hℓ").
  iNext.
  iIntros(?)"[->Hℓ]".
  iPoseProof (Stdlib__sub__spec) as "Hsub".
  { exact (eq_refl (VInt (int.repr 13))). }
  { exact (eq_refl (VInt (int.repr 0))). }
  iApply (wp_covariant with "Hsub").
  iIntros (v)"Hv".
  iApply (wp_covariant with "Hv"). clear v.
  iIntros (?->).
  iApply wp_ret.
  iApply "Hϕ".
  iPureIntro. reflexivity.
Qed.
