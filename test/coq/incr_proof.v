From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang encode.
From osiris.semantics Require Import sugar locations free eval step notations.
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



Definition spec_env : Type :=
  gmap var (val → iProp Σ).

Definition module_spec_env (Λ : spec_env) (η: env) : iProp Σ :=
  ∀ x,
  ∃ φ, ⌜Λ !! x = Some φ⌝ -∗
       ∃ v, ⌜lookup_name η x = Ret v⌝ -∗
       φ v.


Definition module_spec (Λ : spec_env) (v: val) : iProp Σ :=
  ∃ η, ⌜ v = VStruct η ⌝ ∗ module_spec_env Λ η.


Implicit Type Λ : spec_env.
Implicit Type η : env.
Implicit Type x : var.
Implicit Type e : expr.

Definition module_spec_delete x Λ :=
  let φ : val → iProp Σ := λ _, ⌜False⌝%I in
  <[ x := φ ]> Λ.


Lemma module_spec_ILet_now Λ η x e (t: list sitem) φx :
  Λ !! x = Some φx →
  let Λx := module_spec_delete x Λ in
  ⊢ WP eval η e {{ φx }} -∗
    (∀ v, φx v -∗
      WP eval_mexpr (EnvCons x v η) (MkStruct t) {{ module_spec Λx }}) -∗
    WP eval_mexpr η (MkStruct (ILet (Binding1 (PVar x) e) :: t))
    {{ module_spec Λ }}.
Proof.
  iIntros (Hsome Λx) "He Ht".
  wp.
  iApply (wp_covariant with "He").
  iIntros (v) "Hv".
  iSpecialize ("Ht" with "Hv").
Admitted.

Lemma Incr__spec s E:
  let Λ :=
    {[
      "new_counter" := new_counter_spec;
      "test" := thirteen_spec
    ]}
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Incr @ s; E {{ module_spec Λ }}.
Proof.
  intros.
  unfold Incr.
  iStartProof.
  remember (EFun1Pat _ _).
  remember (Binding1 PAny _).
  remember (Binding1 (PVar "_test") (ELet _ _)).

  wp.
  wp_call.
  iApply wp_covariant; first by iApply Stdlib__ref__spec.
  iIntros (?)"(%l&Hl&->)".
  wp.
  iPoseProof (Stdlib__snd__spec_tac with "[//][Hl]") as "H"; last iAssumption.
  wp.
  wp_call.
  iApply (Stdlib__load__spec_tac with "[//]Hl").
  iIntros "Hl".
  wp.
  iApply (Stdlib__store__spec_tac with "Hl").
  wp.
  iIntros "Hl".
  wp.
  wp_call.
  iApply (Stdlib__load__spec_tac with "[//]Hl").
  iIntros "Hl".
  wp.
  iApply (Stdlib__store__spec_tac with "Hl").



(* --------------------------------------------------------------------------- *)
(* Proof of the program. *)

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

  (* TODO: fix the proof ([Stdlib__ref__spec_tac] should be applicable instead
     of using [wp_covariant]). *)
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
  wp.
  iApply ("Hnew_counter_spec" with "[//][Hϕ]").

  iNext. iIntros (vget vupd) "(%ℓ&Hcounter&#Hget&#Hupd)".

  wp.
  iPoseProof (Stdlib__fst__spec_tac with "[//][Hϕ Hcounter]") as "H"; last iAssumption.

  wp.
  iPoseProof (Stdlib__snd__spec_tac with "[//][Hϕ Hcounter]") as "H"; last iAssumption.

  wp.

  iApply ("Hget" $! 0 NotStuck top with "Hcounter").
  iNext.
  iIntros (?)"(->&Hℓ)".

  wp.
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
Time Qed.
