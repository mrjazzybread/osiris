From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_stateless.


Section Specifications.
  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Specifications for the module [Counter]. *)

  Definition is_counter (n : nat) (v : val) : iProp Σ :=
    ∃ (ℓ : loc), ⌜v = #ℓ⌝ ∗ ℓ ↦ #n.

  Definition make_spec (vmake : val) : iProp Σ :=
    □ WP call vmake #() {{ λ res, is_counter O res }}.

  Definition get_spec (vget : val) : iProp Σ :=
    □ ∀ (v : val) (n : nat),
    is_counter n v -∗ WP call vget v {{ λ res, ⌜res = #n⌝ ∗ is_counter n v }}.

  Definition incr_spec (vincr : val) : iProp Σ :=
    □ ∀ (v : val) (n : nat),
    is_counter n v -∗
    WP call vincr v {{ λ res, ⌜res = VUnit⌝ ∗ is_counter (S n) v }}.
  Definition set_spec (vset : val) : iProp Σ :=
    □ ∀ (v : val),
    WP call vset v {{
          λ res,
            ∀ (n m : nat),
            ⌜(n <= m)%nat⌝ →
            ⌜representable n⌝ →
            ⌜representable m⌝ →
            is_counter n v -∗
            WP call res #m {{ λ res, ⌜res = VUnit⌝ ∗ is_counter m v }} }}.

  Definition Counter_specs : spec val :=
    SpecModule
      Auto
      [
        ("make", SpecImpure NoAuto make_spec) ;
        ("get", SpecImpure NoAuto get_spec) ;
        ("incr", SpecImpure NoAuto incr_spec) ;
        ("set", SpecImpure NoAuto set_spec)
      ]
      emp%I.

  Definition Counter_spec : val → iProp Σ :=
    λ v, (□ satisfies_spec Counter_specs v)%I.

  Definition Stateless_spec (v : val) : iProp Σ :=
    □ satisfies_spec
      (SpecModule Auto [("Counter", SpecImpure NoAuto Counter_spec)] emp%I) v.
End Specifications.



Section ProofExamples.
  Context `{!osirisGS Σ}.

  Ltac call := @oCall unfold.
  Ltac prove_counter := iSplit;
                      [ by equality
                      | iExists _; iSplit ; [ equality | iFrame ] ].
  Ltac wp_prove_spec :=
    iExists _;
    by (iSplit;
        [ done | repeat (iSplit; first (iExists _; iSplit; done))] ).


  (* This proof uses variables in the context instead of an explicit environment
     [η] to the goal below. This is thought to be easier to use in the proof of
     foreign modules. *)
  Variables (η : env)
            (Hη_ref: lookup_name η "ref" = Ret Stdlib__ref)
            (Hη_load: lookup_name η "!" = Ret Stdlib__load)
            (Hη_store: lookup_name η ":=" = Ret Stdlib__store)
            (Hη_add: lookup_name η "+" = Ret Stdlib__add)
            (Hη_le: lookup_name η "<=" = Ret Stdlib__le).

  Lemma Stateless_correct :
    ⊢ WP eval_mexpr η __main {{ Stateless_spec }}.
  Proof using Hη_add Hη_le Hη_load Hη_ref Hη_store osirisGS0 Σ η.
    oSpecify "make" make_spec vmake "#Hmake" !.
    { iIntros "!>".
      @oCall unfold; wp_bind; wp_continue.
      wp_alloc ℓ "[Hℓ _]".
      iExists ℓ.
      iSplit; first equality.
      by cbn. }


    oSpecify "incr" incr_spec vincr "#Hincr" !.
    { iIntros "!>" (? n) "(%ℓ&->&Hℓ)".
      call. wp_load "Hℓ". wp_store "Hℓ".
      replace (VInt (repr (n + 1))) with (#(S n)); last first.
      { simpl. do 2 f_equal; lia. }
      prove_counter. }

    oSpecify "set" set_spec vset "#Hset" !.
    { iIntros "!>" (vc). call.
      iIntros (n m Hle ??) "(%ℓ&->&Hℓ)". call.
      (* TODO deal with [EAssert] properly *)
      rewrite eval_eval'. simpl.
      rewrite <- try_choose. rewrite <- bind_as_try.
      iApply (wp_bind_binary with "[Hℓ]").
      { wp.
        iApply (wp_choose_ok _ _ _ (ℓ ↦ #n)%I with "[Hℓ]").
        + iFrame.
        + iModIntro. iIntros "Hℓ".
          wp.
          wp_load "Hℓ".
          rewrite lt_repr_repr; try representable.
          (* TODO deal with comparisons in a more automated way *)
          replace (m <? n) with false; last first.
          { symmetry; rewrite Z.ltb_ge; lia. }
          wp. iFrame.
      } iIntros "_ Hℓ".
      (* Done dealing with [EAssert]... *)
      wp.
      wp_store "Hℓ". prove_counter. }

    oSpecify "get" get_spec vget "#Hget" !.
    { iIntros "!>"(? nc) "(%ℓ&->&Hℓ)".
      call. wp_load "Hℓ". prove_counter. }

    oSpecify "Counter" Counter_spec vCounter "#?" !.
    { iModIntro. wp_prove_spec. }

    iModIntro; wp_prove_spec.
  Qed.

End ProofExamples.
