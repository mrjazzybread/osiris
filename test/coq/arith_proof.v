From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import arith.

Local Transparent eval. (* TODO. *)

(* -------------------------------------------------------------------------- *)

(* The current file is a sandbox to develop tactics on the specification of
   mutually recursive functions. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS_gen hlc Σ}.

(* -------------------------------------------------------------------------- *)

(* Definition of the specifications. They have to be persistent for the tactics
   to work properly. *)

Definition add_spec vadd : iProp Σ :=
  □ (∀ (x : Z),
    ⌜0 <= x⌝%Z →
    WP call vadd #x
    {{ λ v,
        ∀ (y: Z),
          ⌜0 <= y⌝%Z →
        WP call v #y {{ λ res, ⌜res = #(x + y)%Z⌝ }} }}).

Definition mult_spec vmult : iProp Σ :=
  □ (∀ (x: Z),
    ⌜0 <= x⌝%Z →
    WP call vmult #x
       {{ λ v, ∀ (y: Z),
             ⌜0 <= y⌝%Z →
             WP call v #y {{ λ res, ⌜res = #(x * y)%Z⌝ }} }}).

Definition trivial_spec: val → iProp Σ := λ v, ⌜ True ⌝%I.
Definition is_equal `{Encode X} (e: X) : val → iProp Σ := λ v, ⌜v = #e⌝%I.

(* -------------------------------------------------------------------------- *)

(* As there is no proper notation for specifications of closures yet, I added
   the following for the goal to remain readable. *)

Local Notation "'Spec'  'of'  'the'  'addition.'" :=
  (add_spec _)
  (only printing).

Local Notation "'Spec'  'of'  'the'  'multiplication.'" :=
  (mult_spec _)
  (only printing).

(* -------------------------------------------------------------------------- *)

(* Whether or not integers are representable does not matter for now. *)
Axiom int_representable:
  forall (i: Z), (int.min_signed ≤ i ≤ int.max_signed)%Z.

(* The specification of [Add] will be proven several times. Each attempt should
   improve the proof --- especially the way to handle mutually recursive
   functions. *)

Lemma Add_spec :
    let Λ :=
    [
      ("add", add_spec);
      ("mult", mult_spec);
      ("i3", is_equal #3)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Arith {{ module_spec Λ }}.
Proof.
  intros. wp. do 2 wp_bind.

  o_specify "add" add_spec "#Hadd"
            "mult" mult_spec "#Hmult".

  (* Specification of the addition. *)
  { iModIntro. iIntros(i1 H1).

      (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
      oCall "add" vadd "mult" vmult. wp. wp_continue.

      (* The proof can now continue as expected. *)
      iIntros(i2 H2). wp. wp_continue.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      iIntros (veq_part) "Hspec_eq".
      wp. do 2 wp_bind.
      iApply (wp_covariant with "Hspec_eq"). (* TODO: fix [wp_use]. *)
      iIntros (? ->).
      destruct (i2 =? 0)%Z eqn:E; wp.
      { (* [i2 = 0%Z] *)
        apply Z.eqb_eq in E as ->.
        wp_use "Hmult"; first done.
        iIntros (Hmult_part) "Hmult_part".
        iApply (wp_covariant with "[Hmult_part]").
        { iApply "Hmult_part"; done. }
        iIntros(?->).
        iPureIntro. do 2 f_equal. lia. }
      { (* [i2 != 0%Z], goal: [1 + (add x (y - 1)) == x + y] *)
        wp_par.
        { (* [λ y, 1 + y] *) iIntros (vpartial) "H". iExact "H". }
        { (* [add x (y - 1)]. *)
          wp_par.
          { wp_use "Hadd"; iPureIntro; exact H1. }
          - wp_call.
            by instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I); encode.
          - iIntros (vpadd ?) "Hadd_partial ->".
            wp_use "Hadd_partial".
            iPureIntro. lia. }
        { iIntros (vadd1 ?) "Hadd1 ->".
          wp.
          iSpecialize ("Hadd1" $! (i1 + (i2 - 1))%Z NotStuck top). wp.
          iApply (wp_covariant with "Hadd1").
          iIntros (?->).
          iPureIntro. do 2 f_equal. lia. } } }

  (* ------------------------------------------------------------------ *)
  (* Specification of the multiplication. *)
  { iModIntro. iIntros (i1 H1).

    (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
    oCall "add" vadd "mult" vmult. wp_continue.

    (* The proof can now continue as expected. *)
    iIntros(i2 H2). wp. wp_continue.
    wp_use Stdlib__eq__spec; try done; try apply int_representable.
    iIntros (veq_part) "Heq_part".
    wp. do 2 wp_bind. iApply (wp_covariant with "Heq_part").
    iIntros (?->).
    destruct (i2 =? 0)%Z eqn:E.
    { (* [i2 = 0%Z]. *) wp.
      apply Z.eqb_eq in E as ->. iPureIntro. do 2 f_equal. lia. }
    { (* [i2 != 0%Z]. *) wp.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      clear veq_part.
      iIntros (veq_part) "Heq_part".
      wp. do 2 wp_bind. iApply (wp_covariant with "Heq_part").
      iIntros (?->).
      destruct (i2 =? 1)%Z eqn:E1.
      { (* [i2 = 1%Z]. *) wp.
        apply Z.eqb_eq in E1 as ->. iPureIntro. do 2 f_equal. lia. }
      { (* [i2 <> 1%Z]. *) wp.
        (* Proof that [add x (mult x (y - 1)) == x * y]. *)
        wp_par.
        { (* [λ y, add x y]. *)
          iSpecialize ("Hadd" $! i1 H1).
          wp_use "Hadd". }
        { (* [mult x (y - 1)] *)
          wp_par.
          { (* [λ y, mult x y]. *)
            wp_use "Hmult"; iPureIntro; exact H1. }
          { (* [y - 1]. *) wp_call.
            by instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I); encode. }
          { iIntros (vmult_part ?) "Hmult_part ->".
            wp. wp_use "Hmult_part".
            iPureIntro. lia. } }
        { (* Finish the application of [add]. *)
          iIntros (vadd_part ?) "Hadd_part ->".
          wp.
          unshelve iSpecialize ("Hadd_part" $! (i1 * (i2 - 1))%Z _).
          { apply Ztac.mul_le; lia. }
          iApply (wp_covariant with "Hadd_part").
          iIntros (?->).
          iPureIntro. do 2 f_equal.
          lia. } } } }

  wp_par.
  { by wp_use "Hadd". }
  { wp_bind. wp_use "Hadd"; first done.
    iIntros (vadd_part) "Hadd_part"; wp; by iApply "Hadd_part". }
  iIntros (vadd_part ?) "Hadd_part ->". wp.
  iSpecialize("Hadd_part" $! _ _).
  iApply (wp_covariant with "Hadd_part").
  Unshelve. 2: lia.
  iIntros (?->). wp. wp_bind.
  wp_continue.

  repeat wp_par.
  { wp_bind; wp_use "Hmult"; first done.
    iIntros (vmult_part) "Hmult_part".
    iSpecialize ("Hmult_part" $! _ _). wp. wp_bind.
    iApply (wp_covariant with "Hmult_part").
    iIntros (?->).
    wp_use "Hadd"; first done. }
  { wp_use "Hadd"; first done. }
  { wp_use "Hmult"; first done. }
  { wp_bind. wp_use "Hadd"; first done.
    iIntros (vadd_part') "Hadd_part'".
    iSpecialize ("Hadd_part'" $! _ _).
    iApply (wp_covariant with "Hadd_part'").
    iIntros(?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). wp. wp_bind. wp_continue.

    wp_module_spec. }

  Unshelve.
  all: done.
Time Qed.
(* This [Qed.] is about 2.8s, while it was 2.0s with a manual iAssert.
   TODO: improve the lemma applied by [oSpecify] to get better results! *)
