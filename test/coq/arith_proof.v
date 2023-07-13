From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import arith.

(* -------------------------------------------------------------------------- *)

(* The current file is a sandbox to develop tactics on the specification of
   mutually recursive functions. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS Σ}.

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

(* TODO if we abstract the closure away as soon as we have stepped into it,
   then we do not need these notations. See [wp_enter_and_abstract]. *)

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

(* Set Ltac Profiling. *)

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
  ⊢ WP eval_mexpr η _Arith {{ module_spec Λ }}.
Proof.
  intros.

  wp until "add"!.
  oSpecify "add" add_spec vadd "#Hadd"
           "mult" mult_spec vmult "#Hmult".

  (* Specification of the addition. *)
  { iModIntro. iIntros(i1 H1).

      (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
      oCall "add" vadd "mult" vmult. wp. wp_continue.

      (* The proof can now continue as expected. *)
      iIntros(i2 H2). wp.
      wp_continue. (* TODO FIXME this does not terminate! *)
      assert (representable i2) by apply int_representable. (* TODO *)
      rewrite ->eq_repr_repr by representable.
      destruct (i2 =? 0)%Z eqn:E; wp.
      { (* [i2 = 0%Z] *)
        apply Z.eqb_eq in E as ->.
        wp_bind.
        wp_use "Hmult"; first done.
        iIntros (Hmult_part) "Hmult_part".
        iApply (wp_covariant with "[Hmult_part]").
        { iApply "Hmult_part"; done. }
        iIntros(?->).
        iPureIntro. equality. }
      { (* [i2 != 0%Z], goal: [1 + (add x (y - 1)) == x + y] *)
        wp_bind.
        wp_use "Hadd".
        { iPureIntro. lia. }
        iIntros (vpadd) "Hvpadd".
        wp_bind.
        iApply (wp_covariant with "[Hvpadd]").
        { wp_use "Hvpadd".
          iPureIntro. lia. }
        iIntros (?) "->".
        wp.
        iPureIntro. equality.
     }
  }

  (* ------------------------------------------------------------------ *)
  (* Specification of the multiplication. *)
  { iModIntro. iIntros (i1 H1).

    (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
    oCall "add" vadd "mult" vmult. wp_continue.

    (* The proof can now continue as expected. *)
    iIntros(i2 H2). wp. wp_continue.
    assert (representable i2) by apply int_representable.
    rewrite -> eq_repr_repr by representable.
    destruct (i2 =? 0)%Z eqn:E; wp.
    { (* [i2 = 0%Z]. *) iPureIntro; simpl; equality. }
    { (* [i2 != 0%Z]. *)
      rewrite -> eq_repr_repr by representable.
      destruct (i2 =? 1)%Z eqn:E1; wp.
      { (* [i2 = 1%Z]. *) iPureIntro; simpl; equality. }
      { (* [i2 <> 1%Z]. *)
        (* Proof that [add x (mult x (y - 1)) == x * y]. *)
        wp_par.
        { (* [λ y, add x y]. *)
          iSpecialize ("Hadd" $! i1 H1).
          wp_use "Hadd". }
        { wp_bind.
          (* [mult x (y - 1)] *)
          wp_use "Hmult".
          { iPureIntro. lia. }
          iIntros (vmult_part) "Hvmult_part".
          wp_use "Hvmult_part".
          iPureIntro. lia. }
        { iIntros (v1 v2) "Hv1 ->".
          wp.
          iApply (wp_covariant with "[Hv1]").
          { iApply "Hv1". iPureIntro. apply Ztac.mul_le; lia. }
          iIntros (?->).
          iPureIntro; equality. } } } }

  wp_par.
  { by wp_use "Hadd". }
  { wp_bind. wp_use "Hadd"; first done.
    iIntros (vadd_part) "Hadd_part"; wp; by wp_use "Hadd_part". }
  iIntros (vadd_part ?) "Hadd_part ->". wp.
  iSpecialize("Hadd_part" $! _ _).
  wp_bind.
  wp_use "Hadd_part".
  Unshelve. 2: lia. (* TODO avoid this *)
  iIntros (?->). wp. wp_bind.
  wp_continue.

  repeat wp_par.
  { wp_bind; wp_use "Hmult"; first done.
    iIntros (vmult_part) "Hmult_part".
    iSpecialize ("Hmult_part" $! _ _). wp. wp_bind.
    wp_use "Hmult_part".
    iIntros (?->).
    wp_use "Hadd"; first done. }
  { wp_use "Hadd"; first done. }
  { wp_use "Hmult"; first done. }
  { wp_bind. wp_use "Hadd"; first done.
    iIntros (vadd_part') "Hadd_part'".
    iSpecialize ("Hadd_part'" $! _ _).
    iApply (wp_covariant with "Hadd_part'"). (*TODO: fix [wp_use]. *)
    iIntros(?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1"). (* ditto. *)
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1"). (* ditto. *)
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    wp_bind. iApply (wp_covariant with "H1"). (* ditto. *)
    iIntros (?->). wp. wp_bind. wp_continue.

    wp_module_spec. }

  Unshelve. (* TODO avoid this *)
  all: done.
Time Qed.

(* Show Ltac Profile. *)
