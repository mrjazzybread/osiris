From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics notations.
From osiris.libs Require Import Stdlib.
From test Require Import arith.

Context `{!osirisGS_gen hlc Σ}.

Definition add_spec vadd : iProp Σ :=
  ∀ (x y: Z) (vx vy: val),
    ⌜ vx = encode x ⌝ -∗
    ⌜ vy = encode y ⌝ -∗
    WP call vadd vx
    {{ λ v, WP call v vy {{ λ res, ⌜res = encode (x + y)%Z⌝ }} }}.

Definition mult_spec vmult : iProp Σ :=
  ∀ (x: Z),
    WP call vmult (encode x)
    {{ λ v, ∀ (y: Z),
        ⌜ (int.min_signed ≤ x ≤ int.max_signed)%Z⌝ -∗
        ⌜ (int.min_signed ≤ y ≤ int.max_signed)%Z⌝ -∗
        WP call v (encode y) {{ λ res, ⌜res = encode (x * y)%Z⌝ }} }}.

Lemma Add_spec :
    let Λ :=
    [
      ("add", add_spec)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Arith {{ module_spec Λ }}.
Proof.
  intros.
  wp.

  wp_specify "add" add_spec.
  { iIntros (x y ??->->).
    wp_call.
    do 3 wp_continue.

    wp.
    do 2 wp_continue.

    wp_par; [ by iApply Stdlib__add__spec
            | by iApply Stdlib__add__spec | ].
    iNext. iIntros (v1 v2) "H1 ->".
    wp_use "H1". }
  iIntros (v) "#add_spec"; wp_continue.

  wp_specify "mult" mult_spec.
  { iLöb as "IH".
    iIntros (x).
    wp_call.
    iIntros (y Hx Hy).
    wp.
    iApply wp_covariant.
    { iPoseProof (Stdlib__eq__spec
                    NotStuck top
                    (encode y))
        as "H".
      4: instantiate (2 := 0%Z).
      1, 2: exact eq_refl.
      1: assumption.
      1: { apply int.prove_representable_30.
           by vm_compute. }
      replace (VInt (int.repr y)) with (encode y); last reflexivity.
      iExact "H". }
    iIntros (vpartial) "Hpartial". wp.
    iApply (wp_covariant with "Hpartial").
    iIntros (vres->).
    destruct (decide (y = 0)) as [-> | Hneq%Z.eqb_neq].
    { (* y = 0 *)
      simpl; wp.
      iPureIntro.
      do 2 f_equal. lia. }
    { (* y <> 0 *)
      rewrite Hneq. wp.
      iPoseProof Stdlib__lt__spec as "Hpartial".
      2 : instantiate (2 := encode 0%Z).
      1: instantiate (2 := encode y).
      1,2 : exact eq_refl.
      2: { apply int.prove_representable_30.
           by vm_compute. }
      1: assumption.
      iApply (wp_covariant with "Hpartial").
      iIntros (vpartial') "Hpartial'".
      wp. iApply (wp_covariant with "Hpartial'").
      iIntros(?->).

      destruct (decide (y < 0)%Z) as [ ->%Z.ltb_lt | n ].
      { (* y < 0 *)
        wp.
        wp_par.
        2: { iPoseProof (Stdlib__neg__spec) as "H".
             1: reflexivity.
             iExact "H". }
        2: { iNext. iIntros (? ?) "Hpartial' ->".
             wp. iExact "Hpartial'". }
        { iSpecialize ("IH" $! x).
          iApply (wp_covariant with "IH").
          iIntros (?) "H".
          iSpecialize ("H" $! (-y)%Z with "[//][]").
          { (* Prove that -y is reprensentable *) admit. }
          iApply (wp_covariant with "H").
          iIntros (?->).
          iPoseProof Stdlib__neg__spec as "Hneg"; first reflexivity.
          iApply (wp_covariant with "Hneg").
          iIntros (?->).
          iPureIntro.
          unfold encode, Encode_Z.
          do 2 f_equal.
          lia. } }
      { (* y >= 0 *)
        apply Z.ltb_nlt in n; rewrite n. wp.
        iIntros ([]); wp.
        { (* version without the assertion. *)
          (* Code: [x + x * (mult x (y -1))]
             The tree of [Par] is as follows :
             Par
               (λ y, x + y) as [ Par [ret _] [ret _] ]
               (Par
                  (λ y, x * y) as [ Par [ret _] [ret _] ]
                  (Par
                     (λ y, mult x y)
                     (y - 1))) *)

          wp_par;
            [ (* [Stdlib__add__spec] is enough to prove the spec of  λ y, x + y *)
              by iApply Stdlib__add__spec
            | wp_par;
              [ (*1: spec of [λ y, mult x y] *)
              | (*2: spec of [y - 1] *)
              | (* ... *)]
            | (*3: proof of [ x * y = x + x * (y - 1)] *)].
          { wp. (* spec of [mult #x] *)
            instantiate
              (1 :=
                 λ (v: val),
                 (∀ (y: Z),
                     ⌜ (int.min_signed ≤ x ≤ int.max_signed)%Z⌝ -∗
                     ⌜ (int.min_signed ≤ y ≤ int.max_signed)%Z⌝ -∗
                     WP call v (encode y)
                        {{ λ res, ⌜res = encode (x * y)%Z⌝ }} )%I).
            iSpecialize ("IH" $! x).
            iApply (wp_covariant with "IH").
            iIntros (?) "?". iAssumption. }
          { (* spec of [y - 1] *)
            instantiate (1 := λ v, ⌜v = encode (y-1)%Z⌝%I ).
            by wp. }
          { (* spec of [mult x (y-1)] *)
            iNext. iIntros (v1 v2) "H1 ->".
            wp.
            instantiate (1 := λ (v: val), ⌜ v = encode (x * (y - 1))%Z ⌝%I ).
            iApply "H1"; try done.

            (* Proof that y-1 is representable. *) admit. }

          { iNext. iIntros (v1 v2) "H1 ->".
            wp.
            iApply (wp_covariant with "H1").
            iIntros (?->).
            iPureIntro; do 2 f_equal. lia. } }

        { (* version with the assertion *) admit. } } } }
  iIntros (vmult) "#mult_spec"; wp_continue.

  (* All expected specifications have already been proven. *)
  wp_module_spec.
Admitted.
