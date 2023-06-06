From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import records.

Local Transparent eval. (* TODO. *)

Context `{!osirisGS_gen hlc Σ}.

Definition enc_r_elt : val :=
  VRecord $
          EnvCons "b" (encode true) $
          EnvCons "i" (encode 10) $
          EnvNil.
Definition enc_r_elt' : val :=
  VRecord $
          EnvCons "b" (encode false) $
          EnvCons "i" (encode 10) $
          EnvNil.

Definition enc_lily : val := # [enc_r_elt; enc_r_elt'].

Definition is_equal v : val → iProp Σ :=
  λ res, ⌜ res = v ⌝%I.

Definition flip_spec (v : val) : iProp Σ :=
  ∀ (v': val) (b: bool) (i: Z),
    is_equal v' (VRecord $
                         EnvCons "b" (encode b) $
                         EnvCons "i" (encode i) $
                         EnvNil) -∗
    WP call v v'
    {{ λ r, is_equal r (VRecord $
                                EnvCons "b" (encode (negb b)) $
                                EnvCons "i" (encode i) $
                                EnvNil) }}.

Definition r_val_spec (r_val: val): iProp Σ :=
  ∀ (r: val) (i: Z) (b: bool),
    ⌜ r = VRecord $
                  EnvCons "b" #b $
                  EnvCons "i" #i $
                  EnvNil ⌝ →
    WP call r_val r {{ λ result,
    match b with
    | true => ⌜ result = #(i * 2 - 1)%Z ⌝
    | false => ⌜ result = # i ⌝
    end }}.

Definition trivial_spec (v: val) : iProp Σ :=
  ⌜ True ⌝.

Lemma Records_spec :
    let Λ :=
      [
        ("is_odd", trivial_spec) ;
        ("is_odd_naive", trivial_spec) ;
        ("sum", trivial_spec) ;
        ("r_val", r_val_spec) ;
        ("lily", is_equal enc_lily) ;
        ("flip", flip_spec) ;
        ("r_elt", is_equal enc_r_elt)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Records {{ module_spec Λ }}.
Proof.
Admitted.
