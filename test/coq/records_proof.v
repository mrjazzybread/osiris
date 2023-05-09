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
From test Require Import records.

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
  intros Λ η. wp.
  simpl (build _ _). wp.

  (* [r_elt] is a known value. *)
  wp_specify "r_elt" (is_equal enc_r_elt); first done.
  (* There is no need to keep the "spec" of [r_elt] around.*)
  iIntros (r_elt) "->". wp_continue.

  (* [flip] has teh expected spec. *)
  wp_specify "flip" flip_spec.
  { iIntros (v'). wp. wp_call.
    iIntros ([] i <-); wp; wp_call; simpl; wp; done. }
  iIntros (flip) "#Hflip". wp_continue.

  (* [flip] is applied to [r_elt]. *)
  wp_par; [ by wp_use "Hflip"
          | by wp_set_postcondition
          | ].
  iIntros (?? <- ->). wp.

  (* [lily] has teh expected value. *)
  wp_specify "lily" (is_equal enc_lily).
  { iPureIntro. reflexivity. }
  iIntros (lily) "#Hlily". wp_continue.


  (* TODO: uncomment the call to [List.rev]. *)

  (* [r_val] has the expected value. *)
  wp_specify "r_val" r_val_spec.
  { iIntros (r i [] ->).
    - wp_call. wp_continue. wp.
      iPureIntro. reflexivity.
    - wp_call. wp_continue.
      iPureIntro. reflexivity. }
  iIntros (r_val) "#Hr_val". wp_continue.


  (* [sum] is given the trivial spec for now. *)
  wp_specify "sum" trivial_spec; first done.
  iIntros (sum) "#Hsum". wp_continue.

  (* [is_odd_naive] is given the trivial spec for now. *)
  wp_specify "is_odd_naive" trivial_spec; first done.
  iIntros (is_odd_naive) "#His_odd_naive". wp_continue.

  (* [is_odd] is given the trivial spec for now. *)
  wp_specify "is_odd" trivial_spec; first done.
  iIntros (is_odd) "#His_odd". wp_continue.

  (* TODO: uncomment the calls to [sum] and [List.fold_left] *)

  (* Every spec has been proven: [wp_module_spec] can finish the proof. *)
  wp_module_spec.
Qed.
