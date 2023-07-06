From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test.records Require Import records records_code.

(* -------------------------------------------------------------------------- *)

(* Table of content of the file:
   1. Definition of an instance of [Encode] for the a Coq-type representing
      OCaml records of type [{ b: bool; i: int }].
   2. Definitions of values (of type [val]) representing OCaml values appearing
      in the proofs.
   3. Definitions of specifications for elements of the module.
   4. Proofs that each function body respects its specification
      (These are used in the caller-side-reasoning style proof below.)
   5. Proofs that each function respects its specification
      (These are used in the callee-side-reasoning style proof below.)
   6. Proof of the module (Caller-side reasoning).
   7. Proof of the module (Callee-side reasoning).
   8. Direct proof of the module (in one lemma).

Efficiency of 4--5: TODO.

Efficiency of 6--8: TODO. *)

(* -------------------------------------------------------------------------- *)

(* Make sure that the modules [Record] (defined in [records.v]) and
   [opacified_Records] (defined in [records_code.v]) coincide. *)
Goal opacified_Records = _Records.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

Local Transparent eval. (* TODO. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS_gen hlc Σ}.

(* -------------------------------------------------------------------------- *)

(* (1) Local defintion of the record type used in [records.ml]. *)

Record R :=
  { b: bool ;
    i: Z }.

Local Instance r_encode : Encode R :=
  { encode :=
    fun (r: R) =>
      VRecord $
              EnvCons "b" #(r.(b)) $
              EnvCons "i" #( r.(i)) $
              EnvNil }.

Lemma solve_encode_R b i vb vi :
  vb = #b →
  vi = #i →
  VRecord $
    EnvCons "b" vb $
    EnvCons "i" vi $
    EnvNil
  = #{| b := b; i := i |}.
Proof. intros. subst. reflexivity. Qed.

Local Hint Resolve solve_encode_R : encode.

(* TODO FIXME there is already an instance of [Encode nat] in encode.v *)
Fixpoint nat_encode_f (n : nat) : val :=
  match n with
  | O => VData "O" $ VTuple VNil
  | S n => VData "S" $ VTuple $ VCons (nat_encode_f n) VNil
  end.

Local Instance nat_encode : Encode nat :=
  { encode := nat_encode_f }.

(* -------------------------------------------------------------------------- *)

(* (2) Definition of some values; useful to write the specs below. *)
Definition enc_r_elt : val := #{| b := true; i := 10 |}.
Definition enc_r_elt' : val := #{|b := false; i := 10|}.
Definition enc_lily : val := # [enc_r_elt; enc_r_elt'].

(* -------------------------------------------------------------------------- *)

(* (3) Definition of specifications. *)

(* [is_equal] asserts the equality of two values. *)
Definition is_equal (v res: val) : iProp Σ :=
  □ ⌜ res = v ⌝.
  (* TODO persistence is redundant here *)
  (* TODO use Iris's RET notation instead of [is_equal] *)

(* [trivial_spec] is a dummy specification. *)
Definition trivial_spec (v: val) : iProp Σ :=
  □ emp.

(* [flip] negates [b] in records of type [{ b: bool; i: int}]. *)
Definition flip_spec (v : val) : iProp Σ :=
  □ ∀ (b: bool) (i: Z),
    WP call v #{| b := b; i := i |}
    {{ λ r, is_equal r #{| b := negb b; i := i |} }}.

(* [r_val_spec] performs a different arithmetic computation depending on the
   fiels [b] of a record. *)
Definition r_val_pure (r: R) : Z :=
  match r.(b) with
  | true => r.(i) * 2 - 1
  | false => r.(i)
  end.

Definition r_val_spec (r_val: val): iProp Σ :=
  □ ∀ (r: R),
  WP call r_val #r
     {{ λ result, is_equal result #(r_val_pure r) }}.

Definition sum_pure (r1 r2: R) : Z :=
  r_val_pure r1 + r_val_pure r2.
Definition sum_spec (vsum: val) : iProp Σ :=
  □ ∀ (r1 r2 : R),
    WP call vsum #r1 {{
          λ vpart,
          WP call vpart #r2 {{
                λ res,
                is_equal res # (sum_pure r1 r2) }} }}.

Fixpoint is_odd_pure (n: nat) :bool :=
  match n with
  | O => true
  | S n => negb (is_odd_pure n)
  end.

Definition is_odd_spec (vis_odd: val) : iProp Σ:=
  □ ∀ (n : nat),
  WP call vis_odd #n {{ is_equal #(is_odd_pure n) }}.

(* -------------------------------------------------------------------------- *)

(* Specification of the module. *)
Definition Λ :=
  [
    ("sum", sum_spec) ;
    ("r_val", r_val_spec) ;
    ("lily", is_equal enc_lily) ;
    ("flip", flip_spec) ;
    ("r_elt", is_equal enc_r_elt) ;
    ("is_odd'", is_odd_spec)
  ].

(* -------------------------------------------------------------------------- *)

(* TODO [wp_simp_using] should be unnecessary provided H is added to the
   hint database [simp_specs]. *)
Ltac wp_simp_using H :=
  iApply wp_simp; [ by apply H; try done | wp ].

Ltac wp_simp_eusing H :=
  iApply wp_simp; [ by eapply H; try done | wp ].



Lemma Records_spec :
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η _Records {{ module_spec Λ }}.
Proof.
  intros η.
  wp.
  simpl build. (* TODO *)
  wp_bind.
  wp.

  (* [r_elt] is a known value. *)
  wp_bind.
  wp_continue. wp_bind.

  (* [flip] has the expected spec. *)
  oSpecify "flip" flip_spec vflip "#Hflip".
  { iIntros "!>" (b i); wp.
    wp_continue.
    unfold sort. simpl build. (* TODO *)
    do 2 wp_bind. wp. equality. }
  wp_bind.

  (* [flip] is applied to [r_elt]. *)
  wp.
  (* TODO this kind of replacement should be done by letting the tactic
          [encode] solve a goal of the form [v = #?x]. *)
  (* TODO and this should be done automatically by the [wp_] tactics *)
  replace
    (VRecord (EnvCons "b" VTrue (EnvCons "i" (VInt (int.repr 10)) EnvNil)))
    with #{| b := true; i := 10 |}; last reflexivity.
  wp_use "Hflip".
  iIntros (? <-). wp_bind.

  (* [lily] has the expected value. *)
  wp_continue. wp_bind.


  (* TODO: uncomment the call to [List.rev]. *)

  (* [r_val] has the expected value. *)
  oSpecify "r_val" r_val_spec vr_val "#Hr_val".
  { iIntros "!>" ([[|] i]);
      wp; wp_bind; wp_continue; wp_bind; wp_continue; iPureIntro; equality. }
  wp_bind.

  (* [sum] is given the trivial spec for now. *)
  oSpecify "sum" sum_spec vsum "#Hsum".
  { iIntros "!>" ([b1 i1] [b2 i2]).
    wp.
    do 2 wp_continue.
    wp_par.
    { wp_bind.
      (* TODO avoid manual encoding *)
      change (VRecord (EnvCons "b" (VBool b1) $ EnvCons "i" (VInt (int.repr i1)) EnvNil))
      with (#{| b:=b1; i:= i1|}).
      wp_use "Hr_val". iIntros(?<-).
      wp_simp.
      iApply wp_ret.
      wp_set_postcondition. }
    { (* TODO avoid manual encoding *)
      change (VRecord (EnvCons "b" (VBool b2) $ EnvCons "i" (VInt (int.repr i2)) EnvNil))
      with (#{| b:=b2; i:= i2|}).
      wp_use "Hr_val". }
    { iIntros (v1 v2) "%Hadd <-". subst v1.
      wp. equality. }
  }

  wp_continue.
  wp_bind.

  (* [is_odd] is given the trivial spec for now. *)
  oSpecify "is_odd" trivial_spec vis_odd "#?"; first done.
  wp_bind.

  oSpecify "is_odd'" is_odd_spec vis_odd' "#His_odd'".
  { iIntros "!>" ([|]); wp_enter_and_abstract;
      iIntros (is_odd');
    wp_step; iNext; wp. (* FIXME: [wp] uses [wp_simp], thus eating laters. *)
    { wp_continue. equality. }
    { wp_continue.
      (* TODO manual encoding *)
      replace (nat_encode_f n) with #n; last reflexivity.
      iApply (wp_covariant with "His_odd'").
      iIntros (?->).
      destruct (is_odd_pure n) eqn:E; wp; equality. } }
  (* Every spec has been proven: [wp_module_spec] can finish the proof. *)
  wp_module_spec.
Time Qed.
