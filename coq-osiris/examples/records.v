From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_records.

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS Σ}.

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

(* -------------------------------------------------------------------------- *)

(* Specification of the module. *)
Definition Λ :=
  [
    ("sum", sum_spec) ;
    ("r_val", r_val_spec) ;
    ("lily", is_equal enc_lily) ;
    ("flip", flip_spec) ;
    ("r_elt", is_equal enc_r_elt)
  ].

(* -------------------------------------------------------------------------- *)

(* TODO [wp_simp_using] should be unnecessary provided H is added to the
   hint database [simp_specs]. *)
Ltac wp_simp_using H :=
  iApply wp_simp; [ by apply H; try done | wp ].

Ltac wp_simp_eusing H :=
  iApply wp_simp; [ by eapply H; try done | wp ].

Lemma Records_spec :
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  ⊢ WP eval_mexpr η __main {{ module_spec Λ }}.
Proof.
  intros η.
  wp.
  (* TODO something is wrong here: we already have [fix build] in the goal *)
  simpl.
  wp.

  (* [r_elt] is a known value. *)
  wp_continue. wp_bind.

  (* [flip] has the expected spec. *)
  oSpecify "flip" flip_spec vflip "#Hflip".
  { iIntros "!>" (b i); wp.
    simpl. (* TODO *)
    wp. equality. }
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
      wp; wp_bind; wp_continue; iPureIntro; equality. }
  wp_bind.

  (* [sum] is given the trivial spec for now. *)
  oSpecify "sum" sum_spec vsum "#Hsum".
  { iIntros "!>" ([b1 i1] [b2 i2]).
    wp.
    wp_par.
    { wp_bind.
      (* TODO avoid manual encoding *)
      change (VRecord (EnvCons "b" (VBool b1) $ EnvCons "i" (VInt (int.repr i1)) EnvNil))
      with (#{| b:=b1; i:= i1|}).
      wp_use "Hr_val". iIntros(?<-).
      wp_simp.
      iApply wp_ret.
      wp_set_postcondition. }
    { wp_bind.
      (* TODO avoid manual encoding *)
      change (VRecord (EnvCons "b" (VBool b2) $ EnvCons "i" (VInt (int.repr i2)) EnvNil))
      with (#{| b:=b2; i:= i2|}).
      wp_use "Hr_val".
      (* TODO ugly... *)
      iIntros (a) "%Ha". subst a. simpl val_as_int.
      iApply wp_ret. wp_set_postcondition.
    }
    { iIntros (v1 v2) "%Hv1 %Hv2". subst v1 v2.
      wp. equality. }
  }

  (* Every spec has been proven: [wp_module_spec] can finish the proof. *)
  wp_module_spec.
Time Qed.
