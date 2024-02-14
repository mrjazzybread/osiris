From osiris Require Import osiris.
From osiris.examples Require Import og_data.

(* -------------------------------------------------------------------------- *)

(* TODO UNUSED
(* Boilerplate: reflect the algebraic data type ['a arity0]. *)

Inductive arity0 : Type :=
| A0: arity0.

Definition encode_arity0 (a : arity0) : val :=
  match a with
  | A0 =>
      VConstant "A"
  end.

Local Instance Encode_arity0 : Encode arity0 :=
  { encode := encode_arity0 }.

Lemma encode_arity0_is_encode :
  ∀ (a : arity0),
  encode_arity0 a = #a.
Proof. eauto. Qed.

Local Hint Resolve encode_arity0_is_encode : encode.
 *)

(* -------------------------------------------------------------------------- *)

(* This program crashes. *)

Local Transparent structural_equality_error.

Lemma main η :
  simp (eval_mexpr η __main) crash.
Proof.
  simp.
Qed.
