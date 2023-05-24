From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics evalprime. (* TODO *)
From osiris.proofmode Require Import proofmode.

(* -------------------------------------------------------------------------- *)

(* An example algebraic data type. *)

Inductive data := A | B.

Global Instance encode_data : Encode data := {
  encode := λ data,
  match data with
  | A => VData "A" VUnit
  | B => VData "B" VUnit
  end
}.

(* -------------------------------------------------------------------------- *)

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet1Var "x" (EPair (EConstant "A") (EConstant "B")) $
  ELet1 (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal simp (eval EnvNil example) (ret (encode A)).
Proof.
  simp.
  simp_continue.
  (* TODO why is [simp_continue] needed just once and not twice? *)
Qed.

(* TODO Port other examples from examples_wp.v *)
