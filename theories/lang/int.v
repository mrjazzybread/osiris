From osiris.CompCert Require Import Coqlib Integers.
Open Scope Z_scope.

(* This file defines the type [int], a model of the OCaml type [int],
   the type of machine integers. *)

(* -------------------------------------------------------------------------- *)

(* Technical lemmas about integer arithmetic. *)

Lemma half_of_double x :
  (2 * x) / 2 = x.
Proof.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma two_power_nat_mono i j :
  (i <= j)%nat ->
  two_power_nat i <= two_power_nat j.
Proof.
  intros.
  rewrite !two_power_nat_equiv.
  apply Z.pow_le_mono_r; lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Integers in OCaml have an unspecified size. The manual explicitly states
   that it can be 31, 32, or 63, and does not rule out other values. *)

(* We assume that the size of integers is at least 31. *)

(* This constant corresponds to [Sys.int_size] in OCaml. *)

Parameter int_size : nat.

Parameter int_size_ge_31 :
  (31 <= int_size)%nat.

Lemma int_size_not_zero: (int_size <> 0)%nat.
Proof. pose proof int_size_ge_31. lia. Qed.

(* -------------------------------------------------------------------------- *)

(* We write [w] for [int_size - 1]. *)

Definition w : nat :=
  (int_size - 1)%nat.

Lemma int_size_eq_succ_w :
  int_size = S w.
Proof.
  unfold w. pose proof int_size_not_zero. lia.
Qed.

Lemma w_ge_30 :
  (30 <= w)%nat.
Proof.
  pose proof int_size_ge_31. pose proof int_size_eq_succ_w. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The functor [Integers.Make] is instantiated with [int_size]. *)

Module Intsize.
  Definition wordsize := int_size.
  Lemma wordsize_not_zero: (wordsize <> 0)%nat.
  Proof. exact int_size_not_zero. Qed.
End Intsize.

Include Make(Intsize).

Lemma wordsize_is_int_size :
  wordsize = int_size.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

(* OCaml integers are signed. *)

(* The representable integers are comprised between [min_signed] and
   [max_signed], inclusive. *)

Global Notation representable i :=
  (min_signed <= i <= max_signed).

(* The function [signed : int -> Z] maps a machine integer to the
   ideal integer that it represents. *)

(* The function [repr : Z -> int] maps an ideal integer to the machine
   integer that represents it, if there is one. *)

(* The type [int] is internally defined as a subset of Z, which
   corresponds to the interval of the unsigned integers, from 0
   to [2^wordsize-1]. This can be confusing, so it is preferable
   not to think about it, as far as possible. Just view [int] as
   an abstract type. *)

(* The following properties hold: *)

Goal forall i : int, representable (signed i).
Proof. apply signed_range. Qed.

Goal forall i : int, repr (signed i) = i.
Proof. apply repr_signed. Qed.

Goal forall z : Z, representable z -> signed (repr z) = z.
Proof. apply signed_repr. Qed.

(* [min_signed] is [-2^w]. *)

Lemma min_signed_eq :
  min_signed = -(two_power_nat w).
Proof.
  unfold min_signed, half_modulus, modulus.
  rewrite wordsize_is_int_size.
  rewrite int_size_eq_succ_w.
  rewrite (two_power_nat_S w).
  rewrite half_of_double.
  reflexivity.
Qed.

(* [max_signed] is [2^w-1]. *)

Lemma max_signed_eq :
  max_signed = two_power_nat w - 1.
Proof.
  unfold max_signed, half_modulus, modulus.
  rewrite wordsize_is_int_size.
  rewrite int_size_eq_succ_w.
  rewrite (two_power_nat_S w).
  rewrite half_of_double.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following facts are the specifications of the operations on machine
   integers that are of interest to us. *)

(* It is worth noting that negation, addition, subtraction, multiplication
   have no proof obligation. There is no need to prove that the arguments
   or result of the operation are representable. *)

Goal forall z, neg (repr z) = repr (-z).
Proof. apply neg_repr. Qed.

Goal forall z1 z2, add (repr z1) (repr z2) = repr (z1 + z2).
Proof. apply add_repr_repr. Qed.

Goal forall z1 z2, sub (repr z1) (repr z2) = repr (z1 - z2).
Proof. apply sub_repr_repr. Qed.

Goal forall z1 z2, mul (repr z1) (repr z2) = repr (z1 * z2).
Proof. apply mul_repr_repr. Qed.

Goal
  forall z1 z2,
  representable z1 -> representable z2 ->
  divs (repr z1) (repr z2) = repr (z1 ÷ z2).
Proof. apply divs_repr_repr. Qed.

Goal
  forall z1 z2,
  representable z1 -> representable z2 ->
  mods (repr z1) (repr z2) = repr (Z.rem z1 z2).
Proof. apply mods_repr_repr. Qed.

Goal
  forall z1 z2,
  representable z1 -> representable z2 ->
  eq (repr z1) (repr z2) = (z1 =? z2).
Proof. apply eq_repr_repr. Qed.

Goal
  forall z1 z2,
  representable z1 -> representable z2 ->
  lt (repr z1) (repr z2) = (z1 <? z2).
Proof. apply lt_repr_repr. Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas and tactics are intended to help prove that certain
   numbers are representable. *)

Lemma prove_representable_30 i :
  -(two_power_nat 30) <= i < two_power_nat 30 ->
  representable i.
Proof.
  rewrite min_signed_eq, max_signed_eq.
  assert (two_power_nat 30 <= two_power_nat w)
    by auto using two_power_nat_mono, w_ge_30.
  lia.
Qed.

Ltac prove_representable_30 :=
  apply prove_representable_30; cbv; split; congruence.

Goal representable 1673.
Proof.
  prove_representable_30.
Qed.

Goal representable (-512348).
Proof.
  prove_representable_30.
Qed.
