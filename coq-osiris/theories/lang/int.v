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

Definition zintsize := Z.of_nat int_size.

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

(* We do not include [M] because we prefer to control what we export. *)
Module M := Make(Intsize).

Definition wordsize := M.wordsize.

Lemma wordsize_is_int_size :
  M.wordsize = int_size.
Proof. reflexivity. Qed.

Definition min_signed := M.min_signed.
Definition max_signed := M.max_signed.
Definition max_unsigned := M.max_unsigned.

(* -------------------------------------------------------------------------- *)

(* OCaml integers are signed. *)

(* The representable integers are comprised between [min_signed] and
   [max_signed], inclusive. *)

Definition representable i :=
  (min_signed <= i <= max_signed).

(* Should someone wish to work with unsigned integers, then the
   representable integers would be those comprised between [0]
   and [max_unsigned], inclusive. Working with unsigned integers
   is not encouraged in OCaml, but is possible in principle,
   with much care. *)

Definition urepresentable i :=
  (0 <= i <= max_unsigned).

(* The function [signed : int -> Z] maps a machine integer to the
   ideal integer that it represents. *)
Definition signed := M.signed.

(* The function [repr : Z -> int] maps an ideal integer to the machine
   integer that represents it, if there is one. *)
Definition repr := M.repr.
Definition zero := repr 0.
Definition one  := repr 1.

(* The type [int] is internally defined as a subset of Z, which
   corresponds to the interval of the unsigned integers, from 0
   to [2^wordsize-1]. This can be confusing, so it is preferable
   not to think about it, as far as possible. Just view [int] as
   an abstract type. *)
Definition int := M.int.

(* The following properties hold: *)

Lemma signed_range : forall i : int, representable (signed i).
Proof. apply M.signed_range. Qed.

Lemma repr_signed : forall i : int, repr (signed i) = i.
Proof. apply M.repr_signed. Qed.

Lemma signed_repr : forall z : Z, representable z -> signed (repr z) = z.
Proof. apply M.signed_repr. Qed.

(* [min_signed] is [-2^w]. *)

Lemma min_signed_eq :
  min_signed = -(two_power_nat w).
Proof.
  unfold min_signed, M.min_signed, M.half_modulus, M.modulus.
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
  unfold max_signed, M.max_signed, M.half_modulus, M.modulus.
  rewrite wordsize_is_int_size.
  rewrite int_size_eq_succ_w.
  rewrite (two_power_nat_S w).
  rewrite half_of_double.
  reflexivity.
Qed.

(* [max_unsigned] is [2^int_size-1]. *)

Lemma max_unsigned_eq :
  max_unsigned = two_power_nat int_size - 1.
Proof. reflexivity. (* ah! *) Qed.

(* -------------------------------------------------------------------------- *)

(* The following facts are the specifications of the operations on machine
   integers that are of interest to us. *)

(* It is worth noting that negation, addition, subtraction, multiplication
   have no proof obligation. There is no need to prove that the arguments
   or result of the operation are representable. The same is true of the
   logical operations [lnot], [land], [lor], [lxor]. *)

(* In OCaml, the logical operations [lsl], [lsr], and [asr] require their
   second operand [z2] to satisfy [0 <= z2 <= zintsize]. *)

(* [lsl] places no constraint on its first argument. [lsr] requires its
   first argument [z1] to inhabit the interval of the representable unsigned
   integers, that is, to satisfy the constraint [0 <= z1 <= max_unsigned].
   [asr] requires [z1] to inhabit the interval of the representable signed
   integers, that is, to satisfy the constraint [representable z1]. *)

Definition neg  := M.neg.
Definition add  := M.add.
Definition sub  := M.sub.
Definition mul  := M.mul.
Definition divs := M.divs.
Definition mods := M.mods.
Definition eq   := M.eq.
Definition lt   := M.lt.

Definition lnot := M.not.
Definition land := M.and.
Definition lor  := M.or.
Definition lxor := M.xor.
Definition lsl  := M.shl.
Definition lsr  := M.shru. (* inserts zeroes *)
Definition asr  := M.shr.  (* inserts the sign bit of its first operand *)

Lemma neg_repr : forall z, neg (repr z) = repr (-z).
Proof. apply M.neg_repr. Qed.

Lemma add_repr_repr : forall z1 z2, add (repr z1) (repr z2) = repr (z1 + z2).
Proof. apply M.add_repr_repr. Qed.

Lemma sub_repr_repr : forall z1 z2, sub (repr z1) (repr z2) = repr (z1 - z2).
Proof. apply M.sub_repr_repr. Qed.

Lemma mul_repr_repr : forall z1 z2, mul (repr z1) (repr z2) = repr (z1 * z2).
Proof. apply M.mul_repr_repr. Qed.

Lemma divs_repr_repr:
  forall z1 z2,
  representable z1 -> representable z2 ->
  divs (repr z1) (repr z2) = repr (z1 ÷ z2).
Proof. apply M.divs_repr_repr. Qed.

Lemma mods_repr_repr :
  forall z1 z2,
  representable z1 -> representable z2 ->
  mods (repr z1) (repr z2) = repr (Z.rem z1 z2).
Proof. apply M.mods_repr_repr. Qed.

Lemma eq_repr_repr :
  forall z1 z2,
  representable z1 -> representable z2 ->
  eq (repr z1) (repr z2) = (z1 =? z2).
Proof. apply M.eq_repr_repr. Qed.

Lemma eq_repr_repr_unsigned :
  forall z1 z2,
  urepresentable z1 -> urepresentable z2 ->
  eq (repr z1) (repr z2) = (z1 =? z2).
Proof. apply M.eq_repr_repr_unsigned. Qed.

Lemma lt_repr_repr :
  forall z1 z2,
  representable z1 -> representable z2 ->
  lt (repr z1) (repr z2) = (z1 <? z2).
Proof. apply M.lt_repr_repr. Qed.

Lemma not_repr :
  forall z,
  lnot (repr z) = repr (Z.lnot z).
Proof. apply M.not_repr. Qed.

Lemma and_repr_repr :
  forall z1 z2,
  land (repr z1) (repr z2) = repr (Z.land z1 z2).
Proof. apply M.and_repr_repr. Qed.

Lemma or_repr_repr :
  forall z1 z2,
  lor (repr z1) (repr z2) = repr (Z.lor z1 z2).
Proof. apply M.or_repr_repr. Qed.

Lemma xor_repr_repr :
  forall z1 z2,
  lxor (repr z1) (repr z2) = repr (Z.lxor z1 z2).
Proof. apply M.xor_repr_repr. Qed.

Lemma lsl_repr_repr :
  forall z1 z2,
  0 <= z2 <= zintsize ->
  lsl (repr z1) (repr z2) = repr (Z.shiftl z1 z2).
Proof. apply M.shl_repr_repr. Qed.

Lemma lsr_repr_repr :
  forall z1 z2,
  0 <= z1 <= max_unsigned ->
  0 <= z2 <= zintsize ->
  lsr (repr z1) (repr z2) = repr (Z.shiftr z1 z2).
Proof. apply M.shru_repr_repr. Qed.

Lemma asr_repr_repr :
  forall z1 z2,
  min_signed <= z1 <= max_signed ->
  0 <= z2 <= zintsize ->
  asr (repr z1) (repr z2) = repr (Z.shiftr z1 z2).
Proof. apply M.shr_repr_repr. Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas and tactics are intended to help prove that certain
   numbers are representable. *)

Lemma prove_representable_30 i :
  -(two_power_nat 30) <= i < two_power_nat 30 ->
  representable i.
Proof.
  unfold representable.
  rewrite min_signed_eq, max_signed_eq.
  assert (two_power_nat 30 <= two_power_nat w)
    by auto using two_power_nat_mono, w_ge_30.
  lia.
Qed.

Ltac prove_representable_30 :=
  apply prove_representable_30; cbv; split; congruence.
Ltac prove_representable_30' :=
  apply prove_representable_30; rewrite two_power_nat_equiv; lia.
(* TODO should we use [two_power_nat_equiv] and write (2^30)%Z ? *)
(* TODO eliminate the redundancy between these tactics;
        use a single tactic and make it more robust;
        it should either succeed or fail quickly. *)

Goal representable 1673.
Proof.
  prove_representable_30.
Qed.

Goal representable (-512348).
Proof.
  prove_representable_30.
Qed.

Ltac representable :=
  try solve [ tauto | eauto 2 | prove_representable_30'| prove_representable_30 ].

Global Hint Extern 1 (representable _) => representable : representable.

(* -------------------------------------------------------------------------- *)

(* Opacity. *)

Global Opaque
  signed
  repr
  neg
  add
  sub
  mul
  divs
  mods
  eq
  lt
  lnot
  land
  lor
  lxor
  lsl
  lsr
  asr
.
