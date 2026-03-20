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

Lemma zwordsize_is_zintsize:
  M.zwordsize = zintsize.
Proof. reflexivity. Qed.

Definition min_signed := M.min_signed.
Definition max_signed := M.max_signed.
Definition max_unsigned := M.max_unsigned.

(* This constant corresponds to [Sys.max_array_length] in OCaml. *)

Parameter max_array : Z.
Parameter max_array_positive : (0 < max_array).
Parameter max_array_length : (max_array < max_signed).

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

(* [in_shift_range i] means that the integer [i] is an acceptable
   second operand to the shift operators [lsl], [lsr], and [asr]. *)

Definition in_shift_range i :=
  0 <= i <= zintsize.

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

(* Definitions of the operations on machine integers that exist in OCaml. *)

(* [ne] is not needed, because it is defined in terms of [eq]. *)

(* Similarly, [gt], [le], [ge] are defined in terms of [lt]. *)

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

(* -------------------------------------------------------------------------- *)

(* The following facts are the specifications of the operations on machine
   integers that are of interest to us. *)

(* In OCaml, machine integers are usually understood as signed integers. In
   accordance with this convention, several operations require their
   operand(s) to be representable, that is, to inhabit the interval of the
   signed integers. However, some operations require their operand(s) to be
   representable as an unsigned integer. Some operations require one or the
   other. Finally, some operations have no requirement at all. *)

(* [neg], [add], [sub], [mul], [lnot], [land], [lor], [lxor] have no
   precondition. There is no need to prove that the arguments or result of
   the operation are representable. This is convenient, and implies that
   these operations work both with signed and unsigned integers. *)

(* [divs] and [mods] require (signed) representable integers. *)

(* The logical operations [lsl], [lsr], and [asr] require their second
   operand [z2] to satisfy [0 <= z2 <= zintsize]. This is perhaps more
   restrictive than necessary, but this requirement appears in the OCaml
   reference manual. *)

(* [lsl] places no constraint on its first argument. [lsr] requires its
   first argument [z1] to be representable as an unsigned integer. [asr]
   requires [z1] to be representable in the usual sense, that is, as a
   signed integer. *)

(* [eq] requires its arguments to be either both representable as signed
   integers or both representable as unsigned integers. Thus, it works both
   with signed and with unsigned integers, but one must know which. *)

(* [lt] requires its arguments to be representable as signed integers.
   OCaml does not offer unsigned integer comparison operators. *)

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

Lemma lnot_repr :
  forall z,
  lnot (repr z) = repr (Z.lnot z).
Proof. apply M.not_repr. Qed.

Lemma land_repr_repr :
  forall z1 z2,
  land (repr z1) (repr z2) = repr (Z.land z1 z2).
Proof. apply M.and_repr_repr. Qed.

Lemma lor_repr_repr :
  forall z1 z2,
  lor (repr z1) (repr z2) = repr (Z.lor z1 z2).
Proof. apply M.or_repr_repr. Qed.

Lemma lxor_repr_repr :
  forall z1 z2,
  lxor (repr z1) (repr z2) = repr (Z.lxor z1 z2).
Proof. apply M.xor_repr_repr. Qed.

Lemma lsl_repr_repr :
  forall z1 z2,
  in_shift_range z2 ->
  lsl (repr z1) (repr z2) = repr (Z.shiftl z1 z2).
Proof. apply M.shl_repr_repr. Qed.

Lemma lsr_repr_repr :
  forall z1 z2,
  urepresentable z1 ->
  in_shift_range z2 ->
  lsr (repr z1) (repr z2) = repr (Z.shiftr z1 z2).
Proof. apply M.shru_repr_repr. Qed.

Lemma asr_repr_repr :
  forall z1 z2,
  representable z1 ->
  in_shift_range z2 ->
  asr (repr z1) (repr z2) = repr (Z.shiftr z1 z2).
Proof. apply M.shr_repr_repr. Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas and tactics are intended to help prove that certain
   numbers are representable. *)

Lemma array_size_representable i :
  0 <= i <= max_array ->
  representable i.
Proof.
  intros (Hpos & Hle).
  constructor.
  - rewrite min_signed_eq.
    transitivity 0; auto.
    apply Z.opp_nonpos_nonneg. apply Z.lt_le_incl, Z.gt_lt.
    apply Coqlib.two_power_nat_pos.
  - transitivity (max_array); auto.
    apply Z.lt_le_incl, max_array_length.
Qed.

Ltac prove_representable_array :=
  apply array_size_representable; lia.

Lemma in_shift_range_representable z :
  in_shift_range z ->
  representable z.
Proof.
  unfold in_shift_range, representable.
  assert (min_signed < 0).
  { unfold min_signed. apply M.min_signed_neg. }
  assert (zintsize <= max_signed).
  { rewrite <- zwordsize_is_zintsize. unfold max_signed.
    apply M.wordsize_max_signed.
    rewrite zwordsize_is_zintsize; unfold zintsize.
    generalize int_size_ge_31; lia. }
  lia.
Qed.

Lemma in_shift_range_b_spec z :
  in_shift_range z ->
  (0 <=? z) && (z <=? zintsize) = true.
Proof.
  unfold in_shift_range. intros.
  repeat rewrite Zle_imp_le_bool by lia.
  reflexivity.
Qed.

Lemma prove_representable_30 i :
  -(2 ^ 30) <= i < 2 ^ 30 ->
  representable i.
Proof.
  unfold representable.
  change (30) with (Z.of_nat 30).
  rewrite min_signed_eq, max_signed_eq, <- two_power_nat_equiv.
  assert (two_power_nat 30 <= two_power_nat w)
    by auto using two_power_nat_mono, w_ge_30.
  lia.
Qed.

Ltac prove_representable_30 :=
  apply prove_representable_30; lia.

Goal representable 1673.
Proof.
  prove_representable_30.
Qed.

Goal representable (-512348).
Proof.
  prove_representable_30.
Qed.

Lemma prove_urepresentable_30 i :
  0 <= i < 2 ^ 31 ->
  urepresentable i.
Proof.
  pose proof w_ge_30.
  unfold urepresentable.
  rewrite max_unsigned_eq, int_size_eq_succ_w.
  assert (2 ^ 31 <= two_power_nat (S w)).
  { change 31 with (Z.of_nat 31); rewrite <- two_power_nat_equiv.
    apply two_power_nat_mono; lia. }
  lia.
Qed.

Ltac prove_urepresentable_30 :=
  apply prove_urepresentable_30; lia.

Goal urepresentable 2147483647.
Proof.
  prove_urepresentable_30.
Qed.

Lemma prove_in_shift_range_30 i :
  0 <= i <= 31 ->
  in_shift_range i.
Proof.
  unfold in_shift_range.
  rewrite <- zwordsize_is_zintsize.
  unfold M.zwordsize. rewrite wordsize_is_int_size.
  pose proof int_size_ge_31.
  lia.
Qed.

Ltac prove_in_shift_range_30 :=
  apply prove_in_shift_range_30; lia.

Lemma prove_representable_sub (x y : Z) :
  0 <= x <= max_signed ->
  0 <= y <= max_signed ->
  representable (x - y).
Proof.
  intros [??] [??].
  split.
  - transitivity (0 - max_signed); [ | lia ].
    rewrite min_signed_eq, max_signed_eq.
    pose proof (Coqlib.two_power_nat_pos w); lia.
  - lia.
Qed.

(* A more general variant: if [x] and [y] are individually representable
   and both non-negative, then [x - y] is representable. *)

Lemma representable_sub (x y : Z) :
  representable x ->
  0 <= x ->
  representable y ->
  0 <= y ->
  representable (x - y).
Proof.
  unfold representable. intros [_ Hxmax] Hxmin [_ Hymax] Hymin.
  apply prove_representable_sub; lia.
Qed.

Ltac representable :=
  try solve [ tauto | eauto 2
            | prove_representable_30
            | prove_urepresentable_30
            | prove_in_shift_range_30
            | prove_representable_array
            | (eapply representable_sub; [representable | lia | representable | lia]) ].

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
