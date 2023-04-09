Lemma log2_lt_implies_lt_pow2 k z :
  Z.log2 z < Z.of_nat k ->
  z < two_power_nat k.
Proof.
  intros.
  destruct (zlt 0 z).
  (* Case: [0 < z]. *)
  { rewrite two_power_nat_equiv.
    rewrite Z.log2_lt_pow2 by assumption.
    assumption. }
  (* Case: [z <= 0]. *)
  { pose proof (two_power_nat_pos k). lia. }
Qed.

Lemma prove_representable z :
  0 <= z ->
  Z.log2 z < Z.of_nat (wordsize-1) ->
  representable z.
Proof.
  intros Hnneg Hlog.
  split.
  + generalize min_signed_neg. lia.
  + unfold max_signed, half_modulus, modulus.
    cut (z < two_power_nat wordsize / 2); [ lia |].
    (* [wordsize] is not zero; it can be written [w+1]. *)
    pose proof int_size_not_zero as Hnz.
    rewrite <- wordsize_is_int_size in Hnz.
    destruct wordsize as [| w ]; [ lia | clear Hnz ].
    (* The hypotheses and goal can then be cleaned up. *)
    replace (S w - 1)%nat with w in Hlog by lia.
    rewrite two_power_nat_S.
    rewrite half_of_double.
    (* Conclude. *)
    auto using log2_lt_implies_lt_pow2.
Qed.
