(* The following confluence lemma existed before [SimplifyPerform] was added. *)

(* -------------------------------------------------------------------------- *)

(* The relation [simplify] is confluent. *)

(* This result is stronger than [simplify_ret_confluent], because not
   every computation can be simplified to [ret _]. *)

(* This lemma is not crucial. Nevertheless, I have spent a couple hours
   proving it, mostly as a challenge for myself, so I am keeping it. *)

Lemma simplify_confluent :
  ∀ {n i2 j' A E} {m1 m2 m'1 : micro A E},
  simplify i2 m1 m2 →
  simplify j' m1 m'1 →
  i2 + j' = n →
  ∃ m'2 j2 i',
  simplify j2 m'1 m'2 ∧
  simplify i' m2 m'2 ∧
  i' ≤ j' ∧ j2 ≤ i2.
Local Ltac search ::=
  do 3 eexists;
  eauto using simplify_try with simplify lia.
Proof.
  induction n using (well_founded_induction lt_wf).
  (* Reformulate the induction hypothesis for easier application. *)
  assert (IH:
    ∀ i2 j' A E (m1 m2 m'1 : micro A E),
    simplify i2 m1 m2 →
    simplify j' m1 m'1 →
    i2 + j' < n →
    ∃ m'2 j2 i',
    simplify j2 m'1 m'2 ∧
    simplify i' m2 m'2 ∧
    i' ≤ j' ∧ j2 ≤ i2
  ) by eauto; clear H.
  (* The tactic [diagram__ h v] expects two [simplify] edges,
     a horizontal one [h] and a vertical one [v],
     and applies the induction hypothesis to them.
     This yields two new [simplify] edges,
     which we also name [h] and [v]. *)
  Local Ltac diagram__ h v :=
    (* Recognize the induction hypothesis. *)
    match goal with IH: ∀ (i2 j' : nat), _ |- _ =>
      let IH' := fresh in
      (* Apply it to [h] and [v]. *)
      generalize (IH _ _ _ _ _ _ _ h v); intro IH';
      (* Discharge the proof obligation [i2 + j' < n]. *)
      match type of IH' with ?check → _ =>
        let fact := fresh in
        assert (fact: check) by lia;
        specialize (IH' fact);
        clear fact
      end;
      (* Clear old edges and introduce new edges under the same names. *)
      clear h v;
      destruct IH' as (? & ? & ? & h & v & ? & ?)
    end.
  (* The tactic [diagram] identifies two [simplify] edges
     and applies the induction hypothesis to them. *)
  Local Ltac diagram :=
    match goal with h: simplify _ ?m _, v: simplify _ ?m _ |- _ =>
      diagram__ h v
    end.
  (* We are now ready. *)
  intros i2 j' A E m1 m2 m'1 vertical' horizontal ?.
  (* Analyze the vertical edge, while keeping a copy of it. *)
  generalize vertical'; intro vertical.
  dependent destruction vertical';
  try solve [
    (* SimplifyTransitive *)
    repeat diagram; search
  |
    (* All other cases: *)
    (* Analyze the horizontal edge. *)
    dependent destruction horizontal; subst;
    try clarify_simplify;
    try solve [
      search
    | diagram; diagram; search
    ]
  ].
Qed.

(* The relation [simp] is confluent. *)

Lemma simp_confluent {A E} {m1 m2 m'1 : micro A E} :
  simp m1 m2 →
  simp m1 m'1 →
  ∃ m'2,
  simp m'1 m'2 ∧
  simp m2 m'2.
Proof.
  intros Hsimp1 Hsimp2.
  apply simp_simplify in Hsimp1 as (n1 & H1).
  apply simp_simplify in Hsimp2 as (n2 & H2).
  pose proof (simplify_confluent H1 H2 eq_refl)
    as (m'2 & ? & ? & ? & ? & _ & _).
  eauto using simplify_simp.
Qed.

Ltac simp_confluent :=
  match goal with
  | h1: simp ?m ?m'1, h2: simp ?m ?m'2 |- _ =>
      generalize (simp_confluent h1 h2)
  end.

