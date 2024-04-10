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

(* -------------------------------------------------------------------------- *)

(* The following lemma existed before [SimplifyHandle] was added. *)

(* -------------------------------------------------------------------------- *)

(* The following commutation diagram claims that if out of [(σ, m1)] there
   is both a simplification step and a reduction step, then this diagram can
   be closed via at most one reduction step.

   More precisely, the diagram is closed using [i] reduction steps, where
   [i] is either 0 or 1. Furthermore:

   - If [i] is 0 then the diagram guarantees [n' < n], that is, the diagram
     is closed using a simplification step that is shorter than the original
     simplification step. Intuitively, this means that the original
     reduction and simplification steps both go in the same direction. This
     guarantee is later necessary to prove the lemma [wp_simplify].

   - If [i] is 1 then the diagram guarantees [n' ≤ n]. This guarantee is
     necessary for the inductive proof of the diagram to go through; indeed,
     it is exploited in the case of [SimplifyTransitive]. It is not needed
     in the proof of [wp_simplify].

   Intuitively, this simulation diagram that applying a simplification step
   never causes the loss of a reduction step. In other words, applying a
   simplification step does not eliminate any permitted behavior. *)

Lemma simplify_step_diagram {A E n} {m1 m2 : micro A E} :
  (* If there is a simplification step of size [n]: *)
  simplify n m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the diagram can be closed using *)
  ∃ m'2 i n',
  (* [i] reduction steps *)
  steps i (σ, m2) (σ', m'2) ∧
  (* and a simplication step of size [n'] *)
  simplify n' m'1 m'2 ∧
  (* where [i] and [n'] satisfy the following constraint: *)
  (i = 0 ∧ n' < n  ∨  i = 1 ∧ n' ≤ n).
Local Ltac search :=
  do 3 eexists;
  eauto 8 using step_try2, simplify_try2 with steps step simplify simp lia.
Local Ltac use_ih :=
  match goal with
  Hstep: step (_, ?m) _,
  IH: ∀ _ _ _, step (_, ?m) _ → _ |- _ =>
    specialize (IH _ _ _ Hstep);
    destruct IH as (? & ? & ? & ? & ? & ?)
  end.
Ltac destruct_simplify_step_diagram :=
  match goal with h: _ ∨ _ |- _ => destruct h as [ (? & ?) | (? & ?) ] end;
  subst; destruct_steps.
Proof.
  (* A model of a beautiful proof. *)
  induction 1; intros.
  (* SimplifyEval *)
  { destruct_step. search. }
  (* SimplifyLoop *)
  { destruct_step. search. }
  (* SimplifyChooseAgree *)
  { destruct_step; search. }
  (* SimplifyParRetLeft *)
  (* This case is the reason why [SimplifyPerform] is needed. *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyParRetRight *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyPar *)
  { destruct_step; clarify_simplify; try solve [ search | use_ih; search ]. }
  (* SimplifyPerform *)
  { destruct_step. }
  (* SimplifyReflexive *)
  { search. }
  (* SimplifyTransitive *)
  { use_ih; destruct_simplify_step_diagram; [| use_ih ]; search. }
Qed.

(* In the special case where [m2] is final, the previous
   diagram can be simplified, because [m2] cannot step. *)

Lemma simplify_final_step_diagram {A E n} {m1 m2 : micro A E} {σ σ' m'1} :
  (* If there is a simplification step of [m1] to [m2], *)
  simplify n m1 m2 →
  (* if there is also a reduction step out of [m1], *)
  step (σ, m1) (σ', m'1) →
  (* and if [m2] is final, *)
  final m2 →
  (* then this reduction step must take us closer to [m2]. *)
  ∃ n',
  σ' = σ ∧
  simplify n' m'1 m2 ∧
  n' < n.
Proof.
  intros Hsimp Hstep Hfinal.
  destruct (simplify_step_diagram Hsimp Hstep) as (? & ? & ? & ? & ? & ?).
  destruct_simplify_step_diagram.
  { eauto. }
  { exfalso; eauto using destruct_step_final. }
Qed.

Ltac simplify_final_step_diagram :=
  match goal with
  Hsimp: simplify _ ?m1 ?m2,
  Hstep: step (_, ?m1) _
  |- _ =>
    let n' := fresh "n'" in
    destruct (simplify_final_step_diagram Hsimp Hstep)
      as (n' & -> & ? & ?);
      [ prove_final |]
  end.

(* -------------------------------------------------------------------------- *)

(* If there is a simplification path from [m1] to [m2],
   where [m2] is final,
   then there must be a reduction path from [m1] to [m2]. *)

Local Hint Constructors rtc : rtc.

Lemma simplify_final_implies_rtc_step :
  ∀ {n A E} {m1 m2 : micro A E},
  simplify n m1 m2 →
  final m2 →
  ∀ σ,
  rtc step (σ, m1) (σ, m2).
Proof.
  induction n using (well_founded_induction lt_wf).
  (* Reformulate the induction hypothesis. *)
  assert (IH:
    ∀ n' {A E} σ (m1 m2 : micro A E),
    simplify n' m1 m2 →
    final m2 →
    n' < n →
    rtc step (σ, m1) (σ, m2)
  ) by eauto; clear H.
  intros A E m1 m2 Hsimp Hfinal σ.
  (* Reason by cases on [m1]. *)
  triplicity σ m1 Hm1.
  (* Case: [m1] is [ret _]. *)
  { clarify_simplify. eauto with rtc. }
  (* Case: [m1] can step. *)
  { destruct Hm1 as ((σ' & m'1) & Hstep).
    simplify_final_step_diagram.
    (* IH is used. *)
    eauto with rtc. }
  (* Case: [m1] is stuck. *)
  { apply only_crash_and_throw_and_perform_are_stuck in Hm1.
    destruct Hm1 as [| [(e & ?) | (e & k & ?)]]; subst m1; simpl in Hfinal;
    clarify_simplify; solve [ eauto with rtc | tauto ]. }
Qed.

(* If there is a simplification step of [m1] to [m'1]
   and a reduction path of [m1] to [m2],
   where [m'1] and [m2] are final,
   then the two paths must lead to the same end result. *)

Lemma simplify_final_rtc_step_diagram
  {A E n} {m1 m'1 m2 : micro A E} {σ σ'} :
  simplify n m1 m'1 →
  rtc step (σ, m1) (σ', m2) →
  final m'1 →
  final m2 →
  σ' = σ ∧ m2 = m'1.
Proof.
  (* Reformulate the statement. *)
  cut (
    ∀ (c1 c2 : config A E),
    rtc step c1 c2 →
    ∀ σ σ' m1 m'1 m2 n,
    simplify n m1 m'1 →
    final m'1 →
    final m2 →
    c1 = (σ, m1) →
    c2 = (σ', m2) →
    σ' = σ ∧ m2 = m'1
  ). eauto. clear n m1 m'1 m2 σ σ'.
  (* Reason by induction on the reduction path. *)
  induction 1; intros; simplify_eq; clarify_simplify; destruct_config.
  (* The base case is immediate. *)
  { destruct_simplify_final. eauto. }
  (* In the other case, we are looking at a reduction step. We then
     exploit the fact that each reduction step must take us closer
     to [m'1], which is the target of the simplification path. *)
  simplify_final_step_diagram.
  eauto.
Qed.

(* The relation [simplify _], restricted to final results, is confluent.
   That is, simplification cannot lead to two distinct final results. *)

Lemma simplify_final_confluent {A E} {m m1 m2 : micro A E} {n1 n2} :
  simplify n1 m m1 →
  simplify n2 m m2 →
  final m1 →
  final m2 →
  m1 = m2.
Proof.
  intros Hsimp1 Hsimp2 Hfinal1 Hfinal2.
  pose proof (simplify_final_implies_rtc_step Hsimp1 Hfinal1 ∅) as Hpath.
  pose proof (simplify_final_rtc_step_diagram Hsimp2 Hpath Hfinal2 Hfinal1)
    as (_ & ?).
  eauto.
Qed.

Lemma simp_final_confluent {A E} {m m1 m2 : micro A E} :
  simp m m1 →
  simp m m2 →
  final m1 →
  final m2 →
  m1 = m2.
Proof.
  intros (n1 & H1)%simp_simplify (n2 & H2)%simp_simplify.
  eauto using simplify_final_confluent.
Qed.

Ltac simp_final_confluent :=
  match goal with
  | h1: simp ?m ?m1, h2: simp ?m ?m2 |- _ =>
      assert (m1 = m2); [
        eapply (simp_final_confluent h1 h2); prove_final
      | simplify_eq ]
  end.
