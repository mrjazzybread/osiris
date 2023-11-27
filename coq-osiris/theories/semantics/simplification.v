From stdpp Require Import relations. (* nsteps *)
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.
Local Open Scope nat_scope.

(* This file defines a simplification relation: [simp m m'] means that
   [m] can be simplified to [m']. Simplification is pure (it does not
   involve the heap and cannot make non-deterministic choices).

   When this relation holds, we expect [WP m' φ] to imply [WP m φ]. This
   means that one can prove a safety property of the simpler program [m']
   and transport this property back to [m].

   A simplification step is not necessarily a reduction step: that is,
   [simplify] is not a subrelation of [step].

   The simplification relation can serve two distinct (but related) purposes:

   - It can be used to simplify a program while proving that this program
     satisfies a specification of the form of [WP m φ]. This simplification
     process can be transparently performed by the tactics that we define.

   - It can be used to write specifications for pure programs. Indeed, if a
     program is pure (that is, does not involve divergence, non-determinism,
     or mutable state) then it should admit a specification of the form
     [∃ a, simp m (ret a) ∧ φ a]. See the judgement [total] in this file.

     Such a specification implies [WP m (λa, ⌜ φ a ⌝)], so a pure program
     is a special case of a possibly-impure program. *)

(* -------------------------------------------------------------------------- *)

(* The relation [simp m m'] is inductively defined as follows. *)

(* The constructors [SimpEval] and [SimpLoop] allow certain [Stop] events to
   be replaced with their meaning.

   [SimpChooseAgree] requires that the computations [m1] and [m2] can both
   be simplified to a common computation [m]. Thus, this rule is applicable
   only in the special case where the final outcome of the computation is
   independent of the coin flip. This is useful; e.g., it allows OCaml's
   [assert] construct to be regarded as pure.

   Two constructors [SimpParRetLeft] and [SimpParRetRight] simplify a [par]
   construct where at least one side is [ret _].

   The constructor [SimpPar] allows simplification to take place under a [Par]
   constructor.

   The constructors [SimpReflexive] and [SimpTransitive] make simplification
   reflexive and transitive by definition. This is essentially forced on us,
   because otherwise the premises of [SimpFlip] would be too restrictive. The
   paths from [k false] to [m] and from [k true] to [m] must be allowed to
   have different lengths. *)

Inductive simp {A : Type} : micro A → micro A → Prop :=
| SimpEval:
    ∀ η e k ko,
    simp
      (Stop CEval (η, e) k ko)
      (try (eval η e) k ko)
| SimpLoop :
    ∀ η x i1 i2 e k ko,
    simp
      (Stop CLoop (η, x, i1, i2, e) k ko)
      (try (loop η x i1 i2 e) k ko)
| SimpChooseAgree :
    ∀ {B} m m1 m2 (k : B → micro A) z,
    simp m1 m →
    simp m2 m →
    simp
      (Choose m1 m2 k z)
      (try m k z)
| SimpParRetLeft:
    ∀ {A1 A2} (a1 : A1) (m2 : micro A2) k ko,
    simp
      (Par (Ret a1) m2 k ko)
      (try m2 (λ v2, k (a1, v2)) ko)
| SimpParRetRight:
    ∀ {A1 A2} (m1 : micro A1) (a2 : A2) k ko,
    simp
      (Par m1 (Ret a2) k ko)
      (try m1 (λ v1, k (v1, a2)) ko)
| SimpPar:
    ∀ {A1 A2} m1 m'1 m2 m'2 (k : A1 * A2 → micro A) ko,
    simp m1 m'1 →
    simp m2 m'2 →
    simp (Par m1 m2 k ko) (Par m'1 m'2 k ko)
| SimpReflexive:
    ∀ m,
    simp m m
| SimpTransitive:
    ∀ m1 m2 m3,
    simp m1 m2 →
    simp m2 m3 →
    simp m1 m3
.

Global Hint Constructors simp : simp.

(* -------------------------------------------------------------------------- *)

(* More (derived) construction rules for [simp]. *)

(* The following two auxiliary lemmas can be useful when a constructor cannot
   be applied directly. *)

Lemma simp_up_to_eq_left {A} {m1 m1' m2 : micro A} :
  simp m1' m2 →
  m1 = m1' →
  simp m1 m2.
Proof.
  congruence.
Qed.

Lemma simp_up_to_eq_right {A} {m1 m2 m2' : micro A} :
  simp m1 m2 →
  m2 = m2' →
  simp m1 m2'.
Proof.
  congruence.
Qed.

(* Derived constructors. *)

Lemma SimpParRetRet {A1 A2 A} a1 a2 (k : A1 * A2 → micro A) ko :
  simp
    (Par (Ret a1) (Ret a2) k ko)
    (k (a1, a2)).
Proof.
  eauto using simp_up_to_eq_right with simp try_ret.
Qed.

Lemma SimpParRetLeftNext {A1 A2 A} a1 m2 (k : A1 * A2 → micro A) :
  simp
    (Par (Ret a1) m2 k next)
    (v2 ← m2 ; k (a1, v2)).
Proof.
  eauto using simp_up_to_eq_right with simp bind_as_try.
Qed.

Lemma SimpParRetRightNext {A1 A2 A} m1 a2 (k : A1 * A2 → micro A) :
  simp
    (Par m1 (Ret a2) k next)
    (v1 ← m1 ; k (v1, a2)).
Proof.
  eauto using simp_up_to_eq_right with simp bind_as_try.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define a 3-argument relation [simplify n m m'] where the natural integer
   [n] measures the length of the simplification path. The simulation lemmas
   [simplify_step_diagram] and [simplify_ret_step_diagram] control the manner
   in which [n] decreases or is preserved. This is necessary for the proof of
   the lemma [wp_simplify] to go through. *)

(* End users need not be know about this relation. *)

Inductive simplify {A : Type} : nat → micro A → micro A → Prop :=
| SimplifyEval:
    ∀ n p η e k ko,
    p = (η, e) →
    simplify (S n)
      (Stop CEval p k ko)
      (try (eval η e) k ko)
| SimplifyLoop :
    ∀ n p η x i1 i2 e k ko,
    p = (η, x, i1, i2, e) →
    simplify (S n)
      (Stop CLoop p k ko)
      (try (loop η x i1 i2 e) k ko)
| SimplifyChooseAgree :
    ∀ {B} n m m1 m2 (k : B → micro A) z,
    simplify n m1 m →
    simplify n m2 m →
    simplify (S n)
      (Choose m1 m2 k z)
      (try m k z)
| SimplifyParRetLeft:
    ∀ {A1 A2} n (a1 : A1) (m2 : micro A2) k ko,
    simplify (S n)
      (Par (Ret a1) m2 k ko)
      (try m2 (λ v2, k (a1, v2)) ko)
| SimplifyParRetRight:
    ∀ {A1 A2} n (m1 : micro A1) (a2 : A2) k ko,
    simplify (S n)
      (Par m1 (Ret a2) k ko)
      (try m1 (λ v1, k (v1, a2)) ko)
| SimplifyPar:
    ∀ {A1 A2} n1 n2 n m1 m'1 m2 m'2 (k : A1 * A2 → micro A) ko,
    simplify n1 m1 m'1 →
    simplify n2 m2 m'2 →
    S (n1 + n2) ≤ n →
    simplify n (Par m1 m2 k ko) (Par m'1 m'2 k ko)
| SimplifyReflexive:
    ∀ n m,
    simplify n m m
| SimplifyTransitive:
    ∀ n1 n2 n m1 m2 m3,
    simplify n1 m1 m2 →
    simplify n2 m2 m3 →
    S (n1 + n2) ≤ n →
    simplify n m1 m3
.

Global Hint Constructors simplify : simplify.

(* -------------------------------------------------------------------------- *)

(* [simplify _ m m'] and [simp m m'] are equivalent. *)

(* [simplify n m1 m2] implies [simp m1 m2]. *)

Lemma simplify_simp {A} n (m1 m2 : micro A) :
  simplify n m1 m2 →
  simp m1 m2.
Proof.
  induction 1; intros; subst; eauto with simp.
Qed.

(* [simp m1 m2] implies [simplify n m1 m2] for some [n]. *)

Lemma simp_simplify {A} {m1 m2 : micro A} :
  simp m1 m2 →
  ∃ n,
  simplify n m1 m2.
Proof.
  induction 1;
  repeat match goal with h: ∃ n, _ |- _ => destruct h end;
  eauto using
    (SimplifyEval 0),
    (SimplifyLoop 0),
    (SimplifyChooseAgree 0),
    (SimplifyParRetLeft 0),
    (SimplifyParRetRight 0),
    (SimplifyReflexive 0)
    with simplify.
Qed.

(* -------------------------------------------------------------------------- *)

(* Simplification is compatible with [try]. *)

Lemma simplify_try {A B} n (m1 m2 : micro A) (f : A → micro B) ko :
  simplify n m1 m2 →
  simplify n (try m1 f ko) (try m2 f ko).
Proof.
  induction 1; simpl;
  rewrite ?try_try; econstructor; eauto with congruence.
Qed.

Lemma simp_try {A B} (m1 m2 : micro A) (f : A → micro B) ko :
  simp m1 m2 →
  simp (try m1 f ko) (try m2 f ko).
Proof.
  induction 1; simpl; rewrite ?try_try;
  econstructor; eauto with congruence.
Qed.

(* Simplification is compatible with [bind]. *)

Lemma simplify_bind {A B} n (m1 m2 : micro A) (f : A → micro B) :
  simplify n m1 m2 →
  simplify n (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simplify_try.
Qed.

Lemma simp_bind {A B} (m1 m2 : micro A) (f : A → micro B) :
  simp m1 m2 →
  simp (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simp_try.
Qed.

(* -------------------------------------------------------------------------- *)

(* Inversion lemmas and tactics. *)

(* [ret _] cannot be simplified. *)

Lemma destruct_simplify_ret {A} n a1 (m2 : micro A) :
  simplify n (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_ret {A} a1 (m2 : micro A) :
  simp (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [crash] cannot be simplified. *)

Lemma destruct_simplify_crash {A} n (m2 : micro A) :
  simplify n crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_crash {A} (m2 : micro A) :
  simp crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [Next] cannot be simplified. *)

Lemma destruct_simplify_next {A} n (m2 : micro A) :
  simplify n Next m2 →
  m2 = Next.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_next {A} (m2 : micro A) :
  simp Next m2 →
  m2 = Next.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* These tactics apply the above lemmas, if possible. *)

Ltac clarify_simplify :=
  repeat match goal with
  | h: simplify _ (ret _) ?m |- _ => apply destruct_simplify_ret in h
  | h: simplify _ crash ?m |- _ => apply destruct_simplify_crash in h
  | h: simplify _ Next ?m |- _ => apply destruct_simplify_next in h
  end; simplify_eq.

Ltac clarify_simp :=
  repeat match goal with
  | h: simp (ret _) ?m |- _ => apply destruct_simp_ret in h
  | h: simp crash ?m |- _ => apply destruct_simp_crash in h
  | h: simp Next ?m |- _ => apply destruct_simp_next in h
  end; simplify_eq.

(* -------------------------------------------------------------------------- *)

(* The relation transformer [nsteps] is defined in stdpp. *)

(* A construction hint. *)

Local Hint Constructors nsteps : nsteps.

(* Destruction lemmas and tactic. *)

(* In principle, we should be able to use [dependent destruction h] directly
   in the definition of the tactic [destruct_nsteps]. The two lemmas below
   would then not be necessary. However, attempting to do this fails. The
   lemmas are accepted, but Coq 8.16.1 signals a Universe Inconsistency when
   this file is later loaded. *)

Lemma invert_nsteps_0 {A} {c c' : config A} :
  nsteps step 0 c c' →
  c' = c.
Proof.
  inversion 1; eauto.
Qed.

Lemma invert_nsteps_1 {A} (c c' : config A) :
  nsteps step 1 c c' →
  step c c'.
Proof.
  inversion 1; subst.
  match goal with h: nsteps step 0 _ _ |- _ => apply invert_nsteps_0 in h end.
  subst. eauto.
Qed.

Local Ltac destruct_nsteps :=
  repeat match goal with
  | h: nsteps step 0 _ _ |- _ => apply invert_nsteps_0 in h; simplify_eq
  | h: nsteps step 1 _ _ |- _ => apply invert_nsteps_1 in h
  end.

(* [nsteps step n] is compatible with a [Par] context. *)

Local Lemma nsteps_step_par_left
  {A1 A2 A} n σ σ' m1 m'1 m2 (k : A1 * A2 → micro A) ko :
  nsteps step n (σ, m1) (σ', m'1) →
  nsteps step n (σ, Par m1 m2 k ko) (σ', Par m'1 m2 k ko).
Proof.
  (* Massage the goal: *)
  remember (σ, m1) as c. remember (σ', m'1) as c'. intro h.
  revert c c' h σ m1 σ' m'1 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config;
  econstructor; eauto with nsteps; eauto with step.
Qed.

Local Lemma nsteps_step_par_right
  {A1 A2 A} n σ σ' m1 m2 m'2 (k : A1 * A2 → micro A) ko :
  nsteps step n (σ, m2) (σ', m'2) →
  nsteps step n (σ, Par m1 m2 k ko) (σ', Par m1 m'2 k ko).
Proof.
  (* Massage the goal: *)
  remember (σ, m2) as c. remember (σ', m'2) as c'. intro h.
  revert c c' h σ m2 σ' m'2 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config;
  econstructor; eauto with nsteps; eauto with step.
Qed.

Local Hint Resolve
  nsteps_step_par_left
  nsteps_step_par_right
: step.

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

Lemma simplify_step_diagram {A} {n} {m1 m2 : micro A} :
  (* If there is a simplification step of size [n]: *)
  simplify n m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the diagram can be closed using *)
  ∃ m'2 i n',
  (* [i] reduction steps *)
  nsteps step i (σ, m2) (σ', m'2) ∧
  (* and a simplication step of size [n'] *)
  simplify n' m'1 m'2 ∧
  (* where [i] and [n'] satisfy the following constraint: *)
  (i = 0 ∧ n' < n  ∨  i = 1 ∧ n' ≤ n).
Local Ltac search :=
  do 3 eexists;
  eauto 7 using step_try, simplify_try with nsteps step simplify lia.
Local Ltac use_ih :=
  match goal with
  Hstep: step (_, ?m) _,
  IH: ∀ _ _ _, step (_, ?m) _ → _ |- _ =>
    specialize (IH _ _ _ Hstep);
    destruct IH as (? & ? & ? & ? & ? & ?)
  end.
Ltac destruct_simplify_step_diagram :=
  match goal with h: _ ∨ _ |- _ => destruct h as [ (? & ?) | (? & ?) ] end;
  subst; destruct_nsteps.
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
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyParRetRight *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyPar *)
  { destruct_step; clarify_simplify; solve [ search | use_ih; search ]. }
  (* SimplifyReflexive *)
  { search. }
  (* SimplifyTransitive *)
  { use_ih. destruct_simplify_step_diagram; try use_ih; search. }
Qed.

(* In the special case where [m2] is of the form [ret a2], the previous
   diagram can be simplified, because [ret a2] cannot step. *)

Lemma simplify_ret_step_diagram {A} {n} {m1 : micro A} {a2 σ σ' m'1} :
  (* If there is a simplification step of [m1] to [ret a2]: *)
  simplify n m1 (ret a2) →
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the reduction step must take us closer to [ret a2]: *)
  ∃ n',
  σ' = σ ∧
  simplify n' m'1 (ret a2) ∧
  n' < n.
Proof.
  intros Hsimp Hstep.
  destruct (simplify_step_diagram Hsimp Hstep) as (? & ? & ? & ? & ? & ?).
  destruct_simplify_step_diagram; [| exfalso; destruct_step ].
  eauto.
Qed.

(* If there is a simplification path from [m1] to [ret a2], then there
   must be a reduction path from [m1] to [ret a2]. *)

Local Hint Constructors rtc : rtc.

Lemma simplify_ret_implies_step :
  ∀ {n A} {m1 : micro A} {a2},
  simplify n m1 (ret a2) →
  ∀ σ,
  rtc step (σ, m1) (σ, ret a2).
Proof.
  induction n using (well_founded_induction lt_wf).
  (* Reformulate the induction hypothesis. *)
  assert (IH:
    ∀ n' {A} σ (m1 : micro A) (a2 : A),
    simplify n' m1 (ret a2) →
    n' < n →
    rtc step (σ, m1) (σ, ret a2)
  ) by eauto; clear H.
  intros ? ? ? Hsimp σ.
  (* Reason by cases on [m1]. *)
  triplicity σ m1 Hm1.
  (* Case: [m1] is [ret _]. *)
  { clarify_simplify. eauto with rtc. }
  (* Case: [m1] can step. *)
  { destruct Hm1 as ((σ' & m'1) & Hstep).
    pose proof (simplify_ret_step_diagram Hsimp Hstep)
      as (n' & -> & Hsimp' & ?).
    specialize (IH _ _ σ _ _ Hsimp').
    eauto with rtc. }
  (* Case: [m1] is stuck. Impossible. *)
  { apply only_crash_and_next_are_stuck in Hm1.
    destruct Hm1 as [|]; subst m1; clarify_simplify. }
Qed.

(* If there is a simplification step of [m1] to [ret a2]
   and a reduction path of [m1] to [ret b2],
   then the two paths must lead to the same end result. *)

Lemma simplify_ret_rtc_step_diagram {A} {n} {m1 : micro A} {a2 b2 σ σ'} :
  simplify n m1 (ret a2) →
  rtc step (σ, m1) (σ', ret b2) →
  σ' = σ ∧ a2 = b2.
Proof.
  (* Reformulate the statement. *)
  cut (
    ∀ c1 c2,
    rtc step c1 c2 →
    ∀ σ σ' m1 b2 n (a2 : A),
    simplify n m1 (ret a2) →
    c1 = (σ, m1) →
    c2 = (σ', ret b2) →
    σ' = σ ∧ a2 = b2
  ). eauto. clear n m1 a2 b2 σ σ'.
  (* Reason by induction on the reduction path. *)
  induction 1; intros; simplify_eq; clarify_simplify; destruct_config.
  (* The base case is immediate. *)
  { eauto. }
  { (* Exploit the fact that each reduction step must take us closer to
       [ret a2]. *)
    match goal with Hsimp: simplify _ _ _, Hstep: step _ _ |- _ =>
      pose proof (simplify_ret_step_diagram Hsimp Hstep)
        as (n' & -> & Hsimp' & ?)
    end.
    eauto. }
Qed.

(* The relation [simplify _ ?m (ret ?a)] is confluent. That is,
   simplification cannot lead to two distinct results. *)

Lemma simplify_ret_confluent {A} (m : micro A) n1 n2 a1 a2 :
  simplify n1 m (ret a1) →
  simplify n2 m (ret a2) →
  a1 = a2.
Proof.
  intros Hsimp1 Hsimp2.
  pose proof (simplify_ret_implies_step Hsimp1 ∅) as Hpath.
  pose proof (simplify_ret_rtc_step_diagram Hsimp2 Hpath) as (_ & ?).
  congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas transport information in the reverse direction
   along the simplification relation. If [simplify _ m1 m2] holds, then
   information about [m2] can be transported to [m1]. *)

(* If [m1] can be simplified into [m2],
   and if [m2] can step,
   then [m1] can step. *)

Lemma invert_simplify_can_step {A} n (m1 m2 : micro A) σ :
  simplify n m1 m2 →
  can_step (σ, m2) →
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are [Ret] and [Crash] and [Next], and
     these terms cannot appear on the left-hand side of [simplify], so the
     proof is trivial. *)
  induction 1; eauto with step.
Qed.

(* If [m1] can be simplified into [ret a2] then
   either [m1] is [ret _]
   or [m1] can step. *)

Lemma invert_simplify_ret {A} n (m1 : micro A) a2 σ :
  simplify n m1 (ret a2) →
  is_ret m1 = None →
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are [Ret] and [Crash] and [Next], and
     these terms cannot appear on the left-hand side of [simplify], so the
     proof is almost trivial. Only [SimplifyTransitive] requires work. *)
  intro h; dependent induction h; intros; simpl in *;
  try solve [ congruence | eauto with step ].

  (* SimplifyTransitive *)
  specialize (IHh2 _ eq_refl).
  case_eq (is_ret m2); [ intros a'2 Hm2 | intro Hm2 ].
  (* Case: [m2] is [ret a2]. *)
  { apply invert_is_ret_Some in Hm2. subst m2.
    eauto using invert_simplify_can_step. }
  (* Case: [m2] is not [ret _]. *)
  { specialize (IHh2 Hm2).
    eauto using invert_simplify_can_step. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The relation [simplify] is confluent. *)

(* This result is stronger than [simplify_ret_confluent], because not
   every computation can be simplified to [ret _]. *)

(* This lemma is not crucial. Nevertheless, I have spent a couple hours
   proving it, mostly as a challenge for myself, so I am keeping it. *)

Lemma simplify_confluent :
  ∀ {n i2 j' A} {m1 m2 m'1 : micro A},
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
    ∀ i2 j' A (m1 m2 m'1 : micro A),
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
      generalize (IH _ _ _ _ _ _ h v); intro IH';
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
  intros i2 j' A m1 m2 m'1 vertical' horizontal ?.
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
    repeat diagram; search
  ].
Qed.

(* The relation [simp _ (ret _)] is confluent. *)

Lemma simp_ret_confluent {A} {m : micro A} {a1 a2} :
  simp m (ret a1) →
  simp m (ret a2) →
  a1 = a2.
Proof.
  intros Hsimp1 Hsimp2.
  apply simp_simplify in Hsimp1 as (n1 & H1).
  apply simp_simplify in Hsimp2 as (n2 & H2).
  eauto using simplify_ret_confluent.
Qed.

Ltac simp_ret_confluent :=
  match goal with
  | h1: simp ?m (ret ?a1), h2: simp ?m (ret ?a2) |- _ =>
      generalize (simp_ret_confluent h1 h2); intro
  end.

(* The relation [simp] is confluent. *)

Lemma simp_confluent {A} {m1 m2 m'1 : micro A} :
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

(* Useful type class instances. *)

(* Instantiating [Reflexive] allows to use [reflexivity] to prove
   [simp ?m ?m]. *)
Global Instance TC_reflexivity_simp {A} : Reflexive (@simp A) :=
  SimpReflexive.

(* Instantiating [Transitive] allows to use [transitivity] (as well as
   [etransitivity] to prove [simp ?m ?m']. *)
Global Instance TC_transitivity_simp {A} : Transitive (@simp A) :=
  SimpTransitive.

(* -------------------------------------------------------------------------- *)

(* We now define a Hoare logic for pure expressions. *)

(* Because this definition is based on [simp], it can be used to reason about
   pure expressions only. Because [simp] is inductively defined, it can reason
   about terminating expressions only; it is a logic of total correctness. *)

(* This Hoare logic can reason both about expressions that terminate normally
   and about expressions that raise the exception [Next]. *)

(* The judgement [total m φ ψ] means that either [m] terminates and produces
   a value [a] that satisfies the postcondition [φ], or [m] raises [Next],
   in which case [ψ] is satisfied. *)

Definition total {A} m (φ : A → Prop) ψ :=
  (∃ a, simp m (ret a) ∧ φ a) ∨
  (simp m Next ∧ ψ).

Ltac destruct_total :=
  match goal with
  | h: total _ _ _ |- _ =>
      destruct h as [ (? & ? & ?) | (? & ?) ]
  end.

(* The reasoning rule for [ret _]. *)

Lemma total_ret {A} a (φ : A → Prop) ψ :
  φ a →
  total (ret a) φ ψ.
Proof.
  intros. left. eauto with simp.
Qed.

(* The reasoning rule for [Next]. *)

Lemma total_Next {A} (φ : A → Prop) (ψ : Prop) :
  ψ →
  total Next φ ψ.
Proof.
  intros. right. eauto with simp.
Qed.

(* The consequence rule. *)

Lemma total_consequence {A} m (φ φ' : A → Prop) (ψ ψ' : Prop) :
  total m φ ψ →
  (∀ a, φ a → φ' a) →
  (ψ → ψ') →
  total m φ' ψ'.
Proof.
  intros. destruct_total.
  { left. eauto. }
  { right. eauto. }
Qed.

(* The simplification rule. *)

(* This rule allows performing a simplification step in the middle
   of a Hoare-style proof. *)

(* Although there is no reasoning rule for [Stop], the lemma [total_simp] can
   be used to reason about [Stop CEval] and [Stop CLoop]. *)

Lemma total_simp {A} m m' (φ : A → Prop) (ψ : Prop) :
  simp m m' →
  total m' φ ψ →
  total m φ ψ.
Proof.
  intros. destruct_total.
  { left. eauto with simp. }
  { right. eauto with simp. }
Qed.

(* A reasoning rule for [try]. *)

Lemma total_try {A B} m f g (φ : B → Prop) (φ' : A → Prop) (ψ ψ' : Prop) :
  total m φ' ψ' →
  (∀ a, φ' a → total (f a) φ ψ) →
  (ψ' → total (g ()) φ ψ) →
  total (try m f g) φ ψ.
Proof.
  intros. destruct_total.
  { eapply total_simp; [ eapply simp_try; eauto |].
    rewrite try_ret.
    eauto. }
  { eapply total_simp; [ eapply simp_try; eauto |].
    rewrite try_next.
    eauto. }
Qed.

(* A reasoning rule for [bind]. *)

Lemma total_bind {A B} m f (φ : B → Prop) (φ' : A → Prop) (ψ : Prop) :
  total m φ' ψ →
  (∀ a, φ' a → total (f a) φ ψ) →
  total (bind m f) φ ψ.
Proof.
  rewrite bind_as_try. eauto using total_try, total_Next.
Qed.

Lemma total_bind_unary {A B} m f (φ : B → Prop) (ψ : Prop) :
  total m (λ (a : A), total (f a) φ ψ) ψ →
  total (bind m f) φ ψ.
Proof.
  eauto using total_bind.
Qed.

(* A reasoning rule for [par]. *)

(* This rule is limited to the case where [ψ] is [False] because dealing with
   arbitrary [ψ] would require the ability to simplify [Par Next Next _ _]
   into [Next]. The relation [simp] currently does not allow this. *)

Lemma total_par {A1 A2} m1 m2
  (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  let ψ := False in
  total m1 φ1 ψ →
  total m2 φ2 ψ →
  (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
  total (par m1 m2) φ ψ.
Proof.
  intros. repeat destruct_total; try solve [ exfalso; tauto ].
  eapply total_simp.
  eapply SimpPar; eassumption.
  eapply total_simp; [ eapply SimpParRetRet |].
  eapply total_ret.
  eauto.
Qed.

(* A reasoning rule for [choose]. *)

(* This rule is limited to the case where [φ] is deterministic because we
   must ensure that [m1] and [m2] produce the same result. Indeed, unlike
   [step], the relation [simp] can simplify [choose m1 m2] only if both
   sides produce the same result. *)

(* This rule is limited to the case where [ψ] is [False] because we cannot
   allow [m1] to raise an exception while [m2] terminates, or vice-versa. *)

Definition deterministic {A} (φ : A → Prop) :=
  ∀ a1 a2, φ a1 → φ a2 → a1 = a2.

Lemma total_choose {A} m1 m2 (φ : A → Prop) :
  let ψ := False in
  total m1 φ ψ →
  total m2 φ ψ →
  deterministic φ →
  total (choose m1 m2) φ ψ.
Proof.
  intros. repeat destruct_total; try solve [ exfalso; tauto ].
  match goal with h1: simp m1 (ret ?a1), h2: simp m2 (ret ?a2) |- _ =>
    assert (a1 = a2); [ eauto | subst ]
  end.
  eapply total_simp.
  eapply SimpChooseAgree; eassumption.
  eapply total_ret.
  eauto.
Qed.

(* The infinitary intersection rule. *)

(* If for every [x] one can prove that the result of [m] satisfies [φ x],
   then one can deduce that the result of [m] satisfies [φ x] for every
   [x] simultaneously. *)

Lemma total_intersection {A} `{Inhabited X} m (φ : X → A → Prop) (ψ : Prop) :
  (∀ x, total m (φ x) ψ) →
  total m (λ a, ∀ x, φ x a) ψ.
Proof.
  intros Hm.
  (* Instantiate [Hm] with an arbitrary [x]. *)
  generalize (Hm inhabitant). intros [ (a & ? & ?) | (? & ?) ].
  (* Case: there exists [a] such that [m] can be simplified to [ret a]. *)
  { left. exists a. split; [ eauto |].
    intros x. destruct (Hm x) as [ (a' & ? & ?) | (? & ?) ].
    (* Because [simp _ (ret _)] is confluent, [a] and [a'] must be equal. *)
    { simp_ret_confluent. congruence. }
    (* Because [simp _ _] is confluent, [m] cannot be simplified both to
       [ret _] and [Next]. So, this subcase is impossible. *)
    { exfalso. simp_confluent; intros (m' & h1 & h2). clarify_simp. }
  }
  (* Case: [m] can be simplified to [Next]. *)
  { right. eauto. }
Qed.

(* The binary intersection rule. *)

(* If one can prove that the result of [m] satisfies [φ1]
   and if one can prove that the result of [m] satisfies [φ2]
   then one can deduce that the result of [m] satisfies [φ1] and [φ2]
   simultaneously. *)

Lemma total_binary_intersection {A} m (φ1 φ2 : A → Prop) (ψ : Prop) :
  total m φ1 ψ →
  total m φ2 ψ →
  total m (λ a, φ1 a ∧ φ2 a) ψ.
Proof.
  intros.
  set (post := λ (b : bool), λ a, if b then φ1 a else φ2 a).
  eapply total_consequence with (φ := λ a, ∀ b, post b a) (ψ := ψ).
  { eapply total_intersection.
    intros b. destruct b; unfold post; assumption. }
  { intros a Hpost. split.
    + apply (Hpost true).
    + apply (Hpost false). }
  { tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* We now prepare to prove the reciprocal bind rule, that is,
   the reverse implication of the lemma [total_bind_unary]. *)

(* -------------------------------------------------------------------------- *)

(* To do so, we need another indexed variant of the relation [simp].
   This variant places a weight of 1 on every node. This weight is
   used to do a well-founded induction in the proof of the lemma
   [invert_stack_try_ret]. *)

(* One can think of a proof of [sss n m m'] as a simplification tree
   from [m] to [m'] whose weight is [n]. *)

Inductive sss {A : Type} : nat → micro A → micro A → Prop :=
| SssEval:
    ∀ p η e k ko,
    p = (η, e) →
    sss 1
      (Stop CEval p k ko)
      (try (eval η e) k ko)
| SssLoop :
    ∀ p η x i1 i2 e k ko,
    p = (η, x, i1, i2, e) →
    sss 1
      (Stop CLoop p k ko)
      (try (loop η x i1 i2 e) k ko)
| SssChooseAgree :
    ∀ {B} n1 n2 m m1 m2 (k : B → micro A) z,
    sss n1 m1 m →
    sss n2 m2 m →
    sss (n1 + n2 + 1)
      (Choose m1 m2 k z)
      (try m k z)
| SssParRetLeft:
    ∀ {A1 A2} (a1 : A1) (m2 : micro A2) k ko,
    sss 1
      (Par (Ret a1) m2 k ko)
      (try m2 (λ v2, k (a1, v2)) ko)
| SssParRetRight:
    ∀ {A1 A2} (m1 : micro A1) (a2 : A2) k ko,
    sss 1
      (Par m1 (Ret a2) k ko)
      (try m1 (λ v1, k (v1, a2)) ko)
| SssPar:
    ∀ {A1 A2} n1 n2 n m1 m'1 m2 m'2 (k : A1 * A2 → micro A) ko,
    sss n1 m1 m'1 →
    sss n2 m2 m'2 →
    n1 + n2 ≤ n →
    sss n (Par m1 m2 k ko) (Par m'1 m'2 k ko)
| SssReflexive:
    ∀ m,
    sss 1 m m
| SssTransitive:
    ∀ n1 n2 n m1 m2 m3,
    sss n1 m1 m2 →
    sss n2 m2 m3 →
    n1 + n2 < n →
    sss n m1 m3
.

Local Hint Constructors sss : sss.

(* -------------------------------------------------------------------------- *)

(* [sss _ m m'] and [simp m m'] are equivalent. *)

Local Lemma sss_simp {A} {n} {m m' : micro A} :
  sss n m m' →
  simp m m'.
Proof.
  induction 1; subst; eauto with simp.
Qed.

Local Lemma simp_sss {A} {m m' : micro A} :
  simp m m' →
  ∃ n, sss n m m'.
Local Ltac baz :=
  match goal with h: ∃ n, sss n _ _ |- _ => destruct h end.
Proof.
  induction 1; try solve [ repeat baz; eauto with lia sss ].
Qed.

(* -------------------------------------------------------------------------- *)

(* The weight of a simplification tree is positive. *)

Local Lemma sss_positive {A} {n} {m m' : micro A} :
  sss n m m' →
  0 < n.
Proof.
  induction 1; eauto with lia.
Qed.

Local Ltac sss_positive :=
  match goal with h: sss _ _ _ |- _ =>
    generalize (sss_positive h); intro
  end.

(* -------------------------------------------------------------------------- *)

(* A stack of simplification trees is needed in the statement of the lemma
   [invert_stack_try_ret]. *)

(* One can think of this stack as an evaluation context. Although there is
   no syntax for evaluation contexts, because the [micro] monad is a shallow
   embedding, making evaluation contexts explicit, and controlling their
   weight, is required here. *)

Inductive stack {A : Type} : nat → micro A → micro A → Prop :=
| StackNil:
    forall n m,
    0 ≤ n →
    stack n m m
| StackCons:
    forall n1 n2 n m1 m2 m3,
    sss n1 m1 m2 →
    stack n2 m2 m3 →
    n1 + n2 ≤ n →
    stack n m1 m3.

Local Hint Constructors stack : stack.

(* -------------------------------------------------------------------------- *)

(* In [stack n m m'], the parameter [n] is an over-approximation of the
   weight of the stack, which itself is the sum of the weights of the
   trees in the stack. *)

Local Lemma stack_monotone {A} n (m m' : micro A) :
  ∀ n',
  stack n m m' →
  n ≤ n' →
  stack n' m m'.
Proof.
  induction 1; intros; econstructor; eauto with lia.
Qed.

(* A single tree forms a stack (of one cell). *)

Lemma sss_stack {A} n (m m' : micro A) :
  sss n m m' →
  stack n m m'.
Proof.
  eauto with stack lia.
Qed.

(* A stack represents a simplification path. *)

Lemma stack_simp {A} {n} {m m' : micro A} :
  stack n m m' →
  simp m m'.
Proof.
  induction 1; eauto using sss_simp with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* The main lemma. *)

(* If [try m m ko] can be simplified to [ret b]
   via a stack of weight [n],
   then:
   - either [m] can be simplified to [ret a]
     for some [a] such that
     [k a] can be simplified to [ret b]
     via a stack of weight [n],
   - or [m] can be simplified to [Next]
     and [ko()] can be simplified to [ret b]
     via a stack of weight [n].
 *)

(* This lemma is the reason why the coin flip effect, which would just flip
   a Boolean coin, has been removed and replaced with a primitive [Choose]
   construct in the [micro] monad. In the earlier approach, [choose m1 m2]
   was encoded as [b ← flip; if b then m1 else m2], and the relation [simp]
   included a rule stating that if [k false] and [k true] can both be
   simplified to [m] then [bind flip k] can be simplified to [m]. However,
   this rule invalidates the reciprocal bind rule: indeed, it states that
   [bind flip k] can be simplified even though [flip] itself cannot be
   simplified. In other words, the computation [flip] was viewed as impure
   (not simplifiable), yet the more complex computation [bind flip k] could
   be viewed as pure (simplifiable). This was not really a problem in
   practice, but we prefer to have a better-behaved language if we can. *)

Lemma invert_stack_try_ret :
  ∀ n {A B} m (k : A → micro B) ko b,
  stack n (try m k ko) (ret b) →
  total m
    (λ a, stack n (k a) (ret b))
    (stack n (ko()) (ret b)).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).

  (* Reformulate the induction hypothesis by weakening it so that its
     conclusion mentions [n] instead of [i]. Also, place the side
     condition [i < n] in the last position. *)
  assert (IHw :
    ∀ i {A B} m (k : A → micro B) ko b,
    stack i (try m k ko) (ret b) →
    i < n →
    total m
      (λ a, stack n (k a) (ret b))
      (stack n (ko()) (ret b))
  ).
  { intros. eapply total_consequence; intuition eauto using stack_monotone. }
  clear IH.

  (* Now begin the proof. *)
  intros A B m k ko b.
  intros Hstack.

  (* If [m] is [ret a] or [Next], then the result is immediate. Treat
     these two cases now, so as to avoid treating them several times
     later on. *)
  destruct (ret_or_next_or_else m) as [ (a & ?) | [ ? | (Hret & HNext) ]].
  (* Case: [m] is [ret a]. *)
  { subst m. rewrite try_ret in Hstack. eapply total_ret. eauto. }
  (* Case: [m] is [Next]. *)
  { subst m. rewrite try_next in Hstack. eapply total_Next. eauto. }
  (* We can now assume that [m] is neither [ret _] nor [Next]. *)

  (* Is the stack empty? *)
  dependent destruction Hstack.
  (* Case: the stack is empty. *)
  { clear IHw. exfalso. eauto using invert_try_eq_ret. }
  (* Case: the stack is nonempty. Analyze its first element. *)
  match goal with h: sss _ _ _ |- _ => dependent destruction h end.

  (* Subcase: [SssEval]. *)
  { subst p.
    (* [m] is [Stop CEval _ _ _]. *)
    invert_try_eq_stop. subst m. clear Hret HNext.
    (* Perform one step forward in the goal. *)
    eapply total_simp; [ eapply SimpEval |].
    (* Recognize [(try (try _ _ _) _ _)] in the stack. (Yes!) *)
    rewrite <- try_try in Hstack.
    (* Abstract away the inner [try _ _ _]. (Optional.) *)
    match type of Hstack with context[try ?m _ _] =>
      generalize dependent m
    end; intros m Hstack.
    (* We recognize an opportunity to apply the induction hypothesis. *)
    eauto with lia.
  }

  (* Subcase: [SssLoop]. *)
  { subst p.
    (* [m] is [Stop Loop _ _ _]. *)
    invert_try_eq_stop. subst m. clear Hret HNext.
    (* Perform one step forward in the goal. *)
    eapply total_simp; [ eapply SimpLoop |].
    (* Recognize [(try (try _ _ _) _ _)] in the stack. (Yes!) *)
    rewrite <- try_try in Hstack.
    (* Abstract away the inner [try _ _ _]. (Optional.) *)
    match type of Hstack with context[try ?m _ _] =>
      generalize dependent m
    end; intros m Hstack.
    (* We recognize an opportunity to apply the induction hypothesis. *)
    eauto with lia.
  }

  (* Subcase: [SssChoose]. *)
  {
    (* [m] is [Choose m1 m2 _ _]. *)
    invert_try_eq_choose. subst m. clear Hret HNext.
    (* Perform one step forward in the goal. *)
    eapply total_simp; [ eapply SimpChooseAgree; eauto using sss_simp |].
    (* Recognize [(try (try _ _ _) _ _)] in the stack. (Yes!) *)
    rewrite <- try_try in Hstack.
    (* Apply the induction hypothesis. *)
    eauto with lia.
  }

  (* Subcase: [SssParRetLeft]. *)
  {
    (* [m] is [Par m1 m2 _ _]. *)
    invert_try_eq_par. subst m. clear Hret HNext.
    (* Perform one step forward in the goal. *)
    eapply total_simp; [ eapply SimpParRetLeft |].
    (* Recognize [(try (try _ _ _) _ _)] in the stack. (Yes!) *)
    rewrite <- try_try in Hstack.
    (* Apply the induction hypothesis. *)
    eauto with lia.
  }

  (* Subcase: [SssParRetRight]. *)
  {
    (* [m] is [Par m1 m2 _ _]. *)
    invert_try_eq_par. subst m. clear Hret HNext.
    (* Perform one step forward in the goal. *)
    eapply total_simp; [ eapply SimpParRetRight |].
    (* Recognize [(try (try _ _ _) _ _)] in the stack. (Yes!) *)
    rewrite <- try_try in Hstack.
    (* Apply the induction hypothesis. *)
    eauto with lia.
  }

  (* Subcase: [SssPar]. *)
  {
    (* [m] is [Par m1 m2 _ _]. *)
    invert_try_eq_par. subst m. clear Hret HNext.
    (* Change [m1] to [m'1] and [m2] to [m'2] in the goal. *)
    eapply total_simp.
    { eapply SimpPar; eapply sss_simp; eauto. }
    (* Recognize [try (Par _ _ _ _) _ _] in the stack. *)
    rewrite <- try_Par in Hstack.
    (* Apply the induction hypothesis. *)
    sss_positive. eauto with lia.
  }

  (* Subcase: [SssReflexive]. *)
  { eauto with lia. }

  (* Subcase: [SssTransitive]. *)
  { eauto with stack lia. }

Qed.

(* -------------------------------------------------------------------------- *)

(* The previous lemma can now be specialized to the case where the stack
   initially has height one, that is, it consists of a single tree. *)

(* This yields the reciprocal try rule. *)

Lemma invert_simp_try_ret {A B} m (k : A → micro B) ko b :
  simp (try m k ko) (ret b) →
  total m
    (λ a, simp (k a) (ret b))
    (simp (ko()) (ret b)).
Proof.
  intros Hsimp.
  (* Transform [simp _ _] into [sss n _ _] for some unknown [n]. *)
  apply simp_sss in Hsimp.
  destruct Hsimp as (n & Hsimp).
  (* Thus, we have a stack (of one cell). *)
  apply sss_stack in Hsimp.
  (* We can apply the previous lemma. *)
  apply invert_stack_try_ret in Hsimp.
  (* The result then follows via the consequence rule. *)
  eapply total_consequence; [ eauto | |].
  + simpl. eauto using stack_simp.
  + eauto using stack_simp.
Qed.

(* The previous lemma can be specialized to obtain a result about [bind]. *)

Lemma invert_simp_bind_ret_total {A B} m (k : A → micro B) b :
  simp (bind m k) (ret b) →
  total m
    (λ a, simp (k a) (ret b))
    False.
Proof.
  rewrite bind_as_try.
  intros h.
  eapply total_consequence.
  { eauto using invert_simp_try_ret. }
  { eauto. }
  (* There remains to argue that [Next] cannot reduce to [ret _]. *)
  { simpl. intros. clarify_simp. }
Qed.

(* Unfolding [total] in the previous result yields this perhaps more
   readable statement. *)

(* This is the reciprocal bind rule. *)

Lemma invert_simp_bind_ret {A B} m (k : A → micro B) b :
  simp (bind m k) (ret b) →
  ∃ a, simp m (ret a) ∧ simp (k a) (ret b).
Proof.
  intros h. apply invert_simp_bind_ret_total in h. unfold total in h. tauto.
Qed.
