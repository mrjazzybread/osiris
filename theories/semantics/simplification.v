From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.

(* This file defines a simplification relation: [simplify _ m m'] means that
   [m] can be simplified to [m'].

   When this relation holds, we expect [WP m' φ] to imply [WP m φ]. This
   means that one can prove a safety property of the simpler program [m']
   and transport this property back to [m].

   The simplification relation can serve two slightly distinct purposes:

   - It can be used to simplify a program while proving that this program
     satisfies a specification of the form of [WP m φ]. This simplification
     process can be transparently performed by the tactics that we define.

   - It can be used to write specifications for pure programs. Indeed, if a
     program is pure (that is, does not involve divergence, non-determinism,
     or mutable state) then it should admit a specification of the form
     [∃ n a, simplify n m (ret a) ∧ P a].

     Such a specification implies [WP m (λa, ⌜ P a ⌝)], so a pure program
     is a special case of a possibly-impure program. *)

(* -------------------------------------------------------------------------- *)

(* The simplification relation is inductively defined as follows. *)

(* The constructors [SimplifyEval] and [SimplifyLoop] allow certain [Stop]
   events to be replaced with their meaning.

   [SimplifyFlip] requires that the computations [k false] and [k true] can
   both be simplified to a common computation [m]. Thus, [SimplifyFlip] is
   applicable only in the special case where the final outcome of the
   computation is independent of the coin flip. This is useful; e.g., it
   allows OCaml's [assert] construct to be regarded pure.

   Two constructors [SimplifyParRetLeft] and [SimplifyParRetRight] simplify a
   [par] construct where at least one side is [ret _].

   A simplification step is not necessarily a reduction step: that is,
   [simplify] is not a subrelation of [step].

   The constructor [SimplifyPar] allows simplification to take place under a
   [Par] constructor.

   The constructors [SimplifyReflexive] and [SimplifyTransitive] make
   simplification reflexive and transitive by definition. This is essentially
   forced on us, because otherwise the premises of [SimplifyFlip] would be too
   restrictive. The paths from [k false] to [m] and from [k true] to [m] must
   be allowed to have different lengths. *)

(* The relation [simplify n m m'] is indexed with a natural integer [n], which
   measures the length of the simplification path. The main simulation lemmas,
   [simplify_step_diagram] and [simplify_ret_step_diagram], control the manner
   in which [n] decreases or is preserved. This is necessary for the proof of
   the lemma [wp_simplify] to go through. *)

Inductive simplify {A : Type} : nat → free A → free A → Prop :=
| SimplifyEval:
    ∀ n η e k ko,
    simplify (S n)
      (Stop CEval (η, e) k ko)
      (try (eval η e) k ko)
| SimplifyLoop :
    ∀ n η x i1 i2 e k ko,
    simplify (S n)
      (Stop CLoop (η, x, i1, i2, e) k ko)
      (try (loop η x i1 i2 e) k ko)
| SimplifyFlip :
    ∀ n x k ko m,
    simplify n (k false) m →
    simplify n (k true) m →
    simplify (S n)
      (Stop CFlip x k ko)
      m
| SimplifyParRetLeft:
    ∀ {A1 A2} n (a1 : A1) (m2 : free A2) k ko,
    simplify (S n)
      (Par (Ret a1) m2 k ko)
      (try m2 (λ v2, k (a1, v2)) ko)
| SimplifyParRetRight:
    ∀ {A1 A2} n (m1 : free A1) (a2 : A2) k ko,
    simplify (S n)
      (Par m1 (Ret a2) k ko)
      (try m1 (λ v1, k (v1, a2)) ko)
| SimplifyPar:
    ∀ {A1 A2} n1 n2 n m1 m'1 m2 m'2 (k : A1 * A2 → free A) ko,
    simplify n1 m1 m'1 →
    simplify n2 m2 m'2 →
    n1 + n2 ≤ n →
    simplify n (Par m1 m2 k ko) (Par m'1 m'2 k ko)
| SimplifyReflexive:
    ∀ n m,
    simplify n m m
| SimplifyTransitive:
    ∀ n1 n2 n m1 m2 m3,
    simplify n1 m1 m2 →
    simplify n2 m2 m3 →
    n1 + n2 ≤ n →
    simplify n m1 m3
.

Global Hint Constructors simplify : simplify.

(* Simplification is compatible with [try]. *)

Lemma simplify_try {A B} n (m1 m2 : free A) (f : A → free B) ko :
  simplify n m1 m2 →
  simplify n (try m1 f ko) (try m2 f ko).
Proof.
  induction 1; simpl;
  rewrite ?try_try; econstructor; eauto with congruence.
Qed.

(* Simplification is compatible with [bind]. *)

Lemma simplify_bind {A B} n (m1 m2 : free A) (f : A → free B) :
  simplify n m1 m2 →
  simplify n (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simplify_try.
Qed.

(* -------------------------------------------------------------------------- *)

(* Inversion lemmas and tactics. *)

(* [ret _] cannot be simplified. *)

Lemma destruct_simplify_ret {A} n a1 (m2 : free A) :
  simplify n (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [crash] cannot be simplified. *)

Lemma destruct_simplify_crash {A} n (m2 : free A) :
  simplify n crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [Next] cannot be simplified. *)

Lemma destruct_simplify_next {A} n (m2 : free A) :
  simplify n Next m2 →
  m2 = Next.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* This tactic applies the above lemmas if possible. *)

Ltac clarify_simplify :=
  repeat match goal with
  | h: simplify _ (ret _) ?m |- _ => apply destruct_simplify_ret in h
  | h: simplify _ crash ?m |- _ => apply destruct_simplify_crash in h
  | h: simplify _ Next ?m |- _ => apply destruct_simplify_next in h
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
  {A1 A2 A} n σ σ' m1 m'1 m2 (k : A1 * A2 → free A) ko :
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
  {A1 A2 A} n σ σ' m1 m2 m'2 (k : A1 * A2 → free A) ko :
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

Lemma simplify_step_diagram {A} {n} {m1 m2 : free A} :
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
  eauto 7 using step_try with nsteps step simplify lia.
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
  (* SimplifyFlip *)
  (* The fact [k false] and [k true] both simplify to [m] is exploited. *)
  { destruct_step. destruct b; search. }
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

Lemma simplify_ret_step_diagram {A} {n} {m1 : free A} {a2 σ σ' m'1} :
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

(* This lemma is currently not used. *)

Local Hint Constructors rtc : rtc.

Lemma simplify_ret_implies_step :
  ∀ n {A} σ (m1 : free A) (a2 : A),
  simplify n m1 (ret a2) →
  rtc step (σ, m1) (σ, ret a2).
Proof.
  induction n using (well_founded_induction lt_wf).
  (* Reformulate the induction hypothesis. *)
  assert (IH:
    ∀ n' {A} σ (m1 : free A) (a2 : A),
    simplify n' m1 (ret a2) →
    n' < n →
    rtc step (σ, m1) (σ, ret a2)
  ) by eauto; clear H.
  intros ? ? ? ? Hsimp.
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

(* This lemma is currently not used. *)

Lemma simplify_ret_rtc_step_diagram {A} {n} {m1 : free A} {a2 b2 σ σ'} :
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

(* -------------------------------------------------------------------------- *)

(* The following lemmas transport information in the reverse direction
   along the simplification relation. If [simplify _ m1 m2] holds, then
   information about [m2] can be transported to [m1]. *)

(* If [m1] can be simplified into [m2],
   and if [m2] can step,
   then [m1] can step. *)

Lemma invert_simplify_can_step {A} n (m1 m2 : free A) σ :
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

Lemma invert_simplify_ret {A} n (m1 : free A) a2 σ :
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

(* A non-indexed simplification relation. *)

(* This version is intended for use by end users. *)

Inductive simp {A : Type} : free A → free A → Prop :=
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
| SimpFlip :
    ∀ x k ko m,
    simp (k false) m →
    simp (k true) m →
    simp
      (Stop CFlip x k ko)
      m
| SimpParRetLeft:
    ∀ {A1 A2} (a1 : A1) (m2 : free A2) k ko,
    simp
      (Par (Ret a1) m2 k ko)
      (try m2 (λ v2, k (a1, v2)) ko)
| SimpParRetRight:
    ∀ {A1 A2} (m1 : free A1) (a2 : A2) k ko,
    simp
      (Par m1 (Ret a2) k ko)
      (try m1 (λ v1, k (v1, a2)) ko)
| SimpPar:
    ∀ {A1 A2} m1 m'1 m2 m'2 (k : A1 * A2 → free A) ko,
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

(* This auxiliary lemma is useful when a constructor of the relation [simp]
   cannot be applied directly. *)

Lemma simp_up_to_eq {A} {m1 m2 m2' : free A} :
  simp m1 m2 →
  m2 = m2' →
  simp m1 m2'.
Proof.
  congruence.
Qed.

(* Simplification is compatible with [try]. *)

Lemma simp_try {A B} (m1 m2 : free A) (f : A → free B) ko :
  simp m1 m2 →
  simp (try m1 f ko) (try m2 f ko).
Proof.
  induction 1; simpl; rewrite ?try_try;
  econstructor; eauto with congruence.
Qed.

(* Simplification is compatible with [bind]. *)

Lemma simp_bind {A B} (m1 m2 : free A) (f : A → free B) :
  simp m1 m2 →
  simp (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simp_try.
Qed.

(* [simplify n m1 m2] implies [simp m1 m2]. *)

(* This property should not be needed, but is a sanity check. *)

Lemma simplify_simp {A} n (m1 m2 : free A) :
  simplify n m1 m2 →
  simp m1 m2.
Proof.
  induction 1; eauto with simp.
Qed.

(* [simp m1 m2] implies [simplify n m1 m2] for some [n]. *)

Lemma simp_simplify {A} {m1 m2 : free A} :
  simp m1 m2 →
  ∃ n,
  simplify n m1 m2.
Proof.
  induction 1;
  repeat match goal with h: ∃ n, _ |- _ => destruct h end;
  eauto using
    (SimplifyEval 0),
    (SimplifyLoop 0),
    (SimplifyParRetLeft 0),
    (SimplifyParRetRight 0),
    (SimplifyReflexive 0)
    with simplify.
Qed.

(* Special cases. *)

Lemma SimpParRetRet {A1 A2 A} a1 a2 (k : A1 * A2 → free A) ko :
  simp
    (Par (Ret a1) (Ret a2) k ko)
    (k (a1, a2)).
Proof.
  eauto using simp_up_to_eq with simp try_ret.
Qed.

Lemma SimpParRetLeftNext {A1 A2 A} a1 m2 (k : A1 * A2 → free A) :
  simp
    (Par (Ret a1) m2 k next)
    (v2 ← m2 ; k (a1, v2)).
Proof.
  eauto using simp_up_to_eq with simp bind_as_try.
Qed.

Lemma SimpParRetRightNext {A1 A2 A} m1 a2 (k : A1 * A2 → free A) :
  simp
    (Par m1 (Ret a2) k next)
    (v1 ← m1 ; k (v1, a2)).
Proof.
  eauto using simp_up_to_eq with simp bind_as_try.
Qed.
