From stdpp Require Import relations.
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
     or mutable state) then it should have a specification of the form
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
   reflexive and transitive by definition. *)

Inductive simp {A E : Type} : micro A E → micro A E → Prop :=
| SimpEval:
    ∀ η e k z,
    simp
      (Stop CEval (η, e) k z)
      (try (eval η e) k z)
| SimpLoop :
    ∀ η x i1 i2 e k z,
    simp
      (Stop CLoop (η, x, i1, i2, e) k z)
      (try (loop η x i1 i2 e) k z)
| SimpChooseAgree :
    ∀ {B E'} m m1 m2 (k : B → _) (z : E' → _),
    simp m1 m →
    simp m2 m →
    simp
      (Choose m1 m2 k z)
      (try m k z)
| SimpParRetLeft:
    ∀ {A1 A2 E'} a1 m2 (k : A1 * A2 → _) (z : E' → _),
    simp
      (Par (Ret a1) m2 k z)
      (try m2 (λ v2, k (a1, v2)) z)
| SimpParRetRight:
    ∀ {A1 A2 E'} m1 a2 (k : A1 * A2 → _) (z : E' → _),
    simp
      (Par m1 (Ret a2) k z)
      (try m1 (λ v1, k (v1, a2)) z)
| SimpPar:
    ∀ {A1 A2 E'} m1 m'1 m2 m'2 (k : A1 * A2 → _) (z : E' → _),
    simp m1 m'1 →
    simp m2 m'2 →
    simp (Par m1 m2 k z) (Par m'1 m'2 k z)
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

Lemma simp_up_to_eq_left {A E} {m1 m1' m2 : micro A E} :
  simp m1' m2 →
  m1 = m1' →
  simp m1 m2.
Proof.
  congruence.
Qed.

Lemma simp_up_to_eq_right {A E} {m1 m2 m2' : micro A E} :
  simp m1 m2 →
  m2 = m2' →
  simp m1 m2'.
Proof.
  congruence.
Qed.

(* A consequence rule. *)

Lemma simp_consequence {A E} (m : micro A E) a' a :
  simp m (ret a') →
  a = a' →
  simp m (ret a).
Proof.
  intros. subst. eauto.
Qed.

(* Derived constructors. *)

Lemma SimpParRetRet {A1 A2 A E E'} a1 a2 (k : A1 * A2 → _) (z : E' → micro A E) :
  simp
    (Par (Ret a1) (Ret a2) k z)
    (k (a1, a2)).
Proof.
  eauto using simp_up_to_eq_right with simp try_ret.
Qed.

Lemma SimpParRetLeftThrow {A1 A2 A E} a1 m2 (k : A1 * A2 → micro A E) :
  simp
    (Par (Ret a1) m2 k throw)
    (v2 ← m2 ; k (a1, v2)).
Proof.
  eauto using simp_up_to_eq_right with simp bind_as_try.
Qed.

Lemma SimpParRetRightThrow {A1 A2 A E} m1 a2 (k : A1 * A2 → micro A E) :
  simp
    (Par m1 (Ret a2) k throw)
    (v1 ← m1 ; k (v1, a2)).
Proof.
  eauto using simp_up_to_eq_right with simp bind_as_try.
Qed.

Lemma simp_par {A E A1 A2 E'} (m1 : micro A1 E) (m2 : micro A2 E) (m : micro A E')
  k (z : E -> micro A E') a1 a2 :
  simp m1 (ret a1) ->
  simp m2 (ret a2) ->
  simp (k (a1, a2)) m ->
  simp (Par m1 m2 k z) m.
Proof.
  intros. eauto with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define a 3-argument relation [simplify n m m'] where the natural integer
   [n] measures a certain notion of the cost of the simplification path from
   [m] to [m'].

   The main two commutative diagrams, namely [simplify_step_diagram] and
   [simplify_confluent], control the manner in which [n] decreases or is
   preserved.

   In [simplify_step_diagram], the fact that [n] cannot increase means that
   one [step] of computation cannot create simplification work. Intuitively,
   this is true because [step] does not duplicate computations.

   In [simplify_confluent], a similar intuition holds. One step of
   simplification cannot create more simplification work, because
   simplification does not duplicate computations. *)

(* In [SimplifyTransitive], requiring [0 < n1] and [0 < n2] lets us forbid a
   trivial use of reflexivity under the transitivity rule. This gives us a
   simple way of ensuring that the two children of the transitivity rule have
   smaller indices, while still assigning zero cost to the transitivity rule
   itself. *)

(* In [SimplifyPar], we could require [0 < n1 ∨ 0 < n2], because the case
   where both children perform no simplification work is trivial. However,
   that would not help. We must assign a nonzero cost to [SimplifyPar] anyway;
   otherwise, we cannot ensure that both children have smaller indices, and
   the proof of [simplify_confluent] fails. *)

(* It is worth noting that the lemma [wp_simp] needs only the weak commutative
   diagram [simp_step_diagram], where the index [n] is not controlled. Indeed,
   the proof of [wp_simp] is by Löb induction, so only a finite number of
   [step]s into the future are of interest. Therefore, even if the cost of the
   [simp] path is not under control, once the end of the future is reached, we
   do not care any more. *)

(* End users need not be know about the relation [simplify]. *)

Inductive simplify {A E : Type} : nat → micro A E → micro A E → Prop :=
| SimplifyEval:
    ∀ p η e k z,
    p = (η, e) →
    simplify 1
      (Stop CEval p k z)
      (try (eval η e) k z)
| SimplifyLoop :
    ∀ p η x i1 i2 e k z,
    p = (η, x, i1, i2, e) →
    simplify 1
      (Stop CLoop p k z)
      (try (loop η x i1 i2 e) k z)
| SimplifyChooseAgree :
    ∀ {B E'} n1 n2 m m1 m2 (k : B → _) (z : E' → _),
    simplify n1 m1 m →
    simplify n2 m2 m →
    simplify (n1 + n2 + 1)
      (Choose m1 m2 k z)
      (try m k z)
| SimplifyParRetLeft:
    ∀ {A1 A2 E'} a1 m2 (k : A1 * A2 → _) (z : E' → _),
    simplify 1
      (Par (Ret a1) m2 k z)
      (try m2 (λ v2, k (a1, v2)) z)
| SimplifyParRetRight:
    ∀ {A1 A2 E'} m1 a2 (k : A1 * A2 → _) (z : E' → _),
    simplify 1
      (Par m1 (Ret a2) k z)
      (try m1 (λ v1, k (v1, a2)) z)
| SimplifyPar:
    ∀ {A1 A2 E'} n1 n2 m1 m'1 m2 m'2 (k : A1 * A2 → _) (z : E' → _),
    simplify n1 m1 m'1 →
    simplify n2 m2 m'2 →
    simplify (n1 + n2 + 1) (Par m1 m2 k z) (Par m'1 m'2 k z)
| SimplifyReflexive:
    ∀ m,
    simplify 0 m m
| SimplifyTransitive:
    ∀ n1 n2 m1 m2 m3,
    simplify n1 m1 m2 →
    simplify n2 m2 m3 →
    0 < n1 →
    0 < n2 →
    simplify (n1 + n2) m1 m3
.

Global Hint Constructors simplify : simplify.

(* -------------------------------------------------------------------------- *)

(* [simplify 0 m1 m2] implies [m1 = m2]. *)

Lemma invert_simplify_zero {A E} {m1 m2 : micro A E} :
  simplify 0 m1 m2 →
  m1 = m2.
Proof.
  intros h; dependent induction h; eauto with lia f_equal.
Qed.

(* The requirement [0 < n1 ∧ 0 < n2] in [SimplifyTransitive] does not cause
   a loss of generality. Indeed, the cases [0 = n1] and [0 = n2] represent
   zero simplification work, so they are useless. *)

Lemma SimplifyTransitiveUnrestricted {A E} n1 n2 (m1 m2 m3 : micro A E) :
  simplify n1 m1 m2 →
  simplify n2 m2 m3 →
  simplify (n1 + n2) m1 m3.
Proof.
  intros H1 H2.
  assert (0 = n1 ∨ 0 < n1) as [|] by lia; [ subst |].
  { apply invert_simplify_zero in H1. subst. eauto. }
  assert (0 = n2 ∨ 0 < n2) as [|] by lia; [ subst |].
  { apply invert_simplify_zero in H2. subst.
    replace (n1 + 0) with n1 by lia. eauto. }
  eauto with simplify.
Qed.

Global Hint Resolve SimplifyTransitiveUnrestricted : simplify.

(* -------------------------------------------------------------------------- *)

(* [simplify _ m m'] and [simp m m'] are equivalent. *)

(* [simplify n m1 m2] implies [simp m1 m2]. *)

Lemma simplify_simp {A E} n (m1 m2 : micro A E) :
  simplify n m1 m2 →
  simp m1 m2.
Proof.
  induction 1; intros; subst; eauto with simp.
Qed.

(* [simp m1 m2] implies [simplify n m1 m2] for some [n]. *)

Lemma simp_simplify {A E} {m1 m2 : micro A E} :
  simp m1 m2 →
  ∃ n,
  simplify n m1 m2.
Proof.
  induction 1;
  repeat match goal with h: ∃ n, _ |- _ => destruct h end;
  eauto with simplify.
Qed.

(* -------------------------------------------------------------------------- *)

(* Simplification is compatible with [try]. *)

Lemma simplify_try {A B E' E} n m1 m2 (f : A → micro B E) (h : E' → _) :
  simplify n m1 m2 →
  simplify n (try m1 f h) (try m2 f h).
Proof.
  induction 1; simpl;
  rewrite ?try_try; econstructor; eauto with congruence.
Qed.

Lemma simp_try {A B E' E} m1 m2 (f : A → micro B E) (h : E' → _) :
  simp m1 m2 →
  simp (try m1 f h) (try m2 f h).
Proof.
  induction 1; simpl; rewrite ?try_try;
  econstructor; eauto with congruence.
Qed.

(* The Try rule. *)

Lemma prove_simp_try {A B E' E m m' a} {f : A → micro B E} (h : E' → _) :
  simp m (ret a) →
  simp (f a) m' →
  simp (try m f h) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.

(* The Try rule when the computation fails. *)

Lemma prove_simp_try_throw {A B E' E m m'} e {f : A → micro B E} (h : E' -> micro B E) :
  simp m (throw e) →
  simp (h e) m' →
  simp (try m f h) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.


(* Simplification is compatible with [bind]. *)

Lemma simplify_bind {A B E} n m1 m2 (f : A → micro B E) :
  simplify n m1 m2 →
  simplify n (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simplify_try.
Qed.

Lemma simp_bind {A B E} m1 m2 (f : A → micro B E) :
  simp m1 m2 →
  simp (bind m1 f) (bind m2 f).
Proof.
  rewrite !bind_as_try. eauto using simp_try.
Qed.

(* The Bind rule. *)

Lemma prove_simp_bind {A B E m m' a} {f : A → micro B E} :
  simp m (ret a) →
  simp (f a) m' →
  simp (bind m f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* Inversion lemmas and tactics. *)

(* [ret _] cannot be simplified. *)

Lemma destruct_simplify_ret {A E} n a1 (m2 : micro A E) :
  simplify n (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_ret {A E} a1 (m2 : micro A E) :
  simp (ret a1) m2 →
  m2 = ret a1.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [crash] cannot be simplified. *)

Lemma destruct_simplify_crash {A E} n (m2 : micro A E) :
  simplify n crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_crash {A E} (m2 : micro A E) :
  simp crash m2 →
  m2 = crash.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* [Throw _] cannot be simplified. *)

Lemma destruct_simplify_throw {A E} n e (m2 : micro A E) :
  simplify n (throw e) m2 →
  m2 = throw e.
Proof.
  intro h; dependent induction h; eauto.
Qed.

Lemma destruct_simp_throw {A E} e (m2 : micro A E) :
  simp (throw e) m2 →
  m2 = throw e.
Proof.
  intro h; dependent induction h; eauto.
Qed.

(* These tactics apply the above lemmas, if possible. *)

Ltac clarify_simplify :=
  repeat match goal with
  | h: simplify _ (ret _) ?m |- _ => apply destruct_simplify_ret in h
  | h: simplify _ crash ?m |- _ => apply destruct_simplify_crash in h
  | h: simplify _ (throw _) ?m |- _ => apply destruct_simplify_throw in h
  end; simplify_eq.

Ltac clarify_simp :=
  repeat match goal with
  | h: simp (ret _) ?m |- _ => apply destruct_simp_ret in h
  | h: simp crash ?m |- _ => apply destruct_simp_crash in h
  | h: simp (throw _) ?m |- _ => apply destruct_simp_throw in h
  end; simplify_eq.

(* A category of final terms, which cannot be simplified
   and cannot step. *)

Definition final {A E} (m : micro A E) :=
  match m with
  | Ret _ | Throw _ | Crash => True
  | _                       => False
  end.

Lemma destruct_simplify_final {A E n} {m1 m2 : micro A E} :
  simplify n m1 m2 →
  final m1 →
  m2 = m1.
Proof.
  intros. destruct m1; clarify_simplify; tauto.
Qed.

Lemma destruct_step_final {A E} σ1 σ2 (m1 m2 : micro A E) :
  step (σ1, m1) (σ2, m2) →
  final m1 →
  False.
Proof.
  intros. destruct m1; destruct_step; tauto.
Qed.

Ltac destruct_simplify_final :=
  match goal with h1: simplify _ ?m1 ?m2, h2: final ?m1 |- _ =>
    pose proof (destruct_simplify_final h1 h2); subst m2
  end.

(* -------------------------------------------------------------------------- *)

(* Destruction lemmas and tactic. *)

(* In principle, we should be able to use [dependent destruction h] directly
   in the definition of the tactic [destruct_steps]. The two lemmas below
   would then not be necessary. However, attempting to do this fails. The
   lemmas are accepted, but Coq 8.16.1 signals a Universe Inconsistency when
   this file is later loaded. *)

Lemma invert_steps_0 {A E} {c c' : config A E} :
  steps 0 c c' →
  c' = c.
Proof.
  inversion 1; eauto.
Qed.

Local Ltac destruct_steps :=
  repeat match goal with
  | h: steps 0 _ _ |- _ => apply invert_steps_0 in h; simplify_eq
  | h: steps 1 _ _ |- _ => apply nsteps_once_inv in h
end.

(* [steps n] is compatible with a [Par] context. *)

Local Lemma steps_step_par_left
  {A1 A2 A E' E} n σ σ' m1 m'1 m2 (k : A1 * A2 → micro A E) (z : E' → _) :
  steps n (σ, m1) (σ', m'1) →
  steps n (σ, Par m1 m2 k z) (σ', Par m'1 m2 k z).
Proof.
  (* Massage the goal: *)
  remember (σ, m1) as c. remember (σ', m'1) as c'. intro h.
  revert c c' h σ m1 σ' m'1 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config; econstructor.
  eapply StepParLeft; eassumption.
  eapply IHh; reflexivity.
Qed.

Local Lemma steps_step_par_right
  {A1 A2 A E' E} n σ σ' m1 m2 m'2 (k : A1 * A2 → micro A E) (z : E' → _) :
  steps n (σ, m2) (σ', m'2) →
  steps n (σ, Par m1 m2 k z) (σ', Par m1 m'2 k z).
Proof.
  (* Massage the goal: *)
  remember (σ, m2) as c. remember (σ', m'2) as c'. intro h.
  revert c c' h σ m2 σ' m'2 Heqc Heqc'.
  (* Prove it: *)
  induction 1; intros; simplify_eq; destruct_config; econstructor.
  eapply StepParRight; eassumption.
  eapply IHh; reflexivity.
Qed.

Local Hint Resolve
  steps_step_par_left
  steps_step_par_right
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
  eauto 8 using step_try, simplify_try with steps step simplify lia.
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
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyParRetRight *)
  { destruct_step; try solve [destruct_step]; clarify_simplify; search. }
  (* SimplifyPar *)
  { destruct_step; clarify_simplify; solve [ search | use_ih; search ]. }
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

Ltac prove_final :=
  first [ exact I | eauto ].

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

(* The following are (weakened) reformulations of the previous two lemmas
   in terms of [simp]. *)

Lemma simp_step_diagram {A E} {m1 m2 : micro A E} :
  (* If there is a simplification step: *)
  simp m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a reduction step: *)
  step (σ, m1) (σ', m'1) →
  (* then the diagram can be closed using *)
  ∃ m'2 i,
  (* [i] reduction steps *)
  steps i (σ, m2) (σ', m'2) ∧
  (* and a simplication step *)
  simp m'1 m'2 ∧
  (* where [i] is at most 1. *)
  (i = 0 ∨ i = 1).
Proof.
  (* It would be possible to give a direct proof of this lemma,
     without relying on [simplify_step_diagram]. *)
  intros (n & Hsimplify)%simp_simplify.
  intros ? ? ? Hstep.
  pose proof (simplify_step_diagram Hsimplify Hstep)
    as (m'2 & i & n' & ? & ? & ?).
  eauto 6 using simplify_simp with lia.
Qed.

Ltac simp_step_diagram :=
  match goal with
  Hsimp: simp ?m1 _,
  Hstep: step (_, ?m1) _
  |- _ =>
    let Hstep' := fresh in
    let Hsimp' := fresh in
    let Hcases := fresh in
    pose proof (simp_step_diagram Hsimp Hstep)
      as (? & ? & Hstep' & Hsimp' & Hcases);
    clear Hsimp Hstep;
    rename Hsimp' into Hsimp;
    rename Hstep' into Hstep;
    destruct Hcases;
    subst; destruct_steps
  end.

Lemma simp_final_step_diagram {A E} {m1 m2 : micro A E} {σ σ' m'1} :
  (* If there is a simplification step of [m1] to [m2], *)
  simp m1 m2 →
  (* if there is also a reduction step out of [m1], *)
  step (σ, m1) (σ', m'1) →
  (* and if [m2] is final, *)
  final m2 →
  (* then this reduction step does not prevent us from reaching [m2]. *)
  σ' = σ ∧
  simp m'1 m2.
Proof.
  intros (n & Hsimplify)%simp_simplify.
  intros Hstep Hfinal.
  simplify_final_step_diagram.
  eauto using simplify_simp.
Qed.

Ltac simp_final_step_diagram :=
  match goal with
  Hsimp: simp ?m1 ?m2,
  Hstep: step (_, ?m1) _
  |- _ =>
    destruct (simp_final_step_diagram Hsimp Hstep)
      as (-> & ?);
      [ prove_final |]
  end.

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
  { apply only_crash_and_throw_are_stuck in Hm1.
    destruct Hm1 as [| (e & ?)]; subst m1;
    clarify_simplify; eauto with rtc. }
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

(* -------------------------------------------------------------------------- *)

(* The following lemmas transport information in the reverse direction
   along the simplification relation. If [simplify _ m1 m2] holds, then
   information about [m2] can be transported to [m1]. *)

(* If [m1] can be simplified into [m2],
   and if [m2] can step,
   then [m1] can step. *)

Lemma invert_simp_can_step {A E} (m1 m2 : micro A E) σ :
  simp m1 m2 →
  can_step (σ, m2) →
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are [ret _] and [crash] and [throw _],
     and these terms cannot appear on the left-hand side of [simplify], so
     the proof is trivial. *)
  induction 1; eauto with step.
Qed.

(* If [m1] can be simplified into a final result [m2] then
   either [m1] is [m2]
   or [m1] can step. *)

Lemma invert_simp_final {A E} {m1 m2 : micro A E} σ :
  simp m1 m2 →
  final m2 →
  m1 = m2 ∨
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are the final terms, and these
     terms cannot be simplified, so the result is almost immediate. *)
  intro h; dependent induction h; intros Hfinal; simpl in *;
  eauto with step.
  (* Only [SimpTransitive] requires some work. *)
  destruct (IHh2 Hfinal); clear IHh2; [ subst |].
  { destruct (IHh1 Hfinal); eauto. }
  { eauto using invert_simp_can_step. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Potentially useful type class instances. *)

(* Instantiating [Reflexive] allows to use [reflexivity] to prove
   [simp ?m ?m]. *)
Global Instance TC_reflexivity_simp {A E} : Reflexive (@simp A E) :=
  SimpReflexive.

(* Instantiating [Transitive] allows to use [transitivity] (as well as
   [etransitivity] to prove [simp ?m ?m']. *)
Global Instance TC_transitivity_simp {A E} : Transitive (@simp A E) :=
  SimpTransitive.

(* -------------------------------------------------------------------------- *)

(* We now define a Hoare logic for pure expressions. *)

(* Because this definition is based on [simp], it can be used to reason about
   pure expressions only. Because [simp] is inductively defined, it can reason
   about terminating expressions only; it is a logic of total correctness. *)

(* This Hoare logic can reason both about expressions that terminate normally
   and about expressions that raise an exception. *)

(* The judgement [total m φ ψ] means that either [m] terminates and produces
   a result [a] that satisfies the postcondition [φ], or [m] raises an
   exception [e], such that [ψ e] is satisfied. *)

Definition total {A E} m (φ : A → Prop) (ψ : E → Prop) :=
  (∃ a, simp m (ret a) ∧ φ a) ∨
  (∃ e, simp m (throw e) ∧ ψ e).

(* The judgement [totalv m φ] is the special case where [ψ] is [λ _, False].
   It means that [m] must terminate and produce a result [a] such that [φ a]
   holds. *)

Definition totalv {A E} m (φ : A → Prop) :=
  total m φ (λ (e : E), False).

(* The tactic [destruct_total a e] destructs a hypothesis of the form
   [total m φ ψ] or [totalv m φ]. The result of [m], if there is one,
   is named [a]. The exception, if there is one, is named [e]. *)

Ltac destruct_total a e :=
  match goal with
  | h: total _ _ _ |- _ =>
      destruct h as [ (a & ? & ?) | (e & ? & ?) ]
  | h: totalv _ _ |- _ =>
      unfold totalv in h at 1;
      destruct h as [ (a & ? & ?) | (? & ?) ]; [| tauto ]
  end.

(* The reasoning rule for [ret _]. *)

Lemma total_ret {A E} a (φ : A → Prop) (ψ : E → Prop) :
  φ a →
  total (ret a) φ ψ.
Proof.
  intros. left. eauto with simp.
Qed.

(* The reasoning rule for [throw _]. *)

Lemma total_throw {A E} e (φ : A → Prop) (ψ : E → Prop) :
  ψ e →
  total (throw e) φ ψ.
Proof.
  intros. right. eauto with simp.
Qed.

(* The consequence rule. *)

Lemma total_consequence {A E} m (φ φ' : A → Prop) (ψ ψ' : E → Prop) :
  total m φ ψ →
  (∀ a, φ a → φ' a) →
  (∀ e, ψ e → ψ' e) →
  total m φ' ψ'.
Proof.
  intros. destruct_total a e.
  { left. eauto. }
  { right. eauto. }
Qed.

(* The simplification rule. *)

(* This rule allows performing a simplification step in the middle
   of a Hoare-style proof. *)

(* Although there is no reasoning rule for [Stop], the lemma [total_simp] can
   be used to reason about [Stop CEval] and [Stop CLoop]. *)

Lemma total_simp {A E} m m' (φ : A → Prop) (ψ : E → Prop) :
  simp m m' →
  total m' φ ψ →
  total m φ ψ.
Proof.
  intros. destruct_total a e.
  { left. eauto with simp. }
  { right. eauto with simp. }
Qed.

(* A reasoning rule for [try]. *)

Lemma total_try {A B E' E} m f g
  (φ : B → Prop) (φ' : A → Prop)
  (ψ : E → Prop) (ψ' : E' → Prop) :
  total m φ' ψ' →
  (∀ a, φ' a → total (f a) φ ψ) →
  (∀ e, ψ' e → total (g e) φ ψ) →
  total (try m f g) φ ψ.
Proof.
  intros. destruct_total a e.
  { eapply total_simp; [ eapply simp_try; eauto |].
    simpl try. eauto. }
  { eapply total_simp; [ eapply simp_try; eauto |].
    simpl try. eauto. }
Qed.

(* A reasoning rule for [orelse]. *)

Lemma total_orelse {A E} (m1 m2 : micro A E) φ ψ1 ψ :
  total m1 φ ψ1 →
  (∀ e, ψ1 e → total m2 φ ψ) →
  total (orelse m1 m2) φ ψ.
Proof.
  intros Hm1 H2. unfold orelse. eauto using total_try, total_ret.
Qed.

(* A reasoning rule for [bind]. *)

Lemma total_bind {A B E} m f
  (φ : B → Prop) (φ' : A → Prop) (ψ : E → Prop) :
  total m φ' ψ →
  (∀ a, φ' a → total (f a) φ ψ) →
  total (bind m f) φ ψ.
Proof.
  rewrite bind_as_try. eauto using total_try, total_throw.
Qed.

Lemma total_bind_unary {A B E} m f (φ : B → Prop) (ψ : E → Prop) :
  total m (λ (a : A), total (f a) φ ψ) ψ →
  total (bind m f) φ ψ.
Proof.
  eauto using total_bind.
Qed.

(* A reasoning rule for [par]. *)

(* This rule is limited to the case where [ψ] is [λ _, False]. Dealing with
   arbitrary [ψ] would require simplifying [Par (throw e) (throw e) _ _]
   into [throw e]. The relation [simp] currently does not allow this.
   Furthermore, such a rule would require [ψ] to be deterministic. *)

Lemma total_par {A1 A2 E} m1 m2 φ1 φ2 (φ : A1 * A2 → Prop) :
  let ψ := λ (e : E), False in
  total m1 φ1 ψ →
  total m2 φ2 ψ →
  (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
  total (par m1 m2) φ ψ.
Proof.
  intros.
  destruct_total a2 e2; destruct_total a1 e1; try solve [ exfalso; tauto ].
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

(* This rule is limited to the case where [ψ] is [λ _, False] because we
   cannot allow [m1] to raise an exception while [m2] terminates, or
   vice-versa. *)

Definition deterministic {A} (φ : A → Prop) :=
  ∀ a1 a2, φ a1 → φ a2 → a1 = a2.

Lemma total_choose {A E} m1 m2 (φ : A → Prop) :
  let ψ := λ (_ : E), False in
  total m1 φ ψ →
  total m2 φ ψ →
  deterministic φ →
  total (choose m1 m2) φ ψ.
Proof.
  intros.
  destruct_total a2 e2; destruct_total a1 e1; try solve [ exfalso; tauto ].
  assert (a1 = a2); [ eauto | subst ].
  eapply total_simp.
  eapply SimpChooseAgree; eassumption.
  eapply total_ret.
  eauto.
Qed.

(* The infinitary intersection rule. *)

(* If for every [x] one can prove that the result of [m] satisfies [φ x],
   then one can deduce that the result of [m] satisfies [φ x] for every
   [x] simultaneously. *)

Lemma total_intersection {A E} `{Inhabited X}
  m (φ : X → A → Prop) (ψ : E → Prop) :
  (∀ x, total m (φ x) ψ) →
  total m (λ a, ∀ x, φ x a) ψ.
Proof.
  intros Hm.
  (* Instantiate [Hm] with an arbitrary [x]. *)
  generalize (Hm inhabitant).
  intro Htotal. destruct_total a e.
  (* Case: there exists [a] such that [m] can be simplified to [ret a]. *)
  { left. exists a. split; [ eauto |].
    intro x. specialize (Hm x). destruct_total a' e';
    (* Because [simp _ _], restricted to final results, is confluent,
       the two results must be equal. *)
    simp_final_confluent; congruence. }
  (* Case: [m] can be simplified to [throw _]. *)
  { right. eauto. }
Qed.

(* The binary intersection rule. *)

(* If one can prove that the result of [m] satisfies [φ1]
   and if one can prove that the result of [m] satisfies [φ2]
   then one can deduce that the result of [m] satisfies [φ1] and [φ2]
   simultaneously. *)

Lemma total_binary_intersection {A E} m (φ1 φ2 : A → Prop) (ψ : E → Prop) :
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

(* Special cases of the above rules for [totalv]. *)

(* These rules may seem a bit trivial, but it is probably preferable to state
   them explicitly and have them at hand, rather than attempt to reconstruct
   them on the fly every time they are needed. *)

(* The reasoning rule for [ret _]. *)

Lemma totalv_ret {A E} a (φ : A → Prop):
  φ a →
  totalv (ret a : micro A E) φ.
Proof.
  unfold totalv. eauto using total_ret.
Qed.

(* The consequence rule. *)

Lemma totalv_consequence {A E} (m : micro A E) (φ φ' : A → Prop) :
  totalv m φ →
  (∀ a, φ a → φ' a) →
  totalv m φ'.
Proof.
  unfold totalv. eauto using total_consequence.
Qed.

(* The simplification rule. *)

Lemma totalv_simp {A E} (m m' : micro A E) (φ : A → Prop) :
  simp m m' →
  totalv m' φ →
  totalv m φ.
Proof.
  unfold totalv. eauto using total_simp.
Qed.

(* [simp m (ret a)] is equivalent to a Hoare logic judgement [totalv m _]
   whose postcondition is an equality [λ a', a = a']. *)

Lemma simp_totalv {A E} m (a : A) :
  simp m (ret a : micro A E) ↔
  totalv m (λ a', a = a').
Proof.
  split.
  { eauto using totalv_simp, totalv_ret. }
  { intros. destruct_total a' e'. congruence. }
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [throw _],
   so the handler [g] is dead and no proof obligation bears on it. *)

Lemma totalv_try {A B E' E} m f (g : E' → micro B E)
  (φ : B → Prop) (φ' : A → Prop) :
  totalv m φ' →
  (∀ a, φ' a → totalv (f a) φ) →
  totalv (try m f g) φ.
Proof.
  unfold totalv. intros.
  eapply total_try; try solve [ eauto | simpl; tauto ].
Qed.

(* A reasoning rule for [bind]. *)

Lemma totalv_bind {A B E} (m : micro A E) f (φ : B → Prop) (φ' : A → Prop) :
  totalv m φ' →
  (∀ a, φ' a → totalv (f a) φ) →
  totalv (bind m f) φ.
Proof.
  unfold totalv. eauto using total_bind.
Qed.

Lemma totalv_bind_unary {A B E} (m : micro A E) f (φ : B → Prop) :
  totalv m (λ (a : A), totalv (f a) φ) →
  totalv (bind m f) φ.
Proof.
  eauto using totalv_bind.
Qed.

(* A reasoning rule for [par]. *)

Lemma totalv_par {A1 A2 E} (m1 m2 : micro _ E) φ1 φ2 (φ : A1 * A2 → Prop) :
  totalv m1 φ1 →
  totalv m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
  totalv (par m1 m2) φ.
Proof.
  unfold totalv. eauto using total_par.
Qed.

(* A reasoning rule for [choose]. *)

Lemma totalv_choose {A E} (m1 m2 : micro A E) (φ : A → Prop) :
  totalv m1 φ →
  totalv m2 φ →
  deterministic φ →
  totalv (choose m1 m2) φ.
Proof.
  unfold totalv. eauto using total_choose.
Qed.

(* The infinitary intersection rule. *)

Lemma totalv_intersection {A E} `{Inhabited X} (m : micro A E) (φ : X → A → Prop) :
  (∀ x, totalv m (φ x)) →
  totalv m (λ a, ∀ x, φ x a).
Proof.
  unfold totalv. eauto using total_intersection.
Qed.

(* The binary intersection rule. *)

Lemma totalv_binary_intersection {A E} (m : micro A E) (φ1 φ2 : A → Prop) :
  totalv m φ1 →
  totalv m φ2 →
  totalv m (λ a, φ1 a ∧ φ2 a).
Proof.
  unfold totalv. eauto using total_binary_intersection.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now prepare to prove the reciprocal bind rule, that is,
   the reverse implication of the lemma [total_bind_unary]. *)

(* -------------------------------------------------------------------------- *)

(* To do so, we need another indexed variant of the relation [simp].

   The relation [sss] is identical to [simplify], except that it places a
   weight of 1 on transitivity nodes, where [simplify] assigns them zero
   cost. This weight of 1 is needed in the last case of the proof of the
   lemma [invert_stack_try_ret]. *)

Inductive sss {A E : Type} : nat → micro A E → micro A E → Prop :=
| SssEval:
    ∀ p η e k z,
    p = (η, e) →
    sss 1
      (Stop CEval p k z)
      (try (eval η e) k z)
| SssLoop :
    ∀ p η x i1 i2 e k z,
    p = (η, x, i1, i2, e) →
    sss 1
      (Stop CLoop p k z)
      (try (loop η x i1 i2 e) k z)
| SssChooseAgree :
    ∀ {B E'} n1 n2 m m1 m2 (k : B → _) (z : E' → _),
    sss n1 m1 m →
    sss n2 m2 m →
    sss (n1 + n2 + 1)
      (Choose m1 m2 k z)
      (try m k z)
| SssParRetLeft:
    ∀ {A1 A2 E'} a1 m2 (k : A1 * A2 → _) (z : E' → _),
    sss 1
      (Par (Ret a1) m2 k z)
      (try m2 (λ v2, k (a1, v2)) z)
| SssParRetRight:
    ∀ {A1 A2 E'} m1 a2 (k : A1 * A2 → _) (z : E' → _),
    sss 1
      (Par m1 (Ret a2) k z)
      (try m1 (λ v1, k (v1, a2)) z)
| SssPar:
    ∀ {A1 A2 E'} n1 n2 n m1 m'1 m2 m'2 (k : A1 * A2 → _) (z : E' → _),
    sss n1 m1 m'1 →
    sss n2 m2 m'2 →
    n1 + n2 < n →
    sss n (Par m1 m2 k z) (Par m'1 m'2 k z)
| SssReflexive:
    ∀ m,
    sss 0 m m
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

Local Lemma sss_simp {A E n} {m m' : micro A E} :
  sss n m m' →
  simp m m'.
Proof.
  induction 1; subst; eauto with simp.
Qed.

Local Lemma simp_sss {A E} {m m' : micro A E} :
  simp m m' →
  ∃ n, sss n m m'.
Local Ltac baz :=
  match goal with h: ∃ n, sss n _ _ |- _ => destruct h end.
Proof.
  induction 1; try solve [ repeat baz; eauto with lia sss ].
Qed.

(* -------------------------------------------------------------------------- *)

(* A stack of simplification trees is needed in the statement of the lemma
   [invert_stack_try_ret]. *)

(* One can think of this stack as an evaluation context. Although there is
   no syntax for evaluation contexts, because the [micro] monad is a shallow
   embedding, making evaluation contexts explicit, and controlling their
   weight, is required here. *)

Inductive stack {A E : Type} : nat → micro A E → micro A E → Prop :=
| StackNil:
    forall n m,
    0 ≤ n →
    stack n m m
| StackCons:
    forall n1 n2 n m1 m2 m3,
    sss n1 m1 m2 →
    stack n2 m2 m3 →
    0 < n1 →
    n1 + n2 ≤ n →
    stack n m1 m3.

Local Hint Constructors stack : stack.

(* -------------------------------------------------------------------------- *)

(* In [stack n m m'], the parameter [n] is an over-approximation of the
   weight of the stack, which itself is the sum of the weights of the
   trees in the stack. *)

Local Lemma stack_monotone {A E} n (m m' : micro A E) :
  ∀ n',
  stack n m m' →
  n ≤ n' →
  stack n' m m'.
Proof.
  induction 1; intros; econstructor; eauto with lia.
Qed.

(* [sss 0 m1 m2] implies [m1 = m2]. *)

Lemma invert_sss_zero {A E} {m1 m2 : micro A E} :
  sss 0 m1 m2 →
  m1 = m2.
Proof.
  intros h; dependent induction h; eauto with lia f_equal.
Qed.

(* The side condition [0 < n1] in [StackCons] is not restrictive. *)

Lemma StackConsUnrestricted {A E} n1 n2 n (m1 m2 m3 : micro A E) :
  sss n1 m1 m2 →
  stack n2 m2 m3 →
  n1 + n2 ≤ n →
  stack n m1 m3.
Proof.
  intros H1 H2 ?.
  assert (0 = n1 ∨ 0 < n1) as [|] by lia; [ subst |].
  { apply invert_sss_zero in H1. subst.
    eauto using stack_monotone with lia. }
  eauto with stack.
Qed.

Local Hint Resolve StackConsUnrestricted : stack.

(* A single tree forms a stack (of one cell). *)

Lemma sss_stack {A E} n (m m' : micro A E) :
  sss n m m' →
  stack n m m'.
Proof.
  eauto with stack lia.
Qed.

(* A stack represents a simplification path. *)

Lemma stack_simp {A E n} {m m' : micro A E} :
  stack n m m' →
  simp m m'.
Proof.
  induction 1; eauto using sss_simp with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* The main lemma. *)

(* If [try m m h] can be simplified to [ret b]
   via a stack of weight [n],
   then:
   - either [m] can be simplified to [ret a]
     for some [a] such that
     [k a] can be simplified to [ret b]
     via a stack of weight [n],
   - or [m] can be simplified to [throw e]
     and [h e] can be simplified to [ret b]
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
  ∀ n {A B E' E} m (k : A → micro B E) (h : E' → _) b,
  stack n (try m k h) (ret b) →
  total m
    (λ a, stack n (k a) (ret b))
    (λ e, stack n (h e) (ret b)).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).

  (* Reformulate the induction hypothesis by weakening it so that its
     conclusion mentions [n] instead of [i]. Also, place the side
     condition [i < n] in the last position. *)
  assert (IHw :
    ∀ i {A B E' E} m (k : A → micro B E) (h : E' → _) b,
    stack i (try m k h) (ret b) →
    i < n →
    total m
      (λ a, stack n (k a) (ret b))
      (λ e, stack n (h e) (ret b))
  ).
  { intros. eapply total_consequence; intuition eauto using stack_monotone. }
  clear IH.

  (* Now begin the proof. *)
  intros A B E' E m k h b.
  intros Hstack.

  (* If [m] is [ret a] or [throw e], then the result is immediate. Treat
     these two cases now, so as to avoid treating them several times
     later on. *)
  destruct (ret_or_throw_or_else m) as [ (a & ?) | [ (e & ?) | (Hret & Hthrow) ]].
  (* Case: [m] is [ret a]. *)
  { subst m. simpl try in Hstack. eapply total_ret. eauto. }
  (* Case: [m] is [throw e]. *)
  { subst m. simpl try in Hstack. eapply total_throw. eauto. }
  (* We can now assume that [m] is neither [ret _] nor [throw _]. *)

  (* Is the stack empty? *)
  dependent destruction Hstack.
  (* Case: the stack is empty. *)
  { clear IHw. exfalso. eauto using invert_try_eq_ret. }
  (* Case: the stack is nonempty. Analyze its first element. *)
  match goal with h: sss _ _ _ |- _ => dependent destruction h end.

  (* Subcase: [SssEval]. *)
  { subst p.
    (* [m] is [Stop CEval _ _ _]. *)
    invert_try_eq_stop. subst m. clear Hret Hthrow.
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
    invert_try_eq_stop. subst m. clear Hret Hthrow.
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
    invert_try_eq_choose. subst m. clear Hret Hthrow.
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
    invert_try_eq_par. subst m. clear Hret Hthrow.
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
    invert_try_eq_par. subst m. clear Hret Hthrow.
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
    invert_try_eq_par. subst m. clear Hret Hthrow.
    (* Change [m1] to [m'1] and [m2] to [m'2] in the goal. *)
    eapply total_simp.
    { eapply SimpPar; eapply sss_simp; eauto. }
    (* Recognize [try (Par _ _ _ _) _ _] in the stack. *)
    rewrite <- try_Par in Hstack.
    (* Apply the induction hypothesis. *)
    eauto with lia.
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

Lemma invert_simp_try_ret {A B E' E} m (k : A → micro B E) (h : E' → _) b :
  simp (try m k h) (ret b) →
  total m
    (λ a, simp (k a) (ret b))
    (λ e, simp (h e) (ret b)).
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
  + simpl. eauto using stack_simp.
Qed.

(* The previous lemma can be specialized to obtain a result about [bind]. *)

Lemma invert_simp_bind_ret_totalv {A B E} m (k : A → micro B E) b :
  simp (bind m k) (ret b) →
  totalv m (λ a, simp (k a) (ret b)).
Proof.
  rewrite bind_as_try.
  intros h.
  unfold totalv.
  eapply total_consequence.
  { eauto using invert_simp_try_ret. }
  { eauto. }
  (* There remains to argue that [throw _] cannot reduce to [ret _]. *)
  { simpl. intros. clarify_simp. }
Qed.

(* Reformulating the previous result yields this statement. *)

(* This is the reciprocal bind rule for [totalv]. *)

Lemma invert_totalv_bind {A B E} m (k : A → micro B E) (φ : B → Prop) :
  totalv (bind m k) φ →
  totalv m (λ a, totalv (k a) φ).
Proof.
  intros.
  destruct_total b e.
  apply invert_simp_bind_ret_totalv in H.
  destruct_total a e.
  eauto using totalv_simp, totalv_ret.
Qed.

(* Another reformulation yields this alternative statement. *)

(* This is the reciprocal bind rule for [simp]. *)

Lemma invert_simp_bind_ret {A B E} m (k : A → micro B E) b :
  simp (bind m k) (ret b) →
  ∃ a, simp m (ret a) ∧ simp (k a) (ret b).
Proof.
  intros h. apply invert_simp_bind_ret_totalv in h.
  destruct_total a e. eauto.
Qed.
