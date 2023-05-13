From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.

(* This file defines a simplification relation: [simplify m m'] means that
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
     [∃ a, simplify m (ret a) ∧ P a].

     Such a specification implies [WP m (λa, ⌜ P a ⌝)], so a pure program
     is a special case of a possibly-impure program. *)

(* -------------------------------------------------------------------------- *)

(* The simplification relation is inductively defined as follows. *)

(* The constructors [SimplifyEval], [SimplifyLoop], [SimplifyFlip] allow
   certain [Stop] events to be replaced with their meaning. [SimplifyFlip]
   requires [k false = k true], which means that it is applicable only in
   the special case where the final outcome of the computation is
   independent of the coin flip. (This is useful; e.g., it allows OCaml's
   [assert] construct to be regarded pure.)

   Two constructors [SimplifyParRetLeft] and [SimplifyParRetRight] simplify
   a [par] construct where at least one side is [ret _]. These steps are not
   reduction steps: that is, [simplify] is not a subrelation of [step].

   The constructors [SimplifyParLeft] and [SimplifyParRetRight] allow
   simplification to take place under a [Par] constructor. *)

Inductive simplify {A : Type} : free A → free A → Prop :=
| SimplifyEval:
    ∀ η e k,
    simplify
      (Stop CEval (η, e) k)
      (bind (eval η e) k)
| SimplifyLoop :
    ∀ η x i1 i2 e k,
    simplify
      (Stop CLoop (η, x, i1, i2, e) k)
      (bind (loop η x i1 i2 e) k)
| SimplifyFlip :
    ∀ x k m,
    k false = m →
    k true = m →
    simplify
      (Stop CFlip x k)
      m
| SimplifyParRetLeft:
    ∀ {A1 A2} (a1 : A1) (m2 : free A2) k,
    simplify
      (Par (Ret a1) m2 k next)
      (v2 ← m2 ; k (a1, v2))
| SimplifyParRetRight:
    ∀ {A1 A2} (m1 : free A1) (a2 : A2) k,
    simplify
      (Par m1 (Ret a2) k next)
      (v1 ← m1 ; k (v1, a2))
| SimplifyParLeft:
    ∀ {A1 A2} m1 m'1 m2 (k : A1 * A2 → free A) ko,
    simplify m1 m'1 →
    simplify (Par m1 m2 k ko) (Par m'1 m2 k ko)
| SimplifyParRight:
    ∀ {A1 A2} m1 m2 m'2 (k : A1 * A2 → free A) ko,
    simplify m2 m'2 →
    simplify (Par m1 m2 k ko) (Par m1 m'2 k ko)
.

Global Hint Constructors simplify : simplify.

(* Of course, if both sides of a [par] combinator are of the form [ret _],
   then it can be simplified. *)

Lemma simplify_par_ret_ret {A1 A2 A} a1 a2 (k : A1 * A2 → free A) :
  simplify
    (Par (Ret a1) (Ret a2) k next)
    (k (a1, a2)).
Proof.
  constructor.
Qed.

(* Simplification is compatible with [bind]. *)

Lemma simplify_bind {A B} (m1 m2 : free A) (f : A → free B) :
  simplify m1 m2 →
  simplify (bind m1 f) (bind m2 f).
Proof.
  induction 1; simpl; rewrite ?bind_bind; econstructor; eauto with congruence.
Qed.

Local Hint Constructors rtc : rtc.

Local Lemma rtc_simplify_bind {A B} (m1 m2 : free A) (f : A → free B) :
  rtc simplify m1 m2 →
  rtc simplify (bind m1 f) (bind m2 f).
Proof.
  induction 1; eauto using simplify_bind with rtc.
Qed.

(* A destruction tactic. *)

Ltac destruct_simplify :=
  match goal with h: simplify _ _ |- _ => dependent destruction h end.

(* -------------------------------------------------------------------------- *)

(* The relation [maybe simplify], which allows zero or one simplification
   step, is used in the statement of the main simulation lemma. It can be
   informally written [simplify?]. *)

Definition maybe {A} (R : A → A → Prop) : A → A → Prop :=
  λ x y, x = y ∨ R x y.

Local Hint Unfold maybe : simplify.

(* [simplify?] is preserved by [Par]. *)

Lemma maybe_simplify_par_left
  {A1 A2 A} m1 m'1 m2 (k : A1 * A2 → free A) ko :
  maybe simplify m1 m'1 →
  maybe simplify (Par m1 m2 k ko) (Par m'1 m2 k ko).
Proof.
  intros [|]; [ left; congruence | eauto with simplify ].
Qed.

Lemma maybe_simplify_par_right
  {A1 A2 A} m1 m2 m'2 (k : A1 * A2 → free A) ko :
  maybe simplify m2 m'2 →
  maybe simplify (Par m1 m2 k ko) (Par m1 m'2 k ko).
Proof.
  intros [|]; [ left; congruence | eauto with simplify ].
Qed.

Local Hint Resolve
  maybe_simplify_par_left
  maybe_simplify_par_right
: simplify.

(* -------------------------------------------------------------------------- *)

(* The following simulation diagram claims that if out of [(σ, m1)] there is
   both a simplification step and a semantic reduction step, then:

   - either these two steps coincide;

   - or they commute, in which case the diagram can be closed via
     one semantic reduction step and at most one simplification step.

   Technically, this means that [simplify?] is a (strong) simulation.

   Intuitively, this means that applying a simplification step never
   causes the loss of a reduction step. In other words, applying a
   simplification step does not eliminate any permitted behavior. *)

Lemma simplify_step_diagram {A} {m1 m2 : free A} :
  (* If there is a simplification step: *)
  simplify m1 m2 →
  ∀ {m'1 σ σ'},
  (* and a semantic step: *)
  step (σ, m1) (σ', m'1) →
  (* then either the two steps coincide: *)
  (σ' = σ ∧ m'1 = m2) ∨
  (* or they commute: *)
  (∃ m'2, step (σ, m2) (σ', m'2) ∧ maybe simplify m'1 m'2).
Proof.
  induction 1; intros.
  (* SimplifyEval *)
  { destruct_step. left; eauto. }
  (* SimplifyLoop *)
  { destruct_step. left; eauto. }
  (* SimplifyFlip *)
  (* This is where [k false = k true] is exploited. *)
  { destruct_step. left; destruct b; eauto. }
  (* SimplifyParRetLeft *)
  { destruct_step; try solve [
      exfalso; destruct_step
    | left; eauto
    | right; eexists; split; eauto using step_bind with simplify
    ]. }
  (* SimplifyParRetRight *)
  { destruct_step; try solve [
      exfalso; destruct_step
    | left; eauto
    | right; eexists; split; eauto using step_bind with simplify
    ]. }
  (* SimplifyParLeft *)
  { destruct_step; try solve [
      exfalso; destruct_simplify
    | eauto 9 with step simplify
    ].
    (* StepParLeft *)
    match goal with Hstep: step _ _ |- _ =>
      destruct (IHsimplify _ _ _ Hstep) as [ (? & ?) | (? & ? & ?) ]
    end;
    subst; eauto 6 with step simplify. }
  (* SimplifyParRight *)
  { destruct_step; try solve [
      exfalso; destruct_simplify
    | eauto 9 with step simplify
    ].
    (* StepParRight *)
    match goal with Hstep: step _ _ |- _ =>
      destruct (IHsimplify _ _ _ Hstep) as [ (? & ?) | (? & ? & ?) ]
    end;
    subst; eauto 6 with step simplify. }
Qed.

(* In the special case where [m2] is of the form [ret a2], the previous
   diagram can be simplified, since [ret a2] cannot step. *)

Lemma simplify_ret_step_diagram {A} {m1 : free A} {a2 σ σ' m'1} :
  (* If there is a simplification step [simplify m1 (ret a2)]: *)
  simplify m1 (ret a2) →
  (* and a semantic step: *)
  step (σ, m1) (σ', m'1) →
  (* then the two steps coincide: *)
  σ' = σ ∧ m'1 = ret a2.
Proof.
  intros Hsimp Hstep.
  pose proof (simplify_step_diagram Hsimp Hstep) as [| (? & ? & ?) ];
    [ eauto | destruct_step ].
Qed.

(* The following lemma is currently not used, but seems instructive. *)

(* If there is a simplification step from [m1] to [ret a2],
   then this step is also a reduction step.
   By the previous lemma, it is then the only possible step. *)

Lemma simplify_ret_implies_step {A} (m1 m2 : free A) :
  simplify m1 m2 →
  ∀ σ a2,
  m2 = ret a2 →
  step (σ, m1) (σ, m2).
Proof.
  induction 1; intros σ ? Hm2; try solve [ congruence | eauto with step ].
  { subst. eauto with step. }
  { destruct m2; simpl in *; solve [ congruence | eauto with step ]. }
  { destruct m1; simpl in *; solve [ congruence | eauto with step ]. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas transport information in the reverse direction
   along the simplification relation. If [simplify m1 m2] holds, then
   information about [m2] can be transported to [m1]. *)

(* If [m1] can be simplified into [ret a2] then [m1] can step. *)

Lemma invert_simplify_ret {A} σ (m1 : free A) a2 :
  simplify m1 (ret a2) →
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are [Ret] and [Crash] and [Next], and
     these terms cannot appear on the left-hand side of [simplify], so the
     proof is trivial. *)
  inversion 1; intros; eauto with step.
Qed.

(* If [m1] can be simplified into [m2], and if [m2] can step,
   then [m1] can step. *)

Lemma invert_simplify_can_step {A} (m1 m2 : free A) σ :
  simplify m1 m2 →
  can_step (σ, m2) →
  can_step (σ, m1).
Proof.
  (* The only terms that cannot step are [Ret] and [Crash] and [Next], and
     these terms cannot appear on the left-hand side of [simplify], so the
     proof is trivial. *)
  induction 1; eauto with step.
Qed.

(* -------------------------------------------------------------------------- *)

(* The parallel simplification relation is inductively defined as follows. *)

(* We prove that parallel simplification is the reflexive transitive closure
   of simplification. Parallel simplification is intended to allow a maximum
   amount of simplification in just one step. *)

Inductive psimplify {A : Type} : free A → free A → Prop :=
| PSimplifyReflexive:
    ∀ m,
    psimplify m m
| PSimplifyEval:
    ∀ η e k m',
    psimplify (bind (eval η e) k) m' →
    psimplify (Stop CEval (η, e) k) m'
| PSimplifyLoop:
    ∀ η x i1 i2 e k m',
    psimplify (bind (loop η x i1 i2 e) k) m' →
    psimplify (Stop CLoop (η, x, i1, i2, e) k) m'
| PSimplifyFlip :
    ∀ x k m m',
    k false = m →
    k true = m →
    psimplify m m' →
    psimplify (Stop CFlip x k) m'
| PSimplifyParRetRet:
    ∀ {A1 A2} (a1 : A1) (a2 : A2) k m',
    psimplify (k (a1, a2)) m' →
    psimplify (Par (Ret a1) (Ret a2) k next) m'
| PSimplifyParRetLeft:
    ∀ {A1 A2} (a1 : A1) (m2 m'2 : free A2) k m',
    psimplify m2 m'2 →
    psimplify (v2 ← m'2 ; k (a1, v2)) m' →
    psimplify (Par (Ret a1) m2 k next) m'
| PSimplifyParRetRight:
    ∀ {A1 A2} (m1 m'1 : free A1) (a2 : A2) k m',
    psimplify m1 m'1 →
    psimplify (v1 ← m'1 ; k (v1, a2)) m' →
    psimplify (Par m1 (Ret a2) k next) m'
| SimplifyPar:
    ∀ {A1 A2} m1 m'1 m2 m'2 (k : A1 * A2 → free A) ko m',
    psimplify m1 m'1 →
    psimplify m2 m'2 →
    psimplify (Par m'1 m'2 k ko) m' →
    psimplify (Par m1 m2 k ko) m'
.

Global Hint Constructors psimplify : psimplify.

(* Parallel simplification contains simplification. *)

Lemma simplify_psimplify {A} (m1 m2 : free A) :
  simplify m1 m2 →
  psimplify m1 m2.
Proof.
  induction 1; eauto with psimplify.
Qed.

(* Parallel simplification is transitive. *)

Lemma psimplify_transitive {A} (m1 m2 : free A) :
  psimplify m1 m2 →
  ∀ m3,
  psimplify m2 m3 →
  psimplify m1 m3.
Proof.
  induction 1; intros ? Hsimp; eauto with psimplify.
Qed.

(* Parallel simplification is the reflexive transitive closure of
   simplification. *)

Local Lemma rtc_simplify_par_left :
  ∀ {A1 A2 A} m1 m'1 m2 (k : A1 * A2 → free A) ko,
  rtc simplify m1 m'1 →
  rtc simplify (Par m1 m2 k ko) (Par m'1 m2 k ko).
Proof.
  induction 1; eauto with rtc simplify.
Qed.

Local Lemma rtc_simplify_par_right :
  ∀ {A1 A2 A} m1 m2 m'2 (k : A1 * A2 → free A) ko,
  rtc simplify m2 m'2 →
  rtc simplify (Par m1 m2 k ko) (Par m1 m'2 k ko).
Proof.
  induction 1; eauto with rtc simplify.
Qed.

Lemma psimplify_rtc_simplify {A} (m1 m2 : free A) :
  psimplify m1 m2 →
  rtc simplify m1 m2.
Proof.
  induction 1;
  eauto using
    rtc_transitive,
    rtc_simplify_par_left,
    rtc_simplify_par_right,
    rtc_simplify_bind
  with rtc simplify.
Qed.
