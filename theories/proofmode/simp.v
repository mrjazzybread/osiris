From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality.

(* A pure computation is terminating, deterministic, and does not use
   mutable state. *)

(* This file offers lemmas and tactics that help simplify computations,
   that is, solve goals of the form [simp m1 ?m2]. *)

(* -------------------------------------------------------------------------- *)

(* Opacity control. *)

(* [force_unfold_at_1 x] unfolds the first occurrence of [x]
   and works even if [x] is opaque. *)

Ltac force_unfold_at_1 x :=
  with_strategy transparent [x] unfold x at 1.

(* [force_unfold x] unfolds all occurrences of [x]
   and works even if [x] is opaque. *)

Ltac force_unfold x :=
  with_strategy transparent [x] unfold x.

(* [unfold_breakpoint m] determines whether the computation [m] is stopped
   at a "breakpoint" and if so, performs an unfolding so as to move the
   goal past the breakpoint.

   Currently, a breakpoint is a computation that is blocked because of an
   invocation of [ret_concat] or [ret_dconcat]. We allow this invocation
   to appear either at the root or in the left-hand side of [bind]. We do
   not need to look under multiple [bind]s because a normalized goal does
   not contain left-nested [bind]s. *)

Ltac unfold_breakpoint m :=
  lazymatch m with
  | ret_concat _ _ =>
      force_unfold_at_1 ret_concat
  | ret_dconcat _ _ =>
      force_unfold_at_1 ret_dconcat
  | bind (ret_concat _ _) _ =>
      force_unfold_at_1 ret_concat
  | bind (ret_dconcat _ _) _ =>
      force_unfold_at_1 ret_dconcat
  | _ =>
      fail "Not at a breakpoint" (* TODO improve message *)
  end.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are reasoning rules for goals of the form [simp _ _]. *)

Lemma prove_simp_ret {A} (a1 a2 : A) :
  a1 = a2 →
  simp (ret a1) (ret a2).
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma prove_simp_ret_encode `{Encode A} v (x : A) :
  v = #x →
  simp (ret v) (ret #x).
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma prove_simp_downto_ret {A} m1 (a2 : A) :
  m1 = ret a2 →
  simp m1 (ret a2).
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma prove_simp_bind {A B m m' a} {f : A → free B} :
  simp m (ret a) →
  simp (f a) m' →
  simp (bind m f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

Lemma prove_simp_try {A B m m' a} {f : A → free B} ko :
  simp m (ret a) →
  simp (f a) m' →
  simp (try m f ko) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.

Lemma simp_tail_call {A} (m : free A) m' :
  simp m m' →
  simp (bind m ret) m'.
Proof.
  rewrite bind_ret_right. eauto.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma simp_enter_call_VClo η a v2 m :
  simp (acall η a v2) m →
  simp (call (VClo η a) v2) m.
Proof.
  tauto.
Qed.

Lemma simp_enter_call_VCloRec η rbs g v2 m :
  simp (
    let δ := eval_rec_bindings η rbs in
    let η := concat δ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) m →
  simp (call (VCloRec η rbs g) v2) m.
Proof.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas are used by the [simp] tactic. *)

(* They are trivial. They could be replaced by nested applications of
   constructors, possibly complemented with [rewrite] steps. Using lemmas
   is somewhat more robust and should give rise to smaller proof terms. *)

Lemma simp_reflexive {A} (m1 m2 : free A) :
  m1 = m2 →
  simp m1 m2.
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma advance_SimpEval {A} η e (k : val → free A) ko m' :
  simp (try (eval η e) k ko) m' →
  simp (Stop CEval (η, e) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpEvalNext {A} η e (k : val → free A) m' :
  simp (bind (eval η e) k) m' →
  simp (Stop CEval (η, e) k next) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpLoop {A} η x i1 i2 e (k : val → free A) ko m' :
  simp (try (loop η x i1 i2 e) k ko) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpLoopNext {A} η x i1 i2 e (k : val → free A) m' :
  simp (bind (loop η x i1 i2 e) k) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k next) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpFlipOK x k ko :
  simp (k false) ok →
  simp (k true) ok →
  simp (Stop CFlip x k ko) ok.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpBindRet {A B} v (f : A → free B) m' :
  simp (f v) m' →
  simp (bind (ret v) f) m'.
Proof.
  eauto.
Qed.

Lemma advance_SimpBind {A B} m1 m2 (f : A → free B) m' :
  simp m1 m2 →
  simp (bind m2 f) m' →
  simp (bind m1 f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

Lemma advance_SimpParRetRet {A1 A2 A} a1 a2 (k : A1 * A2 → free A) ko m' :
  simp (k (a1, a2)) m' →
  simp (Par (Ret a1) (Ret a2) k ko) m'.
Proof.
  eauto using SimpParRetRet with simp.
Qed.

Lemma advance_SimpParRetLeft {A1 A2 A} a1 m2 (k : A1 * A2 → free A) ko m' :
  simp (try m2 (λ v2, k (a1, v2)) ko) m' →
  simp (Par (Ret a1) m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetRight {A1 A2 A} m1 a2 (k : A1 * A2 → free A) ko m' :
  simp (try m1 (λ v1, k (v1, a2)) ko) m' →
  simp (Par m1 (Ret a2) k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetLeftNext {A1 A2 A} a1 m2 (k : A1 * A2 → free A) m' :
  simp (v2 ← m2 ; k (a1, v2)) m' →
  simp (Par (Ret a1) m2 k next) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetLeft.
Qed.

Lemma advance_SimpParRetRightNext {A1 A2 A} m1 a2 (k : A1 * A2 → free A) m' :
  simp (v1 ← m1 ; k (v1, a2)) m' →
  simp (Par m1 (Ret a2) k next) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetRight.
Qed.

Lemma advance_SimpPar {A1 A2 A} m1 m'1 m2 m'2 (k : A1 * A2 → free A) ko m' :
  simp m1 m'1 →
  simp m2 m'2 →
  simp (Par m'1 m'2 k ko) m' →
  simp (Par m1 m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma val_as_bool_VTrue :
  val_as_bool VTrue = ret true.
Proof.
  reflexivity.
Qed.

Lemma val_as_bool_VFalse :
  val_as_bool VFalse = ret false.
Proof.
  reflexivity.
Qed.

Lemma val_as_bool_VBool b :
  val_as_bool (VBool b) = ret b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma simp_as_bool (x : bool) (m : free val) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma simp_as_int (x : Z) (m : free val) :
  simp m (ret #x) →
  simp (as_int m) (ret (repr x)).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

(* This lemma gives the user a chance to prove that the actual argument
   [v'2] is in fact the encoding of some value [x]. The subgoal [v'2 = #x]
   is typically solved by the tactic [encode]. Solving this subgoal
   instantiates both the metavariable [x] and the metavariable [X], which is
   the type of [x]. *)

Lemma simp_call `{Encode X} v1 v'2 (x : X) m' :
  v'2 = #x →
  simp (call v1 #x) m' →
  simp (call v1 v'2) m'.
Proof.
  intros. subst. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* We systematically use [simply eapply] as opposed to [eapply], because
   the latter does not respect opacity. (It is stronger than we wish.) *)

Create HintDb simp_specs.

(* [simp_ret] expects of the goal of the form [simp (ret ?a1) (ret ?a2)].
   It reduces this goal to the equality [a1 = a2], and attempts to prove
   this equality. It leaves zero or one subgoal. *)

Ltac simp_ret :=
  simple eapply prove_simp_ret; [ eauto with encode equality ].
    (* TODO limit search depth? *)

(* The tactic [normalize] attempts to reduce and normalize the goal before
   applying any reasoning rule. It is used by the tactics that follow. *)

(* This tactic has the property that if a term is normalized then its
   subterms are normalized as well. This property is exploited below;
   when a term is decomposed, it is not necessary to normalize again. *)

Ltac normalize :=
  cbn;
  rewrite ?true_iff, ?false_iff in *; (* TODO expensive? *)
  rewrite ?bind_bind. (* TODO may wish to rewrite at the root only. *)

(* [simp_close] solves a goal of the form [simp m1 m2] using reflexivity.

   The term [m1] must be normalized.

   If reflexivity cannot solve the goal, then [close] fails. *)

Ltac simp_close :=
  solve [
    simple eapply SimpReflexive
  | simple eapply prove_simp_ret_encode; [ encode ]
  | simp_ret
  ].

(* [simp_solve_eauto] solves a goal of the form [simp m _].

   The term [m] must be normalized.

   The tactic exploits whatever hypotheses are present in the context and in
   the hint database [simp_specs]. Of course the lemma [SimpReflexive] must
   not appear in this database; we want to make real progress.

   [m] is typically of the form [call v #x] or perhaps [eval η e]. *)

Ltac simp_solve_eauto :=
  solve [ eauto with simp_specs encode typeclass_instances ].

(* [fail_if_goal_contains_eval'] fails if the goal contains an occurrence
   of [eval']. It does nothing otherwise. *)

Ltac fail_if_goal_contains_eval' :=
  lazymatch goal with |- context[eval'] => fail | _ => idtac end.

(* [simp_eval] rewrites [eval] to [eval'], then normalizes the goal,
   hopefully expanding [eval'] away. It checks that [eval'] has indeed
   been eliminated, and fails otherwise. *)

Ltac simp_eval :=
  rewrite eval_eval';
  normalize;
  fail_if_goal_contains_eval'.

(* The tactics [simp0] and [simp1] expect a goal of the form [simp m1 m2].

   They advance this goal by performing simplification steps that lead from
   [m1] to [m'1] and by leaving a residual goal of the form [simp m'1 m2].

   Whereas [simp0] may find zero or more simplification steps, [simp1] must
   find at least one simplification step; otherwise, it fails.

   The term [m1] is expected to be normalized already.

   If the goal is changed to [simp m'1 m2] then the term [m'1] is guaranteed
   to be normalized.

   In some cases, the tactics are allowed to solve the goal. Of course this
   must be done only in situations where we are certain (or have reasonable
   grounds to believe) that the term has been simplified as far as possible
   and cannot be further simplified. *)

Ltac simp0 :=
  (* We are allowed to perform zero or more steps. *)
  (* Either perform at least one step, or perform zero step. *)
  try (simp1; simp0)

with simp1 :=
  (* We must perform at least one step. *)
  (* We examine the syntax of [m1], which is why we require [m1] to be
     normalized already. *)
  lazymatch goal with |- simp ?m1 _ =>
  lazymatch m1 with
  | ret ?a1 =>
      fail
  | lookup_name ?η ?x =>
      (* We may be able to prove [lookup_name η x = ret v], for some [v],
         by exploiting a hypothesis or a hint database. If so, we have
         made progress; we view this as a simplification step. *)
      simple eapply prove_simp_downto_ret; [
        (* subgoal: [m1 = ret v] *)
        solve [ eauto with simp_specs ]
      ]
  | val_as_bool ?v =>
      (* [val_as_bool] is opaque, so we treat it specially. *)
      first [
        rewrite val_as_bool_VTrue
      | rewrite val_as_bool_VFalse
      | rewrite val_as_bool_VBool
      ]; simp0
  | eval ?η ?e =>
      first [
        (* Attempt 1. Solve the goal by exploiting the hint database
           [simp_specs]. This can be necessary if the user chooses to
           populate the hint database with specifications about terms
           of the form [eval η e], as opposed to [call v1 v2]. *)
        simp_solve_eauto
      |
        (* Attempt 2. Rewrite [eval η e] to [eval' η e] and normalize the
           latter form, expanding [eval'] away. We count this as a
           simplification step, so our duty is fulfilled. We are then free
           to use [simp0] to find zero or more further steps. *)
        simp_eval;
        simp0
      ]
  | call ?v1 ?v2 =>
      first [
        simp_enter; simp0
      | simp1_call_reason v2
      ]
  | Stop CEval _ _ _ =>
      first [ simple eapply advance_SimpEvalNext | simple eapply advance_SimpEval ]; normalize;
      simp0
  | Stop CLoop _ _ _ =>
      first [ simple eapply advance_SimpLoopNext | simple eapply advance_SimpLoop ]; normalize;
      simp0
  | Stop CFlip _ _ _ =>
      simple eapply advance_SimpFlipOK; normalize;
      simp0
  | bind ?m ret =>
      (* A tail call can be simplified. *)
      simple eapply simp_tail_call; simp0
  | bind ?m ?f =>
      (* We want to first simplify the left-hand side of [bind], as far as
         possible; then, if possible, simplify the [bind] combinator away
         and further simplify the result. Two attempts are needed to ensure
         that we make one step of progress in at least one of the two
         subgoals. This should nevertheless be reasonably efficient. *)
      first [
        (* Attempt 1. Make progress on the left-hand side,
           and possibly more progress thereafter. *)
        simple eapply advance_SimpBind; [ simp1; simp_close | simp0_bind ]
      |
        (* Attempt 2. Make progress by eliminating this [bind],
           and possibly more progress thereafter. *)
        simp1_bind
      ]
  | try ?m ?f ?ko =>
      (* TODO treat [try] in the same way as [bind] *)
      simple eapply prove_simp_try; [ simp0; simp_close |];
      normalize; simp0
  | Par ?m1l ?m1r ?k ?ko =>
      (* We want to first simplify both sides of the [Par] independently, as
         far as possible; then, if possible, simplify the [Par] combinator
         away and further simplify the result. Three attempts are needed to
         ensure that we make one step of progress in at least one of the
         three subgoals. This should nevertheless be reasonably efficient. *)
      first [
        (* Attempt 1. Make progress on the left-hand side,
           and possibly more progress elsewhere. *)
        simple eapply advance_SimpPar; [ simp1; simp_close | simp0; simp_close | simp0_par ]
      |
        (* Attempt 2. Make progress on the right-hand side,
           and possibly more progress elsewhere. *)
        simple eapply advance_SimpPar; [ simp_close | simp1; simp_close | simp0_par ]
      |
        (* Attempt 3. Make progress by eliminating this [Par],
           and possibly more progress thereafter. *)
        simp1_par
      ]
  end end

(* [simp_enter] expects a goal of the form [simp (call _ _) _] and steps
   into the call. It leaves one (normalized) subgoal. *)

with simp_enter :=
  (* We intentionally use [eapply], not [simple eapply], so that [v1] can be
     unfolded on the fly if necessary. This is useful, e.g., when [v1] is a
     function in the standard library, such as [Stdlib__not]. *)
  first [
    eapply simp_enter_call_VClo
  | eapply simp_enter_call_VCloRec
  ];
  normalize

(* TODO comment *)
(* TODO this tactic leaves zero subgoal,
        but the comments say that it should leave one subgoal *)

with simp1_call_reason v2 :=
  lazymatch v2 with
  | #(?x2) =>
      (* The actual argument is already encoded. Fine. *)
      (* We reason about function calls using whatever hypotheses may be
         present in the context and in the hint database [simp_specs]. *)
      simp_solve_eauto
  | _ =>
      (* The actual argument is not yet encoded. It may or may not be
         necessary to encode it, depending on the specification on the
         function that is called. *)
      first [
        simp_solve_eauto
      | simple eapply simp_call; [ solve [ encode ] | simp_solve_eauto ]
      ]
  end

(* [simp0_bind] and [simp1_bind] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (bind m _) _],
   where [m] is normalized and cannot be simplified. *)

with simp0_bind :=
  first [
    (* Try to make progress. *)
    simp1_bind
  |
    (* If we cannot make progress, stop. Use [normalize] to ensure that
       the result is normalized; e.g., [rewrite bind_bind] can be useful
       here. *)
    normalize
  ]

with simp1_bind :=
  (* Performing at least one simplification step, when the term is a [bind]
     construct, requires rewriting [bind (ret _) _]. To do so, we explicitly
     apply a lemma; this ensures that we fail if the goal is not of the form
     [bind (ret _) _]. *)
  simple eapply advance_SimpBindRet;
  normalize; simp0

(* [simp0_par] and [simp1_par] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (Par m1 m2 _ _) _],
   where [m1] and [m2] are normalized and cannot be simplified. *)

with simp0_par :=
  try simp1_par

with simp1_par :=
  (* Performing at least one simplification step, when the term is a [Par]
     construct, requires applying one of the following rules. *)
  first [
    simple eapply advance_SimpParRetRet (* maybe a special case of the following *)
  | simple eapply advance_SimpParRetLeftNext
  | simple eapply advance_SimpParRetLeft
  | simple eapply advance_SimpParRetRightNext
  | simple eapply advance_SimpParRetRight
  ];
  normalize; simp0.

(* [simp] is the main public entry point into the above tactics. *)

(* [simp] proves or advances a goal of the form [simp m1 m2], where [m2] may
   be a metavariable. If [m2] is a metavariable then it is instantiated with
   a normalized term. *)

Ltac simp :=
  normalize;
  lazymatch goal with |- simp ?m1 _ =>
    simp0; try simp_close
  | _ =>
    fail "[simp] expects a goal of the form [simp _ _]"
  end.

(* [simp_really] is another public entry point into the above tactics. *)

(* [simp_really] proves a goal of the form [simp m1 m2], where [m2]
   must be a metavariable. [m2] is instantiated with a normalized
   term. [simp_really] performs at least one step of simplification.   *)

Ltac simp_really :=
  normalize;
  lazymatch goal with |- simp ?m1 _ =>
    simp1; simp_close
  | _ =>
    fail "[simp_really] expects a goal of the form [simp _ _]"
  end.

(* [simp_continue] unfolds an opaque definition and continues simplifying
   via [simp]. *)

Ltac simp_continue :=
  normalize;
  lazymatch goal with
  | |- simp ?m _ =>
      unfold_breakpoint m;
      simp
  | _ =>
      fail "[simp_continue] expects a goal of the form [simp _ _]"
  end.

(* [simp_enter_and_abstract] expects a goal of the form [simp (call v _) _],
   where [v] is a concrete closure (typically a recursive closure). It steps
   into the call, then abstracts away the closure [v], so as to make it
   opaque. *)

Ltac simp_call_enter_and_abstract :=
  lazymatch goal with |- simp (call ?v _) _ =>
    (* First, expand [call] away. *)
    simp_enter;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract values. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.

(* -------------------------------------------------------------------------- *)

(* The tactic [simp_specify x φ] should be used when the term begins with
   [bind (ret_concat δ η) _], that is, when the environment is about to be
   extended with the environment fragment [δ].

   The tactic looks up the variable [x] in the environment fragment [δ]
   so as to find the value [v] of this variable. Then, it produces two
   subgoals:
   - the subgoal [φ v],
     letting the user prove that [v] satisfies the specification [φ];
   - the original goal,
     generalized under the form [∀ v, φ v → ...],
     which means that [v] becomes an opaque value
     about which nothing is known except that [φ v] holds. *)

Ltac simp_specify x φ :=
  lazymatch goal with
    |- simp (bind (ret_concat ?δ _) _) _ =>
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* -------------------------------------------------------------------------- *)
