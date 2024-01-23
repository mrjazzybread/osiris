From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality.
From osiris.proofmode Require Import specifications.

(* A pure computation is terminating, deterministic, and does not use
   mutable state. *)

(* This file offers lemmas and tactics that help simplify computations,
   that is, solve goals of the form [simp m1 ?m2]. *)

(* -------------------------------------------------------------------------- *)

(* We do not want to unfold [val_as_bool] into a case analysis; that would be
   counter-productive, and could cause the tactics below to diverge.

   Note that [val_as_bool] is more problematic than [val_as_int] because
   integer values have their own tag [VInt], whereas Boolean values do not.
   [VBool] is just sugar, not a genuine tag. *)

Global Opaque val_as_bool.

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
   not need to look under multiple [bind]s because a simplified goal does
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

(* They are used by the tactics that follow. *)

(* [prove_simp_ret] reduces the goal to an equality between values [a1 = a2]. *)

Lemma prove_simp_ret {A E} (a1 a2 : A) :
  a1 = a2 →
  simp (ret a1 : micro A E) (ret a2).
Proof.
  intros. subst. eauto with simp.
Qed.

(* The Bind rule. *)

Lemma prove_simp_bind {A B E m m' a} {f : A → micro B E} :
  simp m (ret a) →
  simp (f a) m' →
  simp (bind m f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

(* The Try rule. *)

Lemma prove_simp_try {A B E' E m m' a} {f : A → micro B E} (h : E' → _) :
  simp m (ret a) →
  simp (f a) m' →
  simp (try m f h) m'.
Proof.
  eauto using simp_try with simp try_ret.
Qed.

(* -------------------------------------------------------------------------- *)

(* More lemmas for use by the tactics that follow. *)

(* These lemmas are trivial. They could be replaced by nested applications of
   constructors, possibly complemented with [rewrite] steps. Using lemmas is
   somewhat more robust and should give rise to smaller proof terms. *)

Lemma simp_reflexive {A E} (m1 m2 : micro A E) :
  m1 = m2 →
  simp m1 m2.
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma simp_reflexive_ret {A E} (m1 : micro A E) a2 :
  m1 = ret a2 →
  simp m1 (ret a2).
Proof.
  intros. subst. eauto with simp.
Qed.

Lemma advance_SimpEval {A E} η e (k : val → micro A E) z m' :
  simp (try (eval η e) k z) m' →
  simp (Stop CEval (η, e) k z) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpEvalThrow {A} η e (k : val → micro A void) m' :
  simp (bind (eval η e) k) m' →
  simp (Stop CEval (η, e) k throw) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpEvalRetThrow η e m' :
  simp (eval η e) m' ->
  simp (Stop CEval (η, e) ret throw) m'.
Proof.
  intros.
  by apply advance_SimpEvalThrow; rewrite bind_ret_right.
Qed.

Lemma advance_SimpEvalRetThrow' η e m' :
  simp (eval η e) m' →
  simp (stop CEval (η, e)) m'.
Proof.
  unfold stop. eauto using advance_SimpEvalRetThrow.
Qed.

Lemma advance_SimpLoop {A E} η x i1 i2 e (k : val → micro A E) z m' :
  simp (try (loop η x i1 i2 e) k z) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k z) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpLoopThrow {A} η x i1 i2 e (k : val → micro A void) m' :
  simp (bind (loop η x i1 i2 e) k) m' →
  simp (Stop CLoop (η, x, i1, i2, e) k throw) m'.
Proof.
  rewrite bind_as_try. eauto with simp.
Qed.

Lemma advance_SimpChooseAgree {A B E' E} m1 m2 m (k : A → micro B E) (z : E' → _) m' :
  simp m1 m →
  simp m2 m →
  simp (try m k z) m' →
  simp (Choose m1 m2 k z) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_simp_choose {A E} (m1 m2 : micro A E) m' :
  simp m1 m' →
  simp m2 m' →
  simp (choose m1 m2) m'.
Proof.
  intros. eapply advance_SimpChooseAgree; eauto.
  rewrite try_ret_right. eauto with simp.
Qed.

Lemma advance_SimpBind {A B E} m1 m2 (f : A → micro B E) m' :
  simp m1 m2 →
  simp (bind m2 f) m' →
  simp (bind m1 f) m'.
Proof.
  eauto using simp_bind with simp.
Qed.

Lemma advance_SimpTry {A B E' E} m1 m2 (f : A → micro B E) (h : E' → _) m' :
  simp m1 m2 →
  simp (try m2 f h) m' →
  simp (try m1 f h) m'.
Proof.
  eauto using simp_try with simp.
Qed.

Lemma advance_SimpParRetRet {A1 A2 A E' E}
  a1 a2 (k : A1 * A2 → micro A E) (z : E' → _) m'
:
  simp (k (a1, a2)) m' →
  simp (Par (Ret a1) (Ret a2) k z) m'.
Proof.
  eauto using SimpParRetRet with simp.
Qed.

Lemma advance_SimpParRetLeft {A1 A2 A E' E}
  a1 m2 (k : A1 * A2 → micro A E) (h : E' → _) m'
:
  simp (try m2 (λ v2, k (a1, v2)) h) m' →
  simp (Par (Ret a1) m2 k h) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetRight {A1 A2 A E' E}
  m1 a2 (k : A1 * A2 → micro A E) (h : E' → _) m'
:
  simp (try m1 (λ v1, k (v1, a2)) h) m' →
  simp (Par m1 (Ret a2) k h) m'.
Proof.
  eauto with simp.
Qed.

Lemma advance_SimpParRetLeftThrow {A1 A2 A E}
  a1 m2 (k : A1 * A2 → micro A E) m'
:
  simp (v2 ← m2 ; k (a1, v2)) m' →
  simp (Par (Ret a1) m2 k throw) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetLeft.
Qed.

Lemma advance_SimpParRetRightThrow {A1 A2 A E}
  m1 a2 (k : A1 * A2 → micro A E) m'
:
  simp (v1 ← m1 ; k (v1, a2)) m' →
  simp (Par m1 (Ret a2) k throw) m'.
Proof.
  rewrite bind_as_try. eauto using advance_SimpParRetRight.
Qed.

Lemma advance_SimpPar {A1 A2 A E' E}
  m1 m'1 m2 m'2 (k : A1 * A2 → micro A E) (z : E' → _) m'
:
  simp m1 m'1 →
  simp m2 m'2 →
  simp (Par m'1 m'2 k z) m' →
  simp (Par m1 m2 k z) m'.
Proof.
  eauto with simp.
Qed.

(* -------------------------------------------------------------------------- *)

(* More lemmas for use by the tactics that follow. *)

(* [val_as_bool] is opaque. to deal with it, we use the following lemmas. *)

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

Lemma advance_simp_val_as_bool_VTrue m' :
  simp (ret true) m' →
  simp (val_as_bool VTrue) m'.
Proof.
  rewrite val_as_bool_VTrue. tauto.
Qed.

Lemma advance_simp_val_as_bool_VFalse m' :
  simp (ret false) m' →
  simp (val_as_bool VFalse) m'.
Proof.
  rewrite val_as_bool_VFalse. tauto.
Qed.

Lemma advance_simp_val_as_bool_VBool b m' :
  simp (ret b) m' →
  simp (val_as_bool (VBool b)) m'.
Proof.
  rewrite val_as_bool_VBool. tauto.
Qed.

Lemma advance_simp_pure_spec_val_as_struct `{Σ: iprop.gFunctors} v a l P :
  @pure_spec Σ val (SpecModule a l P) v →
  simp (val_as_struct v) (Ret (val_as_struct_total v)).
Proof.
  intros H. pose proof H as (?&->&_).
  by erewrite pure_spec_val_as_struct.
Qed.

Lemma advance_simp_is_module_val_as_struct v Λ :
  is_module Λ v →
  simp (val_as_struct v) (Ret (val_as_struct_total v)).
Proof. intros?. by erewrite is_module_val_of_struct. Qed.


Lemma advance_simp_is_module_lookup_name v Λ n :
  is_module Λ v →
  In n Λ →
  simp (lookup_name (val_as_struct_total v) n)
       (Ret (lookup_name_total (val_as_struct_total v) n)).
Proof.
  intros??.
  by erewrite is_module_lookup_name_total.
Qed.

Lemma advance_simp_pure_spec_lookup_name `{Σ : iprop.gFunctors} v a l P n :
  @pure_spec Σ val (SpecModule a l P) v →
  In n (List.map fst l) →
  simp (lookup_name (val_as_struct_total v) n)
       (Ret (lookup_name_total (val_as_struct_total v) n)).
Proof.
  intros H?. pose proof H as (?&->&_).
  by erewrite pure_spec_lookup_total.
Qed.

(* -------------------------------------------------------------------------- *)

(* More lemmas for use by the tactics that follow. *)

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

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is a
   concrete closure (as opposed to a rigid metavariable), they step into the
   call.

   If [eapply] is used, as opposed to [simple eapply], then a definition can
   be unfolded on the fly: that is, the lemma can be applied to a goal of
   the form [simp (call c v2) m] where [c] is the name of a Coq toplevel
   definition.

   The trouble with [eapply], though, is that it does not respect opacity
   (i.e., it can unfold both transparent and opaque definitions).
   Furthermore, somewhat surprisingly, it can unfold and simplify further
   than is strictly necessary for the lemma to be applicable. *)

Lemma simp_enter_call_VClo η a v2 m :
  simp (acall η a v2) m →
  simp (call (VClo η a) v2) m.
Proof.
  tauto.
Qed.

Lemma simp_enter_call_VCloRec η rbs g v2 m :
  simp (
    let δ := eval_rec_bindings η rbs in
    let η := δ ++ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) m →
  simp (call (VCloRec η rbs g) v2) m.
Proof.
  tauto.
Qed.

(* This lemma replaces [eval] with [eval'] at the root of the goal. *)

Lemma advance_simp_eval η e m' :
  simp (eval' η e) m' →
  simp (eval  η e) m'.
Proof.
  rewrite eval_eval'. tauto.
Qed.

Lemma advance_SimpEvalEAssert η e :
  simp (eval η e) (ret #true) →
  simp (eval η (EAssert e)) ok.
Proof.
  intros.
  eapply advance_simp_eval. simpl eval'.
  (* Because of [choose], the runtime test may be skipped or executed.
     If it is skipped, then the result is immediate. If it is executed,
     then the assumption that [e] evaluates to [true] is exploited. *)
  eapply advance_simp_choose.
  { apply SimpReflexive. }
  unfold as_bool.
  rewrite bind_bind.
  eapply prove_simp_bind.
  { eauto. }
  eapply SimpReflexive.
Qed.

(* -------------------------------------------------------------------------- *)

(* More lemmas for use by the tactics that follow. *)

(* The following lemmas paraphrase the rewrite rules [ret_bind], [bind_ret],
   etc., and force the rule to be applied at the root of the goal. This is
   both safe and efficient (there is no need to scan the whole term). *)

Lemma advance_simp_bind_ret {A B E} (a : A) (f : A → micro B E) m' :
  simp (f a) m' →
  simp (bind (ret a) f) m'.
Proof.
  simpl bind. tauto.
Qed.

Lemma advance_simp_bind_ret_right {A E} (m : micro A E) m' :
  simp m m' →
  simp (bind m ret) m'.
Proof.
  rewrite bind_ret_right. eauto.
Qed.

Lemma advance_simp_try_ret {A B E' E} (a : A) (f : A → micro B E) (h : E' → _) m' :
  simp (f a) m' →
  simp (try (ret a) f h) m'.
Proof.
  rewrite try_ret. tauto.
Qed.

Lemma advance_simp_try_throw {A B E' E} x' (f : A → micro B E) (h : E' → _) m' :
  simp (h x') m' →
  simp (try (throw x') f h) m'.
Proof.
  simpl try. tauto.
Qed.

Lemma advance_simp_bind_as_try {A B E} m (f : A → micro B E) m' :
  simp (bind m f) m' →
  simp (try m f throw) m'.
Proof.
  rewrite bind_as_try. tauto.
Qed.

Lemma advance_simp_bind_bind
  {A B C E} (m : micro A E) (f : A → micro B E) (g : B → micro C E) m' :
  simp (bind m (λ a, bind (f a) g)) m' →
  simp (bind (bind m f) g) m'.
Proof.
  rewrite bind_bind. tauto.
Qed.

Lemma advance_simp_bind_try {A B C E' E}
  (m : micro A E') (f : A → micro B E) (g : B → micro C E) (h : E' → _) m' :
  simp (try m (λ a, bind (f a) g) (λ y, bind (h y) g)) m' →
  simp (bind (try m f h) g) m'.
Proof.
  rewrite bind_try. tauto.
Qed.

Lemma advance_simp_try_bind {A B C E}
  m (f : A → micro B E) (g : B → micro C E) h m'
:
  simp (try m (λ y, try (f y) g h) h) m' →
  simp (try (bind m f) g h) m'.
Proof.
  rewrite try_bind. tauto.
Qed.

Lemma advance_simp_try_try {A B C E'' E' E}
  (m : micro A E'') (f : A → micro B E') (g : B → micro C E) h h' m' :
  simp (try m (λ y, try (f y) g h') (λ y, try (h y) g h')) m' →
  simp (try (try m f h) g h') m'.
Proof.
  rewrite try_try. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Some properties of integer arithmetic. *)

(* [Is_true] is implicit in these statements. Its type is [bool → Prop]. *)

Lemma Zeq_spec (x y : Z) :
  (x =? y) ↔ (x = y).
Proof.
  rewrite Is_true_true, Z.eqb_eq. tauto.
Qed.

Lemma Zne_spec (x y : Z) :
  negb (x =? y) ↔ x ≠ y.
Proof.
  rewrite negb_True, Zeq_spec. tauto.
Qed.

Lemma Zlt_spec (x y : Z) :
  (x <? y) ↔ (x < y).
Proof.
  rewrite Is_true_true, Zlt_is_lt_bool. tauto.
Qed.

Lemma Zle_spec (x y : Z) :
  negb (y <? x) ↔ x ≤ y.
Proof.
  rewrite negb_True, Zlt_spec. lia.
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

(* The tactic [normalize] attempts to reduce and normalize the goal.
   It is used (as sparingly as possible) by the tactics that follow. *)

Ltac normalize :=
  cbn.

(* [simp_close] solves a goal of the form [simp m1 m2] using reflexivity.

   If reflexivity cannot solve the goal, then [simp_close] fails. *)
Global Hint Extern 1 (_ = _) => normalize : equality.

Ltac simp_close :=
  solve [
    simple eapply SimpReflexive
  | simp_ret
  ].

(* [simp_solve_eauto] solves a goal of the form [simp m _].

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

(* [simp_eval] rewrites [eval] to [eval'], then reduces the goal, hopefully
   expanding [eval'] away. It checks that [eval'] has indeed been
   eliminated, and fails otherwise. *)

Ltac simp_eval :=
  simple eapply advance_simp_eval;
  cbn; (* TODO or: [simpl eval']? *)
    (* TODO decide how much reduction must be done here, and how *)
  fail_if_goal_contains_eval'.
    (* TODO The goal could still contain [eval'] at this point if [eval']
       is applied to an opaque expression. There is currently an example
       of this in records_proof.v, where we do caller-side reasoning.
       We may abandon this style in the future. This expensive test
       could then become unnecessary. *)

(* The tactics [simp0] and [simp1] expect a goal of the form [simp m1 m2].

   They advance this goal by performing simplification steps that lead from
   [m1] to [m'1] and by leaving a residual goal of the form [simp m'1 m2].

   Whereas [simp0] may find zero or more simplification steps, [simp1] must
   find at least one simplification step; otherwise, it fails.

   The term [m1] has *not* necessarily been reduced (by [cbn], [simpl] or
   other means). If the tactics find that [m1] can be reduced, then they
   do so, and they are careful to perform reduction only where necessary:
   e.g. in the left-hand side of a [bind] but not in its right-hand side.

   In some cases, the tactics are allowed to solve the goal. Of course this
   must be done only in situations where we are certain (or have reasonable
   grounds to believe) that the term has been simplified as far as possible
   and cannot be further simplified. *)
Ltac simp0 :=
  (* We are allowed to perform zero or more steps. *)
  (* Either perform at least one step, or perform zero step. *)
  try simp1

with simp1 :=
  (* We must perform at least one step. *)
  (* We do not invoke Coq's reduction tactics ([cbn], [simpl], etc.) up front
     because they are not selective; they perform reduction everywhere in the
     goal. Instead, we first try to apply one of the following rewriting rules
     at the root of the goal: *)
  first [
    (* Exploit an assumption, if we have one. *)
    eassumption
    (* Transform [try] into [bind]. *)
  | simple eapply advance_simp_bind_as_try; simp0
    (* Perform tail call optimisation. (Not essential.) *)
  |  simple eapply advance_simp_bind_ret_right; simp0
    (* Hoist left-nested [bind]s and [try]s. *)
  | simple eapply advance_simp_bind_bind; simp0
  | simple eapply advance_simp_bind_try; simp0
  | simple eapply advance_simp_try_bind; simp0
  | simple eapply advance_simp_try_try; simp0
    (* Handle [Stop] effects. *)
  | simple eapply advance_SimpEvalRetThrow'; simp0
  | simple eapply advance_SimpEvalRetThrow; simp0
  | simple eapply advance_SimpEvalThrow; simp0
  | simple eapply advance_SimpEval; simp0
      (*| simple eapply advance_SimpLoopThrow; simp0 *)
      (*| simple eapply advance_SimpLoop; simp0 *)
  | simple eapply advance_SimpEvalEAssert; simp0
      (* We do not deal with [choose] in its full generality. Instead,
         we provide ad hoc support for [EAssert] expressions, which
         currently are the only place where [choose] is used. *)
    (* Handle [val_as_bool], which is opaque. *)
  | simple eapply advance_simp_val_as_bool_VTrue; simp0
  | simple eapply advance_simp_val_as_bool_VFalse; simp0
  | simple eapply advance_simp_val_as_bool_VBool; simp0

  | simple eapply advance_simp_is_module_val_as_struct; done
  | simple eapply advance_simp_is_module_lookup_name;
    [ done | by eauto using in_eq, in_cons ]

  | simple eapply advance_simp_pure_spec_val_as_struct; done
  | simple eapply advance_simp_pure_spec_lookup_name;
    [ done | by eauto using in_eq, in_cons ]

  (* TODO the following 4 rules are useful only in pre/postconditions,
     not in [simp] goals *)
  (*
  | rewrite -> Zeq_spec; simp0 (* x =? y ↔ x = y *)
  | rewrite -> Zne_spec; simp0 (* negb (x =? y) ↔ x ≠ y *)
  | rewrite -> Zlt_spec; simp0 (* x <? y ↔ x < y *)
  | rewrite -> Zle_spec; simp0 (* negb (y <? x) ↔ x ≤ y *)
   *)
    (* If none of the above rules can be applied, then we inspect the syntax
       of the goal and, based on it, we try to do something smart. *)
  | simp1_inspect
    (* As a last resort, if none of the above cases fire, it may be the case
       that we are facing a term that needs to be reduced by Coq. This could
       be, for instance, a pair deconstruction [let '(a, b) := t1 in t2], or
       an application of one the interpreter's auxiliary functions. We
       perform this reduction step only if it is nontrivial. *)
    (* One might wish to perform this reduction step only if it is nontrivial
       AND it enables at least one further simplification step. That would be
       expressed by using [simp1] instead of [simp0] below. However, that
       would be too restrictive. Indeed, this reduction step can lead us to a
       situation where a breakpoint is visible and no further simplification
       is possible. *)
    (* TODO is this a good idea? could this be very expensive? *)
  | progress normalize; simp0
  ]

(* Like [simp1], [simp1_inspect] expects a goal of the form [simp m1 _],
   and additionally expects that the term [m1] cannot be rewritten using
   any of the rewriting rules listed above. *)

with simp1_inspect :=
  (* Examine the syntax of [m1]. *)
  (* Note that we do *not* reduce [m1] before inspecting it. *)
  lazymatch goal with |- simp ?m1 _ =>
  lazymatch m1 with
  | ret ?a1 =>
      fail
  | lookup_name ?η ?x =>
      (* We may be able to prove [lookup_name η x = ret v], for some [v],
         either simply by reducing this lookup, or by exploiting a hypothesis
         or a hint database. *)
      simple eapply simp_reflexive_ret; [
        (* subgoal: [m1 = ret v] *)
        solve [ eauto with simp_specs ]
      ]
  | eval ?η ?e =>
      first [
        (* Attempt 1. Solve the goal by exploiting the hint database
           [simp_specs]. This can be necessary if the user chooses to
           populate the hint database with specifications about terms
           of the form [eval η e], as opposed to [call v1 v2]. *)
        simp_solve_eauto
      |
        (* Attempt 2. Unfold the definition of [eval] once in [eval η e]. *)
        simp_eval; simp0
      ]
  | call ?v1 ?v2 =>
      first [
        (* Attempt 1. Step into the call. This is possible only if [v1]
           is a concrete closure. *)
        simp_enter; simp0
        (* Attempt 2. Reason about this call. This is possible only if a
           specification for this call exists in the current context or
           in a hint database. *)
      | simp1_call_reason v2
      ]
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
  | try ?m ?f ?h =>
      (* [try] is treated in the same way as [bind]. *)
      first [
        simple eapply advance_SimpTry; [ simp1; simp_close | simp0_try ]
      | simp1_try
      ]
  | Par ?m1l ?m1r ?k ?h =>
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
   into the call (if possible). It leaves one subgoal. *)

with simp_enter :=
  (* We intentionally use [eapply], not [simple eapply], so that [v1] can be
     unfolded on the fly if necessary. This is useful, e.g., when [v1] is a
     function in the standard library, such as [Stdlib__not].

     We expect [eapply] to succeed only if [v1] is a concrete closure, that
     is, either [VClo ...] or [VCloRec ...] or a transparent definition that
     unfolds to one of these forms. If [v1] is an opaque definition then we
     expect [eapply] to fail. (These expectations may be wrong. I have
     observed situations where [eapply] violates opacity.) *)
  first [
    (* strong *) eapply simp_enter_call_VClo
  | (* strong *) eapply simp_enter_call_VCloRec
  ]

(* [simp_call] expects a goal of the form [simp (call _ _) _] and solves
   this goal using a specification that must exist in the current context or
   in the hint database [simp_specs].

   This tactic leaves zero subgoals. If the goal cannot be solved, then
   this tactic fails. *)

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
   where [m] has been simplified already. *)

with simp0_bind :=
  try simp1_bind

with simp1_bind :=
  (* Performing at least one simplification step, when the term is a [bind]
     construct, requires rewriting [bind (ret _) _]. To do so, we explicitly
     apply a lemma; this ensures that we fail if the goal is not of the form
     [bind (ret _) _]. *)
  (* TODO explain that we wish to allow [m] to reduce to [ret _],
          without violating opacity *)
  first [
    simple eapply advance_simp_bind_ret
  | lazymatch goal with
    |- simp (bind ?m _) _ =>
      let o := eval cbn in m in
      lazymatch o with ret _ =>
        (* strong *) eapply advance_simp_bind_ret
      end
    end
  ];
  simp0

(* [simp0_try] and [simp1_try] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (try m _ _) _],
   where [m] has been simplified already. *)

with simp0_try :=
  try simp1_try

with simp1_try :=
  (* TODO we cut corners and use strong [eapply] here; this is simpler;
          we need not worry about opacity because breakpoints do not
          appear under [try] *)
  first [
    (* strong *) eapply advance_simp_try_ret
  | (* strong *) eapply advance_simp_try_throw
  ];
  simp0

(* [simp0_par] and [simp1_par] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (Par m1 m2 _ _) _],
   where [m1] and [m2] have been simplified already. *)

with simp0_par :=
  try simp1_par

with simp1_par :=
  (* Performing at least one simplification step, when the term is a [Par]
     construct, requires applying one of the following rules. *)
  (* TODO we cut corners and use strong [eapply] here; this is simpler;
          we need not worry about opacity because breakpoints do not
          appear under [par] *)
  first [
    (* strong *) eapply advance_SimpParRetRet (* maybe a special case of the following *)
  | (* strong *) eapply advance_SimpParRetLeftThrow
  | (* strong *) eapply advance_SimpParRetLeft
  | (* strong *) eapply advance_SimpParRetRightThrow
  | (* strong *) eapply advance_SimpParRetRight
  ];
  simp0.

(* [simp] is the main public entry point into the above tactics. *)

(* [simp] proves or advances a goal of the form [simp m1 m2], where [m2] may
   be a metavariable. If [m2] is a metavariable then it is instantiated with
   a term that has been simplified as far as possible. *)

Ltac simp :=
  lazymatch goal with |- simp ?m1 _ =>
    simp0; try simp_close
  | _ =>
    fail "[simp] expects a goal of the form [simp _ _]"
  end.

(* [simp_really] is another public entry point into the above tactics. *)

(* [simp_really] proves a goal of the form [simp m1 m2], where [m2] must be
   a metavariable. [m2] is instantiated with a term that has been simplified
   as far as possible. [simp_really] performs at least one step of
   simplification. *)

Ltac simp_really :=
  lazymatch goal with |- simp ?m1 _ =>
    simp1; simp_close
  | _ =>
    fail "[simp_really] expects a goal of the form [simp _ _]"
  end.

(* [simp_continue] unfolds an opaque definition and continues simplifying
   via [simp]. *)

Ltac simp_continue :=
  lazymatch goal with
  | |- simp ?m _ =>
      (* TODO should use [simple eapply] to enforce rewriting at the root *)
      unfold_breakpoint m;
      simp
  | _ =>
      fail "[simp_continue] expects a goal of the form [simp _ _]"
  end.

(* [simp_enter_and_abstract] expects a goal of the form [simp (call v _) _],
   where [v] is a concrete closure (typically a recursive closure). It steps
   into the call, then abstracts away the closure [v], so as to make it
   opaque. *)

Ltac simp_enter_and_abstract :=
  lazymatch goal with |- simp (call ?v _) _ =>
    (* First, expand [call] away. *)
    simp_enter;
    normalize;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
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
