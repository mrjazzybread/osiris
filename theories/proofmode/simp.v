From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality.

(* A pure computation is terminating, deterministic, and does not use
   mutable state. *)

(* This file offers lemmas and tactics that help simplify computations,
   that is, solve goals of the form [simp m1 ?m2]. *)

(* This file also defines the judgement [SIMP m φ], which asserts that the
   computation [m] is pure and eventually produces a result that satisfies
   the postcondition [φ]. This judgement and its reasoning rules for a
   simple Hoare logic (of total correctness) for pure computations. *)

(* This file offers lemmas and tactics that help work with [SIMP] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)

(* The following lemmas are reasoning rules for goals of the form [simp _ _]. *)

Lemma prove_simp_ret {A} (a1 a2 : A) :
  a1 = a2 →
  simp (ret a1) (ret a2).
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

Lemma prove_simp_par {A1 A2 A} m1 m2 a1 a2 (k : A1 * A2 → free A) m' ko :
  simp m1 (ret a1) →
  simp m2 (ret a2) →
  simp (k (a1, a2)) m' →
  simp (Par m1 m2 k ko) m'.
Proof.
  eauto with simp.
Qed.

Lemma simp_tail_call {A} (m : free A) m' :
  simp m m' →
  simp (bind m ret) m'.
Proof.
  rewrite bind_ret_right. eauto.
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

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

Create HintDb simp_specs.

(* [simp_ret] expects of the goal of the form [simp (ret ?a1) (ret ?a2)].
   It reduces this goal to the equality [a1 = a2], and attempts to prove
   this equality. *)

Ltac simp_ret :=
  eapply prove_simp_ret; [ equality ].

(* The tactic [normalize] attempts to reduce and normalize the goal before
   applying any reasoning rule. It is used by the tactics that follow. *)

Ltac normalize :=
  cbn;
  rewrite ?true_iff, ?false_iff in *; (* TODO expensive? *)
  rewrite ?bind_bind. (* TODO may wish to rewrite at the root only. *)

(* [close] solves a goal of the form [simp m1 m2] using reflexivity.

   The term [m1] must be normalized.

   If reflexivity cannot solve the goal, then [close] fails. *)

Local Ltac close :=
  solve [
    eapply SimpReflexive
  | eapply simp_reflexive; [ eauto with simp_specs ]
      (* This can solve [simp m (ret v)] when there is a hypothesis
         [m = ret v] in the context or in the hint database. This is
         particularly useful when [m] is [lookup η x]. *)
  | simp_ret
  ].

(* The tactics [simp0] and [simp1] expect a goal of the form [simp m1 m2].

   They advance this goal by performing simplification steps that lead from
   [m1] to [m'1] and by leaving a residual goal of the form [simp m'1 m2].

   Whereas [simp0] may find zero or more simplification steps, [simp1] must
   find at least one simplification step; otherwise, it fails.

   The term [m1] is expected to be normalized already.

   If the goal is changed to [simp m'1 m2] then the term [m'1] is guaranteed
   to be normalized. *)

Ltac simp0 :=
  (* We are allowed to perform zero or more steps. *)
  (* Either perform at least one step, or perform zero step. *)
  first [ simp1; simp0 | idtac ]

with simp1 :=
  (* We must perform at least one step. *)
  (* We examine the syntax of [m1], which is why we require [m1] to be
     normalized already. *)
  lazymatch goal with |- simp ?m1 _ =>
  lazymatch m1 with
  | ret ?a1 =>
      fail
  | eval ?η ?e =>
      (* Rewrite [eval η e] to [eval' η e] and normalize the latter form.
         This counts as a simplification step, so our duty is fulfilled.
         We are then free to use [simp0] to find zero or more further steps. *)
      rewrite eval_eval'; normalize;
      simp0
  (* Same as above. *)
  | as_int (eval ?η ?e) =>
      rewrite eval_eval'; normalize; simp0
  | as_bool (eval ?η ?e) =>
      rewrite eval_eval'; normalize; simp0
  | as_loc (eval ?η ?e) =>
      rewrite eval_eval'; normalize; simp0
  | as_record (eval ?η ?e) =>
      rewrite eval_eval'; normalize; simp0
  | call ?v1 ?v2 =>
      (* We allow ourselves to reason about function calls using whatever
         hypotheses may be present in the context and in the hint database
         [simp_specs]. *)
      solve [
        (* This [rewrite] command is ad hoc, maybe slow; TODO.
           The problem is that [cbn] expands [encode] into [encode_list].
           This prevents the application of specification lemmas whose
           statement uses [encode]. *)
        repeat rewrite encode_list_is_encode;
        eauto with simp_specs typeclass_instances
      ]
  | bind ?m ret =>
      (* A tail call can be simplified. *)
      eapply simp_tail_call; simp0
  | bind ?m ?f =>
      (* We apply the reasoning rule Bind only if we are able to solve
         its first premise. This guarantees that we leave only one
         subgoal (not two), as dictated by the specification of this
         tactic. Furthermore, this guarantees that we do not create
         an unsolvable subgoal in situations where the left-hand side
         of the sequence needs an existentially quantified postcondition. *)
      eapply prove_simp_bind; [ normalize; simp0; close |];
      normalize; simp0
  | try ?m ?f ?ko =>
      eapply prove_simp_try; [ normalize; simp0; close |];
      normalize; simp0
  | Stop CEval _ _ _ =>
      first [ eapply advance_SimpEvalNext | eapply advance_SimpEval ]; normalize;
      simp0
  | Stop CLoop _ _ _ =>
      first [ eapply advance_SimpLoopNext | eapply advance_SimpLoop ]; normalize;
      simp0
  | Stop CFlip _ _ _ =>
      eapply advance_SimpFlipOK; normalize;
      simp0
  (* We do not exploit the lemma [prove_simp_par] because we deal with [Par]
     directly, as follows. *)
  | Par ?m1l ?m1r ?k ?ko =>
      (* We want to first simplify both sides of the [Par] independently, as
         far as possible; then, if possible, simplify the [Par] combinator
         away and further simplify the result. Three attempts are needed to
         ensure that we make one step of progress in at least one of the
         three subgoals. This should nevertheless be reasonably efficient. *)
      first [
        (* Attempt 1. Make progress on the left-hand side,
           and possibly more progress elsewhere. *)
        eapply advance_SimpPar; [ simp1; close | simp0; close | simp0_par ]
      |
        (* Attempt 2. Make progress on the right-hand side,
           and possibly more progress elsewhere. *)
        eapply advance_SimpPar; [ close | simp1; close | simp0_par ]
      |
        (* Attempt 3. Make progress by eliminating this [Par],
           and possibly more progress thereafter. *)
        simp1_par
      ]
  end end

(* [simp0_par] and [simp1_par] are special cases of [simp0] and [simp1].

   They assume that the goal is of the form [simp (Par m1 m2 _ _) _],
   where [m1] and [m2] are normalized and cannot be simplified. *)

with simp0_par :=
  first [ simp1_par | idtac ]

with simp1_par :=
  (* Performing at least one simplification step, when the term is a [Par]
     construct, requires applying one of the following rules. *)
  first [
    eapply advance_SimpParRetRet (* maybe a special case of the following *)
  | eapply advance_SimpParRetLeftNext
  | eapply advance_SimpParRetLeft
  | eapply advance_SimpParRetRightNext
  | eapply advance_SimpParRetRight
  ];
  normalize; simp0.

(* [simp] is the main public entry point into the above tactics. *)

(* [simp] proves or advances a goal of the form [simp m1 m2], where [m2] may
   be a metavariable. If [m2] is a metavariable then it is instantiated with
   a normalized term. *)

Ltac simp :=
  normalize;
  lazymatch goal with |- simp ?m1 _ =>
    simp0; try close
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
    simp1; close
  | _ =>
    fail "[simp_really] expects a goal of the form [simp _ _]"
  end.

(* [simp_continue] unfolds [concatenating] in a goal of the form
   [simp (concatenating ...) _], and continues simplifying via [simp]. *)

Ltac simp_continue :=
  normalize;
  lazymatch goal with |- simp (concatenating _ _ _ _) _ =>
    with_strategy transparent [concatenating]
      unfold concatenating at 1;
    normalize;
    simp
  | _ =>
    fail "[simp_continue] expects a goal of the form [simp (concatenating ...) _]"
  end.

(* [simp_enter] expects a goal of the form [simp (call _ _) _] and steps
   into the call. It is normally used at the beginning of the proof of a
   function, that is, when reasoning about a callee. At a call site, it
   is normally not used, unless the user wants to logically inline the
   called function. *)

Ltac simp_enter :=
  with_strategy transparent [call] unfold call; simp.

(* -------------------------------------------------------------------------- *)

(* The tactic [simp_specify x φ] should be used when the term begins with
   [concatenating eval η e δ], that is, when the environment is about to be
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
    |- simp (concatenating eval _ _ ?δ) _ =>
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* The judgement [SIMP m φ] asserts that the computation [m] can be simplified
   to [ret #x], where [x] is a (logical) value so that [φ x] holds. *)

(* Because the relation [simp] is inductively defined, this judgement implies
   that [m] terminates. This is a Hoare logic of total correctness. *)

Definition SIMP `{Encode X} (m : free val) (φ : X → Prop) :=
  ∃ x, simp m (ret #x) ∧ φ x.

(* -------------------------------------------------------------------------- *)

(* Basic reasoning rules for [ret], [bind], [try]. *)

Lemma SIMP_ret `{Encode X} (φ : X → Prop) v x :
  v = #x →
  φ x →
  SIMP (ret v) φ.
Proof.
  unfold SIMP. intros. subst. eauto with simp.
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [Next],
   so the handler [g] is dead and no proof obligation bears on it. *)

Lemma SIMP_try X (_ : Encode X) Y (_ : Encode Y)
  m f g (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (try m f g) ψ.
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_try.
Qed.

(* This variant of the Bind rule has two premises. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind X (_ : Encode X) Y (_ : Encode Y)
  m f (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (bind m f) ψ.
Proof.
  rewrite bind_as_try. eauto using SIMP_try.
Qed.

(* This Iris-style variant of the Bind rule has just one premise. It is
   obtained by choosing the least precise φ in the above lemma. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind_unary X (_ : Encode X) Y (_ : Encode Y)
  m f (ψ : Y → Prop) :
  SIMP m (λ (x : X), SIMP (f #x) ψ) →
  SIMP (bind m f) ψ.
Proof.
  eauto using SIMP_bind.
Qed.

(* -------------------------------------------------------------------------- *)

(* This lemma allows simplifying a goal of the form [SIMP m φ] by first
   simplifying [m] into [m'], then reasoning about [m']. *)

Lemma SIMP_simp `{Encode X} m m' (φ : X → Prop) :
  simp m m' →
  SIMP m' φ →
  SIMP m φ.
Proof.
  unfold SIMP.
  intros ? (x & ? & ?).
  eauto with simp.
Qed.

(* The Consequence rule. *)

Lemma SIMP_covariant `{Encode X} m (φ ψ : X → Prop) :
  SIMP m φ →
  (∀ x, φ x → ψ x) →
  SIMP m ψ.
Proof.
  intros (x & Hm & Hx) ?. exists x. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [bind] composed with [as_bool]. *)

Local Lemma simp_as_bool (x : bool) (m : free val) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_bool Y (_ : Encode Y)
  m (f : bool → free val) (φ : bool → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : bool), φ x → SIMP (f x) ψ) →
  SIMP (bind (as_bool m) f) ψ.
  (* This is [@bind bool val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_bool.
Qed.

(* [bind] composed with [as_bool]. *)

Lemma simp_as_int (x : Z) (m : free val) :
  simp m (ret #x) →
  simp (as_int m) (ret (repr x)).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_int Y (_ : Encode Y)
  m (f : int → free val) (φ : Z → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : Z), φ x → SIMP (f (repr x)) ψ) →
  SIMP (bind (as_int m) f) ψ.
  (* This is [@bind int val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_int.
Qed.

(* TODO add similar lemmas for [as_loc] and possibly others *)

(* -------------------------------------------------------------------------- *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma SIMP_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [SIMP_covariant] and [SIMP_call]. *)

Lemma SIMP_call_covariant `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  (∀ y, φ y → ψ y) →
  SIMP (call v1 v'2) ψ.
Proof.
  eauto using SIMP_covariant, SIMP_call.
Qed.

(* -------------------------------------------------------------------------- *)

(* Opacity. *)

Global Opaque SIMP.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* [SIMP_ret] expects a goal of the form [SIMP (ret v) φ]. It applies
   the lemma [SIMP_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac SIMP_ret :=
  eapply SIMP_ret; [ solve [ encode ] | normalize ].

(* [SIMP_simp] expects a goal of the form [SIMP m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [SIMP m' φ]. *)

Ltac SIMP_simp :=
  eapply SIMP_simp; [ simp_really |].

(* SIMP0 leaves zero subgoal. *)
(* SIMP1 leaves one subgoal, which may have an arbitrary shape. *)

Ltac SIMP0 :=
  normalize;
  try SIMP_simp;
  first [

    SIMP_ret; [
      (* goal: [φ x] *)
      SIMP_close
    ]

  | eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* goal: [SIMP (call #x) φ] *)
      SIMP_close
    ]

  | eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* goal: [∀ x, φ x → φ' x] *)
    | SIMP_close
    ]

  | eapply SIMP_bind_as_bool; [ SIMP0 | normalize; intros; SIMP0 ]
  | eapply SIMP_bind_as_int ; [ SIMP0 | normalize; intros; SIMP0 ]
  | eapply SIMP_bind        ; [ SIMP0 | normalize; intros; SIMP0 ]
  | eapply SIMP_try         ; [ SIMP0 | normalize; intros; SIMP0 ]

  | SIMP_close

  ]

with SIMP1 :=
  normalize;
  try SIMP_simp;
  first [

    SIMP_ret (* residual goal: [φ x] *)

  | eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* residual goal: [∀ x, φ x → φ' x] *)
    | normalize
    ]

  | eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* residual goal: [SIMP (call #x) φ] *)
      idtac
    ]

  | eapply SIMP_bind_as_bool; [ SIMP0 | (* residual goal *) normalize ]
  | eapply SIMP_bind_as_int ; [ SIMP0 | (* residual goal *) normalize ]
  | eapply SIMP_bind        ; [ SIMP0 | (* residual goal *) normalize ]
  | eapply SIMP_try         ; [ SIMP0 | (* residual goal *) normalize ]

  | idtac (* residual goal *)

  ]

with SIMP_close :=
  solve [ eauto with SIMP_specs representable ].

Ltac SIMP_enter :=
  with_strategy transparent [call] unfold call; SIMP1.

Ltac SIMP_continue :=
  normalize;
  lazymatch goal with
  |  |- SIMP (concatenating _ _ _ _) _ =>
      with_strategy transparent [concatenating] unfold concatenating at 1;
      SIMP1
  |  |- SIMP (bind (dconcatenating _ _) _) _ =>
      with_strategy transparent [dconcatenating] unfold dconcatenating at 1;
      SIMP1
  | _ =>
    fail "[SIMP_continue]: unexpected goal."
  end.

Ltac SIMP_specify x φ :=
  lazymatch goal with
  | |- SIMP (bind (dconcatenating ?δ _) _) _ =>
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* It is debatable in which order the two premises of the lemma [SIMP_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [SIMP (call v1 #x) φ]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [SIMP (call v1 #x) φ], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb SIMP_specs.

(* TODO may be unused *)
Ltac SIMP_call :=
  first [
    eapply SIMP_call; [ solve [encode] | solve [eauto with SIMP_specs] ]
  | eapply SIMP_covariant; [
      eapply SIMP_call; [ solve [encode] | eauto with SIMP_specs ]
    | cbn ]
  ].
