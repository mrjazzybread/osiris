From Stdlib Require Import Program.Equality.

From stdpp Require Import gmap fin_map_dom fin_sets.
From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval step.

From iris.base_logic.lib Require Import iprop own.

Section subjective_step.

  Context {Σ : gFunctors}.

  Definition is_outcome {A X} (m : micro A X) :=
    match m with
    | Ret v => Some (O2Ret v)
    | Throw v => Some (O2Throw v)
    | _ => None
    end.

  Definition post_map (_ : gFunctors) := gmap thread gname.
  Instance lookup_post_map : Lookup thread gname (post_map Σ).
  Proof. apply _. Defined.

  Definition th_config A X : Type := store * (micro A X) * (gset thread).
  Definition th_config_step A X : Type := store * (micro A X) * option (thread * microvx).

  (* [subjective_step] is [step] plus the two things [step] cannot express: a
     fork, which produces a new thread, and a prophecy resolution, which
     produces an OBSERVATION. The label is what carries the latter.

     Every rule but [ResolveS] emits nothing, so in practice the label is
     [[]] everywhere except at a resolution — which is exactly what makes
     the change to the existing rules a matter of threading [[]] through. *)

  Inductive subjective_step {A X} :
    th_config A X -> list observation -> th_config_step A X -> Prop :=
  | BaseS : ∀ (m : micro A X) σ m' σ' π,
      step (σ, m) (σ', m') ->
      subjective_step (σ, m, π) [] (σ', m', None)
  | ForkS : ∀ σ ι (π : gset thread) v1 v2 (k : outcome2 val exn -> micro A X),
      ι ∉ π ->
      subjective_step
        (σ, Stop CFork (v1, v2) k, π) []
        (σ, continue k (VThread ι), Some (ι, call v1 v2))

  (* The resolution proper, and the reason this relation is labelled. The
     premise is a step of the BARE system call [stop c x], whose targets
     are exactly [Ret _], [Throw _] and [Crash] — three disjoint shapes,
     so the three rules below never overlap and a resolution can never be
     silently skipped.

     Note that the call and the resolution happen in ONE step. That is the
     whole point: an observation emitted one step later could be separated
     from the call by another thread, and would be worthless as a
     linearization point. *)
  | ResolveS : ∀ {Y} σ σ' (c : code Y val exn) x p v w π
        (k : outcome2 val exn -> micro A X),
      step (σ, stop c x) (σ', Ret w) ->
      subjective_step
        (σ, Stop (CResolve c) (x, p, v) k, π) [(p, (w, v))]
        (σ', continue k w, None)

  (* If the call throws or crashes there is no result to resolve with, and
     the outcome propagates with no observation. *)
  | ResolveThrowS : ∀ {Y} σ σ' (c : code Y val exn) x p v e π
        (k : outcome2 val exn -> micro A X),
      step (σ, stop c x) (σ', Throw e) ->
      subjective_step
        (σ, Stop (CResolve c) (x, p, v) k, π) []
        (σ', discontinue k e, None)

  | ResolveCrashS : ∀ {Y} σ σ' (c : code Y val exn) x p v π
        (k : outcome2 val exn -> micro A X),
      step (σ, stop c x) (σ', Crash) ->
      subjective_step
        (σ, Stop (CResolve c) (x, p, v) k, π) []
        (σ', Crash, None)
  .

  Global Arguments subjective_step {A X}.

End subjective_step.

Global Hint Constructors subjective_step : subjective_step.

From iris.bi Require Import bi.

Ltac destruct_subjective_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try lazymatch goal with
    | h: subjective_step (?σ, Stop ?c ?x ?k, ?π) ?κ ?m' |- _ =>
          remember x
    | h: subjective_step (?σ, stop ?c ?x, ?π) ?κ ?m' |- _ =>
          remember x
    end;
  match goal with h: subjective_step ?m ?κ ?m' |- _ =>
                    dependent destruction h
  end;
  try destruct_step;
  (* We will often conclude that the list of forked threads is empty. *)
  try rewrite bi.sep_emp.


Section can_progress.

  Context {Σ : gFunctors}.

(* -------------------------------------------------------------------------- *)

  Definition can_progress {A E} σ (π : gset thread) (m : micro A E) :=
    match m with
    | Stop CJoin ι' k => ι' ∈ π
    | _ => ∃ κ σ' m' (μ : option (thread * microvx)),
      subjective_step (σ, m, π) κ (σ', m', μ)
    end.

  Lemma invert_can_progress {A E} σ π m :
    @can_progress A E σ π m ->
    ((∃ ι' k, m = Stop CJoin ι' k ∧ ι' ∈ π) ∨
      (∃ v1 v2 k, m = Stop CFork (v1, v2) k) ∨
      (∃ Y (c : code Y val exn) y k, m = Stop (CResolve c) y k) ∨
      (can_step (σ, m))).
  Proof.
    intros Hcp.
    unfold can_progress in Hcp.
    (* Cases on the micro computation. *)
    destruct m;
      (* If that computation is a Stop, destruct the code *)
      try destruct_code;
      (* Generally try to invert Hcp *)
      try (destruct Hcp as (κ & σ' & m' & μ & Hcp);
           dependent destruction Hcp;
           destruct_step; auto with step can_step);
      (* [Resolve]: one goal per code, all of the same shape. *)
      try solve [do 2 right; left; repeat eexists];
      (* There remains some cases *)
      try solve [(do 3 right; auto with step can_step)].

    (* Only the concurrent [Stop] cases are left. *)
    - right; left. destruct x. repeat eexists.
    - left. repeat eexists. apply Hcp.
  Qed.

  Arguments can_progress : simpl never.

  Lemma can_step_can_progress {A E} σ (m : micro A E) :
    ∀ π,
      can_step (σ, m) ->
      can_progress σ π m.
  Proof.
    intros π ([σ' m'] & Hstep).
    unfold can_progress.
    destruct_step;
      do 4 eexists;
      by (eapply BaseS; eauto with step can_step).
    Unshelve. apply b.
  Qed.

  Lemma can_progress_fork {A E} σ π x (k : _ -> micro A E) :
    can_progress σ π (Stop CFork x k).
  Proof.
    destruct x.
    unfold can_progress.
    do 4 eexists. eapply ForkS.
    apply is_fresh.
  Qed.

  (* A [Resolve] can progress provided the system call it wraps can step
     AND that step lands on an outcome — which is what the three [Resolve]
     rules cover between them.

     The second hypothesis is not a technicality: it is atomicity. A code
     like [CEval] steps to a whole computation, not to a result, and there
     is nothing for a resolution to record at such a step. The rule for
     [Resolve] in the program logic will require the same thing, exactly
     as HeapLang's [wp_resolve] requires its expression to be atomic. *)

  Lemma can_progress_resolve {A E X} σ π (c : code X val exn) x p v
    (k : outcome2 val exn -> micro A E) :
    can_step (σ, stop c x) ->
    (∀ σ' m', step (σ, stop c x) (σ', m') ->
       (∃ w, m' = Ret w) ∨ (∃ e, m' = Throw e) ∨ m' = Crash) ->
    can_progress σ π (Stop (CResolve c) (x, p, v) k).
  Proof.
    intros Hcs Hat.
    unfold can_progress.
    destruct Hcs as ([σ' m'] & Hstep).
    (* The shape of the target decides which of the three rules applies. *)
    destruct (Hat _ _ Hstep) as [(w & ->) | [(e & ->) | ->]].
    - do 4 eexists. by eapply ResolveS.
    - do 4 eexists. by eapply ResolveThrowS.
    - do 4 eexists. by eapply ResolveCrashS.
  Qed.

  Lemma can_progress_join {A E} σ π ι' (k : _ -> micro A E) :
    ι' ∈ π ->
    can_progress σ π (Stop CJoin ι' k).
  Proof.
    intros Hπ; simpl.
    unfold can_progress.
    assumption.
  Qed.

  (* No rule for [Resolve] inspects its continuation, so progress does not
     depend on it. This is what the congruence rules need: [try2] and the
     [Par]/[Handle] float-ups all change only the continuation. *)

  Lemma can_progress_resolve_cont {A B E E' X} σ π (c : code X val exn) y
    (k : outcome2 val exn -> micro A E) (k' : outcome2 val exn -> micro B E') :
    can_progress σ π (Stop (CResolve c) y k) ->
    can_progress σ π (Stop (CResolve c) y k').
  Proof.
    unfold can_progress.
    intros (κ & σ' & m' & μ & Hcp).
    dependent destruction Hcp.
    - exfalso. eapply (proj2 (stuck_Resolve _ c y k)); exact H.
    - do 4 eexists. by eapply ResolveS.
    - do 4 eexists. by eapply ResolveThrowS.
    - do 4 eexists. by eapply ResolveCrashS.
  Qed.

  (* [try2] pushes into continuations, and no rule of [subjective_step] looks
     at a continuation, so progress is preserved by it. *)

  Lemma can_progress_try2 {A B E E'} σ π (m : micro A E)
    (f : outcome2 A E -> micro B E') :
    can_progress σ π m ->
    can_progress σ π (try2 m f).
  Proof.
    intros Hcp.
    pose proof Hcp as Hcp'.
    apply invert_can_progress in Hcp'.
    destruct Hcp' as [ (ι' & k & -> & Hdom)
                     | [ (v1 & v2 & k & ->)
                     | [ (Y & c & y & k & ->) | Hcs ] ] ].
    - by apply can_progress_join.
    - apply can_progress_fork.
    - (* [try2] only changes the continuation. *)
      simpl try2. cbn match.
      by eapply can_progress_resolve_cont.
    - apply can_step_can_progress. by apply can_step_try2.
  Qed.

  Lemma inv_can_progress_join {A E} σ (π : post_map Σ) ι' (k : _ -> micro A E) :
    can_progress σ (dom π) (Stop CJoin ι' k) ->
    ∃ φ, π !! ι' = Some φ.
  Proof.
    intros Hprog; simpl.
    apply (elem_of_dom π ι').
    unfold can_progress in Hprog.
    apply Hprog.
  Qed.

  Lemma invert_subjective_step_resume {A E : Type} π (σ σ' : store) κ m' μ (l : loc) (o : outcome2 val exn)
    (k : outcome2 val exn → micro A E)
    (sk : outcome2 val exn → microvx) :
    σ !! l = Some (Kont sk) →
    subjective_step (σ, Stop CResume (l, o) k, π) κ (σ', m', μ) →
      σ' = <[l:=Shot]> σ ∧
      m' = try2 (sk o) k ∧
      μ = None.
  Proof.
    intros Hlookup Hstep.
    dependent destruction Hstep.
    destruct_step.
    repeat split; auto.
    - unfold step_resume_1. rewrite Hlookup. reflexivity.
    - unfold step_resume_2. rewrite Hlookup. reflexivity.
  Qed.

  (* If [m] takes a [subjective_step] to some [m'],
     and [m] can take a sequential step,
     then it took that sequential step which resulted in [m']. *)
  (* A computation that can take a sequential step took one, and a
     sequential step emits nothing: only a [Resolve] does, and a [Resolve]
     has no sequential step. *)
  Lemma invert_can_step_subjective_step {A E} σ π (m : micro A E) m' μ σ' κ :
    subjective_step (σ, m, π) κ (σ', m', μ) ->
    can_step (σ, m) ->
    step (σ, m) (σ', m') ∧
      μ = None ∧ κ = [].
  Proof.
    intros Hwpstep Hstep.
    dependent destruction Hwpstep;
      try solve [ exfalso; eauto with invert_can_step ].
    { done. }
    (* The three [Resolve] cases are vacuous: a [Resolve] has no [step]. *)
    all: exfalso; eauto with invert_can_step.
  Qed.

  Local Ltac invert_try2 :=
    match goal with
    | h: step (_, try2 _ _) (_, _) |- _ => apply invert_step_try2 in h as (? & ? & ->)
    end.

  Lemma invert_subjective_step_try2 {A B E' E} σ π m m' (k : outcome2 A E' -> micro B E) σ' μ κ :
    subjective_step (σ, (try2 m k), π) κ (σ', m', μ) ->
    can_step (σ, m) ->
    ∃ m'', m' = try2 m'' k ∧ subjective_step (σ, m, π) [] (σ', m'', None).
  Proof.
    intros Hwp Hstep.
    dependent destruction Hwp;
      try solve [ exfalso; eauto with invert_can_step ].
    { apply invert_step_try2 in H; last assumption.
      destruct H as (? & Hstep' & ->).
      eexists; split; [ reflexivity | apply BaseS; assumption ]. }
    (* In the remaining cases — [Fork], [Join] and the three [Resolve]s —
       [try2] pushes into the continuation, so [m] is itself the offending
       [Stop], which cannot step, contradicting [can_step (σ, m)]. *)
    all: symmetry in x;
      apply invert_try2_eq_stop in x as (k' & -> & ->);
        try (intros ? ->);
      exfalso; eauto with invert_can_step.
  Qed.

End can_progress.

Global Opaque can_progress.

Global Hint Resolve
  can_progress_join
  can_progress_fork : can_progress.

Section Atomicity.

  Context {A X : Type}.
  Implicit Type m : micro A X.

  Inductive is_outcome3 m : Prop :=
  | is_ret a : m = Ret a → is_outcome3 m
  | is_throw e : m = Throw e → is_outcome3 m
  | is_crash : m = Crash → is_outcome3 m.

  Class Atomic m : Prop :=
    atomic :
      ∀ σ π σ' m' μ κ,
      subjective_step (σ, m, π) κ (σ', m', μ) →
      is_outcome3 m'.

End Atomicity.
