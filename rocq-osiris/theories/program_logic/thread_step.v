From Stdlib Require Import Program.Equality.

From stdpp Require Import gmap fin_map_dom fin_sets.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.

From iris.base_logic.lib Require Import iprop own.

Section thread_step.

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

  Inductive thread_step {A X} : th_config A X -> th_config_step A X -> Prop :=
  | BaseS : ∀ (m : micro A X) σ m' σ' π,
      step (σ, m) (σ', m') ->
      thread_step (σ, m, π) (σ', m', None)
  | ForkS : ∀ σ ι (π : gset thread) v1 v2 (k : outcome2 val exn -> micro A X),
      ι ∉ π ->
      thread_step
        (σ, Stop CFork (v1, v2) k, π)
        (σ, continue k (VThread ι), Some (ι, call v1 v2))
  .

  Global Arguments thread_step {A X}.

End thread_step.

Global Hint Constructors thread_step : thread_step.

From iris.bi Require Import bi.

Ltac destruct_thread_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try lazymatch goal with
    | h: thread_step (?σ, Stop ?c ?x ?k, ?π) ?m' |- _ =>
          remember x
    | h: thread_step (?σ, stop ?c ?x, ?π) ?m' |- _ =>
          remember x
    end;
  match goal with h: thread_step ?m ?m' |- _ =>
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
    | _ => ∃ σ' m' (μ : option (thread * microvx)),
      thread_step (σ, m, π) (σ', m', μ)
    end.

  Lemma invert_can_progress {A E} σ π m :
    @can_progress A E σ π m ->
    ((∃ ι' k, m = Stop CJoin ι' k ∧ ι' ∈ π) ∨
      (∃ v1 v2 k, m = Stop CFork (v1, v2) k) ∨
      (can_step (σ, m))).
  Proof.
    intros Hcp.
    unfold can_progress in Hcp.
    (* Cases on the micro computation. *)
    destruct m;
      (* If that computation is a Stop, destruct the code *)
      try destruct_code;
      (* Generally try to invert Hcp *)
      try (destruct Hcp as (σ' & m' & μ & Hcp);
           dependent destruction Hcp;
           destruct_step; auto with step can_step);
      (* There remains some cases *)
      try solve [(do 2 right; auto with step can_step)].

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
      do 3 eexists;
      by (eapply BaseS; eauto with step can_step).
    Unshelve. apply b.
  Qed.

  Lemma can_progress_fork {A E} σ π x (k : _ -> micro A E) :
    can_progress σ π (Stop CFork x k).
  Proof.
    destruct x.
    unfold can_progress.
    do 3 eexists. eapply ForkS.
    apply is_fresh.
  Qed.

  Lemma can_progress_join {A E} σ π ι' (k : _ -> micro A E) :
    ι' ∈ π ->
    can_progress σ π (Stop CJoin ι' k).
  Proof.
    intros Hπ; simpl.
    unfold can_progress.
    assumption.
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

  Lemma invert_thread_step_resume {A E : Type} π (σ σ' : store) m' μ (l : loc) (o : outcome2 val exn)
    (k : outcome2 val exn → micro A E)
    (sk : outcome2 val exn → microvx) :
    σ !! l = Some (K sk) →
    thread_step (σ, Stop CResume (l, o) k, π) (σ', m', μ) →
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

  (* If [m] takes a [thread_step] to some [m'],
     and [m] can take a sequential step,
     then it took that sequential step which resulted in [m']. *)
  Lemma invert_can_step_thread_step {A E} σ π (m : micro A E) m' μ σ' :
    thread_step (σ, m, π) (σ', m', μ) ->
    can_step (σ, m) ->
    step (σ, m) (σ', m') ∧
      μ = None.
  Proof.
    intros Hwpstep Hstep.
    dependent destruction Hwpstep;
      try solve [ exfalso; eauto with invert_can_step ].
    done.
  Qed.

  Local Ltac invert_try2 :=
    match goal with
    | h: step (_, try2 _ _) (_, _) |- _ => apply invert_step_try2 in h as (? & ? & ->)
    end.

  Lemma invert_thread_step_try2 {A B E' E} σ π m m' (k : outcome2 A E' -> micro B E) σ' μ :
    thread_step (σ, (try2 m k), π) (σ', m', μ) ->
    can_step (σ, m) ->
    ∃ m'', m' = try2 m'' k ∧ thread_step (σ, m, π) (σ', m'', None).
  Proof.
    intros Hwp Hstep.
    dependent destruction Hwp;
      try solve [ exfalso; eauto with invert_can_step ].
    { apply invert_step_try2 in H; last assumption.
      destruct H as (? & Hstep' & ->).
      eexists; split; [ reflexivity | apply BaseS; assumption ]. }
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

  Definition irreducible m σ :=
    ∀ π m' σ' μ, ¬ thread_step (σ, m, π) (σ', m', μ).

  Class Atomic m : Prop :=
    atomic σ π σ' m' μ :
      thread_step (σ, m, π) (σ', m', μ) →
      is_Some (is_outcome m').

End Atomicity.
