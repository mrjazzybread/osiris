From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.

(* Flag stating whether a thread has terminated or not. *)
Inductive thread_state :=
| Alive : thread_state
| Dead : outcome2 val exn -> thread_state.

Definition threadpool : Type := gmap thread thread_state.

Definition th_config A X : Type := store * threadpool * micro A X * thread.
Definition th_config_step A X : Type := store * threadpool * micro A X * list (thread * microvx).

Inductive wp_step {A X} : th_config A X -> th_config_step A X -> Prop :=
| BaseS :
  ∀ m σ m' σ' π ι,
    step (σ, m) (σ', m') ->
    wp_step (σ, π, m, ι) (σ', π, m', [])
| ForkS :
  ∀ σ π ι v1 v2 k ι',
    π !! ι' = None ->
    wp_step
      (σ, π, (Stop CFork (v1, v2) k), ι)
      (σ, <[ ι' := Alive ]> π, continue k (VThread ι'), [ (ι', try2 (call v1 v2) die)])
| JoinS :
  ∀ σ π ι k o ι',
    π !! ι' = Some (Dead o) ->
    wp_step
      (σ, π, Stop CJoin ι' k, ι)
      (σ, π, k o, [])
| SelfS :
  ∀ σ π ι u k,
    wp_step
      (σ, π, Stop CSelf u k, ι)
      (σ, π, continue k (VThread ι), [])
| DieS :
  ∀ σ π ι o k,
    π !! ι = Some Alive ->
    wp_step
      (σ, π, Stop CDie o k, ι)
      (σ, <[ ι := Dead o ]> π, Stop CDie o k, [])
.

Global Hint Constructors wp_step : wp_step.

From iris.bi Require Import bi.

Ltac destruct_wp_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try match goal with h: wp_step (?σ, ?π, Stop ?c ?x ?k, ?ι) ?m' |- _ =>
                        remember x
    end;
  match goal with h: wp_step ?m ?m' |- _ =>
                    dependent destruction h
  end;
  try destruct_step;
  (* We will often conclude that the list of forked threads is empty. *)
  try rewrite bi.sep_emp.


(* -------------------------------------------------------------------------- *)

Definition can_progress {A E} (c : th_config A E) :=
  match c with
  | (_, π, Stop CJoin ι' k, _) => ι' ∈ dom π
  | (_, π, Stop CDie o _, ι) => ι ∈ dom π
  | _ => ∃ c', wp_step c c'
end.

Lemma invert_can_progress {A E} σ π m ι :
  @can_progress A E (σ, π, m, ι) ->
  (∃ ι' k, m = Stop CJoin ι' k ∧ ι' ∈ dom π) ∨
  (∃ o k, m = Stop CDie o k ∧ ι ∈ dom π) ∨
  (∃ v1 v2 k, m = Stop CFork (v1, v2) k) ∨
  (∃ u k, m = Stop CSelf u k) ∨
  (can_step (σ, m)).
Proof.
  intros Hcp.
  destruct m; try destruct_code;
  try by (right; right; right; right; destruct Hcp as ([[[??]?]?] & Hcp); destruct_wp_step; subst;
       auto with step can_step).

  - right; right; left. destruct x. repeat eexists.
  - left; repeat eexists. apply Hcp.
  - right; right; right; left.
    repeat eexists.
  - right; left. repeat eexists. apply Hcp.
Qed.

Arguments can_progress : simpl never.

Lemma can_step_can_progress {A E} σ (m : micro A E) :
  ∀ π ι,
    can_step (σ, m) ->
    can_progress (σ, π, m, ι).
Proof.
  intros π ι ([σ' m'] & Hstep).
  destruct_step;
  eexists (_, π, _, []);
    by (apply BaseS; eauto with step can_step).
  Unshelve. apply b.
Qed.

Lemma can_progress_fork {A E} σ π x (k : _ -> micro A E) ι :
  can_progress (σ, π, (Stop CFork x k), ι).
Proof.
  destruct x.
  assert (exists ι', π !! ι' = None) as [ι' Hι'].
  { exists (fresh (dom π)).
    apply fin_map_dom.not_elem_of_dom_1.
    apply fin_sets.is_fresh. }
  eexists. apply ForkS.
  apply Hι'.
Qed.

Lemma can_progress_join {A E} σ π ι' (k : _ -> micro A E) ι s :
  π !! ι' = Some s ->
  can_progress (σ, π, (Stop CJoin ι' k), ι).
Proof.
  intros Hπ; simpl.
  apply elem_of_dom.
  exists s; assumption.
Qed.

Lemma can_progress_self {A E} σ π u (k : _ -> micro A E) ι :
  can_progress (σ, π, (Stop CSelf u k), ι) .
Proof.
  eexists. apply SelfS.
Qed.

Lemma can_progress_die {A E} σ π o (k : _ -> micro A E) ι s :
  π !! ι = Some s ->
  can_progress (σ, π, (Stop CDie o k), ι).
Proof.
  intros Hπ.
  apply elem_of_dom.
  exists s; assumption.
Qed.

Global Hint Resolve
  can_progress_join
  can_progress_fork
  can_progress_self
  can_progress_die : can_progress.

Lemma invert_wp_step_resume {A E : Type} (σ σ' : store) π π' ι μ (l : loc) (o : outcome2 val exn)
  (k : outcome2 val exn → micro A E)
  (sk : outcome2 val exn → microvx) (m' : micro A E) :
  σ !! l = Some (K sk) →
  wp_step (σ, π, Stop CResume (l, o) k, ι) (σ', π', m', μ) →
  σ' = <[l:=Shot]> σ ∧ m' = try2 (sk o) k ∧ π' = π ∧ μ = [].
Proof.
  intros Hlookup Hstep.
  destruct_wp_step.
  repeat split; auto.
  by unfold step_resume_1; rewrite Hlookup.
  by unfold step_resume_2; rewrite Hlookup.
Qed.

Lemma invert_can_step_wp_step {A E} σ π (m : micro A E) ι π' m' μ σ' :
  wp_step (σ, π, m, ι) (σ', π', m', μ) ->
  can_step (σ, m) ->
  step (σ, m) (σ', m') ∧
    π = π' ∧
    μ = [].
Proof.
  intros Hwpstep Hstep.
  destruct_wp_step; repeat constructor; auto; try solve [ exfalso; eauto with invert_can_step ].
  eapply StepWrap; [ eassumption | reflexivity ].
  eapply StepShallowWrap; [ eassumption | reflexivity ].
Qed.

Local Ltac invert_try2 :=
  match goal with
  | h: step (_, try2 _ _) (_, _) |- _ => apply invert_step_try2 in h as (? & ? & ->)
  end.

Lemma invert_wp_step_try2 {A B E' E} σ π m (k : outcome2 A E' -> micro B E) ι σ' π' m' μ :
  wp_step (σ, π, try2 m k, ι) (σ', π', m', μ) ->
  can_step (σ, m) ->
  ∃ m'', wp_step (σ, π, m, ι) (σ', π, m'', []) ∧ m' = try2 m'' k.
Proof.
  intros Hwp Hstep.
  destruct m; intros;
    destruct_wp_step;
    try solve [ exfalso; eauto with invert_can_step ];
    eexists; (split; [ apply BaseS; eauto with step | eauto with try2_algebraic try_try ]).
Qed.
