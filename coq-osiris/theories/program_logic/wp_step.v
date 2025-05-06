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
.

Ltac destruct_wp_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try match goal with h: wp_step (?σ, ?π, Stop ?c ?x ?k, ?ι) ?m' |- _ =>
                        remember x
    end;
  match goal with h: wp_step ?m ?m' |- _ =>
                    dependent destruction h
  end;
  try destruct_step
.

(* -------------------------------------------------------------------------- *)

Definition not_stuck {A E} (c : th_config A E) :=
  match c with
  | (_, π, Stop CJoin ι' k, _) => ι' ∈ dom π
  | (_, _, Stop CDie o _, _) => True
  | _ => ∃ c', wp_step c c'
  end.

Lemma can_step_not_stuck {A E} σ (m : micro A E) :
  ∀ π ι,
    can_step (σ, m) ->
    not_stuck (σ, π, m, ι).
Proof.
  intros π ι ([σ' m'] & Hstep).
  destruct_step;
  eexists (_, π, _, []);
    by (apply BaseS; eauto with step can_step).
  Unshelve. apply b.
Qed.

Lemma not_stuck_fork {A E} σ π x (k : _ -> micro A E) ι :
  not_stuck (σ, π, (Stop CFork x k), ι).
Proof.
  destruct x.
  assert (exists ι', π !! ι' = None) as [ι' Hι'].
  { exists (fresh (dom π)).
    apply fin_map_dom.not_elem_of_dom_1.
    apply fin_sets.is_fresh. }
  eexists. apply ForkS.
  apply Hι'.
Qed.

Lemma not_stuck_join {A E} σ π ι' (k : _ -> micro A E) ι o :
  π !! ι' = Some o ->
  not_stuck (σ, π, (Stop CJoin ι' k), ι).
Proof.
  intros Hπ; simpl.
  apply elem_of_dom.
  exists o; assumption.
Qed.

Lemma not_stuck_self {A E} σ π u (k : _ -> micro A E) ι :
  not_stuck (σ, π, (Stop CSelf u k), ι) .
Proof.
  eexists. apply SelfS.
Qed.

Global Hint Resolve not_stuck_join not_stuck_fork not_stuck_self : not_stuck.

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
