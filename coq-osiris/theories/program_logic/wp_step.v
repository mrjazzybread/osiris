From stdpp Require Import gmap.
From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval step.

From iris.base_logic.lib Require Import iprop.

Section wp_step.

  Context {Σ : gFunctors}.

  Definition is_outcome {A X} (m : micro A X) :=
    match m with
    | Ret v => Some (O2Ret v)
    | Throw v => Some (O2Throw v)
    | _ => None
    end.

  Definition th_config A X : Type := store * (thpool A X) * thread.
  Definition th_config_step A X : Type := store * (thpool A X) * list (thread * micro A X).

  Inductive wp_step : ∀ A X, th_config A X -> th_config_step A X -> Prop :=
  | BaseS : ∀ {A X} (m : micro A X) σ m' σ' (π : thpool A X) ι,
      π !! ι = Some m ->
      step (σ, m) (σ', m') ->
      wp_step A X (σ, π, ι) (σ', <[ ι := m' ]> π, [])
  | ForkS : ∀ σ π ι v1 v2 (k : outcome2 val exn -> micro val exn) ι',
      π !! ι = Some (Stop CFork (v1, v2) k) ->
      π !! ι' = None ->
      wp_step val exn
        (σ, π, ι)
        (σ, @insert _ _ _ insert_thpool ι' (call v1 v2)
              (@insert _ _ _ insert_thpool ι (continue k (VThread ι')) π), [(ι', call v1 v2)])
  | JoinS : ∀ σ (π : thpool val exn) ι (k : outcome2 val exn -> micro val exn) o ι',
      π !! ι = Some (Stop CJoin ι' k) ->
      (@lookup _ _ _ lookup_thpool ι' π) ≫= is_outcome = Some o ->
      wp_step val exn
        (σ, π, ι)
        (σ, <[ ι := k o ]> π, [])
  | SelfS : ∀ {A X} σ π ι u (k : outcome2 val exn -> micro A X),
      π !! ι = Some (Stop CSelf u k) ->
      wp_step A X
        (σ, π, ι)
        (σ, <[ ι := continue k (VThread ι) ]> π, [])
  .

  Global Arguments wp_step {A X}.

End wp_step.

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
  lazymatch goal with
    h1: ?π !! ?ι = Some ?m, h2: ?π !! ?ι = Some ?m' |- _ =>
      rewrite h2 in h1; try discriminate h1; inversion_clear h1;
      try (subst m || subst m')
  end;
  (* We will often conclude that the list of forked threads is empty. *)
  try rewrite bi.sep_emp.


Section can_progress.

  Context {Σ : gFunctors}.

(* -------------------------------------------------------------------------- *)

  Definition can_progress {A E} (c : th_config A E) :=
    match c with
    | (_, π, ι) =>
        match π !! ι with
        | Some (Stop CJoin ι' k) => ι' ∈ dom π
        | Some _ => ∃ c', wp_step c c'
        | None => False
        end
    end.

  Lemma invert_can_progress {A E} σ π ι :
    @can_progress A E (σ, π, ι) ->
    ∃ m, π !! ι = Some m ∧
    ((∃ ι' k, m = Stop CJoin ι' k ∧ ι' ∈ dom π) ∨
      (∃ v1 v2 k, m = Stop CFork (v1, v2) k) ∨
      (∃ u k, m = Stop CSelf u k) ∨
      (can_step (σ, m))).
  Proof.
    intros Hcp.
    unfold can_progress in Hcp.
    case (π !! ι) eqn:Hlookup in Hcp; last contradiction.
    exists m; split; [ assumption | ].
    (* Cases on the micro computation. *)
    destruct m;
      (* If that computation is a Stop, destruct the code *)
      try destruct_code;
      (* Generally try to invert Hcp *)
      try (
          destruct Hcp as ([[σ' π'] ι'] & Hcp);
          dependent destruction Hcp;
          rewrite Hlookup in H;
          inversion H; subst;
          destruct_step; auto with step can_step);
      (* There remains some cases *)
      try solve [(do 3 right; auto with step can_step)].

    (* Only the concurrent [Stop] cases are left. *)
    - right; left. destruct x. repeat eexists.
    - left. repeat eexists. apply Hcp.
    - right; right; left. repeat eexists; apply Hcp.
  Qed.

  Arguments can_progress : simpl never.

  Lemma can_step_can_progress {A E} σ (m : micro A E) :
    ∀ π ι,
      π !! ι = Some m ->
      can_step (σ, m) ->
      can_progress (σ, π, ι).
  Proof.
    intros π ι Hlookup ([σ' m'] & Hstep).
    unfold can_progress; rewrite Hlookup.
    destruct_step;
      eexists (_, <[ ι := _ ]> π, []);
      by (eapply BaseS; eauto with step can_step).
    Unshelve. apply b.
  Qed.

  Lemma can_progress_fork σ π x (k : _ -> micro val exn) ι :
    π !! ι = Some (Stop CFork x k) ->
    can_progress (σ, π, ι).
  Proof.
    intros Hlookup.
    destruct x.
    assert (exists ι', π !! ι' = None) as [ι' Hι'].
    { exists (fresh (dom π)).
      apply (fin_map_dom.not_elem_of_dom_1 π (fresh (dom π))).
      apply fin_sets.is_fresh. }
    unfold can_progress; rewrite Hlookup.
    eexists. eapply ForkS; eassumption.
  Qed.

  Lemma can_progress_join σ π ι' (k : _ -> micro val exn) ι s :
    π !! ι = Some (Stop CJoin ι' k) ->
    π !! ι' = Some s ->
    can_progress (σ, π, ι).
  Proof.
    intros Hlookup Hπ; simpl.
    unfold can_progress; rewrite Hlookup.
    apply (elem_of_dom π ι').
    exists s; assumption.
  Qed.

  Lemma inv_can_progress_join {A E} σ π ι' (k : _ -> micro A E) ι :
    π !! ι = Some (Stop CJoin ι' k) ->
    can_progress (σ, π, ι) ->
    ∃ s, π !! ι' = Some s.
  Proof.
    intros Hlookup Hprog; simpl.
    apply (elem_of_dom π ι').
    unfold can_progress in Hprog; rewrite Hlookup in Hprog.
    apply Hprog.
  Qed.

  Lemma can_progress_self {A E} σ π u (k : _ -> micro A E) ι :
    π !! ι = Some (Stop CSelf u k) ->
    can_progress (σ, π, ι) .
  Proof.
    intros Hlookup.
    unfold can_progress; rewrite Hlookup.
    eexists; apply SelfS with (u := u); eauto.
  Qed.

  Lemma invert_wp_step_resume {A E : Type} (σ σ' : store) π π' ι μ (l : loc) (o : outcome2 val exn)
    (k : outcome2 val exn → micro A E)
    (sk : outcome2 val exn → microvx) :
    π !! ι = Some (Stop CResume (l, o) k) ->
    σ !! l = Some (K sk) →
    @wp_step A E (σ, π, ι) (σ', π', μ) →
      σ' = <[l:=Shot]> σ ∧
      π' = <[ ι := try2 (sk o) k ]> π ∧
      μ = [].
  Proof.
    intros Hlookup' Hlookup Hstep.
    dependent destruction Hstep;
    rewrite H in Hlookup';
    inversion Hlookup'; subst m.
    destruct_step.
    repeat split; auto.
    - unfold step_resume_1. rewrite Hlookup. reflexivity.
    - unfold step_resume_2. rewrite Hlookup. reflexivity.
  Qed.

  Lemma invert_can_step_wp_step {A E} σ π (m : micro A E) ι π' m' μ σ' :
    π !! ι = Some m ->
    π' !! ι = Some m' ->
    @wp_step A E (σ, π, ι) (σ', π', μ) ->
    can_step (σ, m) ->
    step (σ, m) (σ', m') ∧
      π' = <[ ι := m' ]> π ∧
      μ = [].
  Proof.
    intros Hlookup Hlookup' Hwpstep Hstep.
    dependent destruction Hwpstep;
      rewrite H in Hlookup; inversion Hlookup; subst m;
      try solve [ exfalso; eauto with invert_can_step ].
    rewrite lookup_insert in Hlookup'. inversion Hlookup'; subst m'0.
    clear Hlookup Hstep Hlookup'.
    done.
  Qed.

  Local Ltac invert_try2 :=
    match goal with
    | h: step (_, try2 _ _) (_, _) |- _ => apply invert_step_try2 in h as (? & ? & ->)
    end.

  Lemma invert_wp_step_try2 {A B E' E} σ π m m' (k : outcome2 A E' -> micro B E) ι σ' π' μ :
    π !! ι = Some (try2 m k) ->
    π' !! ι = Some m' ->
    @wp_step B E (σ, π, ι) (σ', π', μ) ->
    can_step (σ, m) ->
    ∃ m'', m' = try2 m'' k.
  Proof.
    intros Hlookup Hlookup' Hwp Hstep.
    dependent destruction Hwp;
      rewrite H in Hlookup; inversion Hlookup; subst;
      try solve [ exfalso; eauto with invert_can_step ].
    { apply invert_step_try2 in H0; last assumption.
      destruct H0 as (? & Hstep' & ->).
      rewrite lookup_insert in Hlookup'; inversion Hlookup'; subst.
      eexists; reflexivity. }
    - symmetry in H2.
      apply invert_try2_eq_stop in H2 as (k' & -> & ->);
        try (intros ? ->);
      exfalso; eauto with invert_can_step.
    - symmetry in H2.
      apply invert_try2_eq_stop in H2 as (k' & -> & ->);
        try (intros ? ->);
        exfalso; eauto with invert_can_step.
    - symmetry in H1.
      apply invert_try2_eq_stop in H1 as (k' & -> & ->);
        try (intros ? ->);
        exfalso; eauto with invert_can_step.
  Qed.

End can_progress.

Opaque can_progress.

Global Hint Resolve
  can_progress_join
  can_progress_fork
  can_progress_self : can_progress.
