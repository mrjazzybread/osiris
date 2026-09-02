From stdpp Require Import relations.

(** * Labelled reduction sequences.

    Two [nsteps] already exist, and neither can be reused for a labelled
    relation over an arbitrary configuration type:

    - stdpp's ([stdpp.relations]) is over a [relation A], that is
      [R : A → A → Prop], so it carries no label at all.

    - Iris's ([iris.program_logic.language]) accumulates labels in exactly the
      shape below, but it lives in [Section language] over
      [cfg Λ = list (expr Λ) * state Λ]. A semantics whose configurations are
      not a thread list (ours uses a [gmap thread]) cannot instantiate
      [language], so its [nsteps] does not apply.

    This is Iris's definition with the configuration type and the label type
    made parameters, so that every labelled step relation in the development
    can share one copy. *)

Section lsteps.

  Context {A L : Type} (R : A → list L → A → Prop).

  (** [lsteps n x κs y]: [n] steps from [x] to [y] emitting the concatenated
      trace [κs]. *)

  Inductive lsteps : nat → A → list L → A → Prop :=
    | lsteps_refl x :
        lsteps 0 x [] x
    | lsteps_l n x y z κ κs :
        R x κ y →
        lsteps n y κs z →
        lsteps (S n) x (κ ++ κs) z.

  (** Forgetting the label. This is a plain [relation A], so stdpp's [rtc]
      applies to it directly: a reachability hypothesis then carries neither a
      step count nor a trace, which is all most clients need. *)

  Definition erased_lstep (x y : A) : Prop := ∃ κ, R x κ y.

  Lemma lsteps_once x κ y :
    R x κ y → lsteps 1 x κ y.
  Proof. intros. rewrite <- (app_nil_r κ). econstructor; [ done | constructor ]. Qed.

  Lemma lsteps_trans n1 n2 x y z κs1 κs2 :
    lsteps n1 x κs1 y →
    lsteps n2 y κs2 z →
    lsteps (n1 + n2) x (κs1 ++ κs2) z.
  Proof.
    induction 1 as [ | n x1 x2 x3 κ κs Hstep Hsteps IH ]; simpl; first done.
    intros Hsteps2. rewrite <- app_assoc.
    econstructor; [ done | by apply IH ].
  Qed.

  Lemma erased_lsteps_lsteps x y :
    rtc erased_lstep x y ↔ ∃ n κs, lsteps n x κs y.
  Proof.
    split.
    - induction 1 as [ x | x1 x2 x3 [ κ Hstep ] _ (n & κs & Hsteps) ].
      + exists 0%nat, []. constructor.
      + exists (S n), (κ ++ κs). by econstructor.
    - intros (n & κs & Hsteps). unfold erased_lstep.
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.

  Lemma erased_lstep_lsteps x y :
    erased_lstep x y → ∃ n κs, lsteps n x κs y.
  Proof. intros. apply erased_lsteps_lsteps. by apply rtc_once. Qed.

  Lemma lsteps_erased_lsteps n x κs y :
    lsteps n x κs y → rtc erased_lstep x y.
  Proof. intros. apply erased_lsteps_lsteps. by eauto. Qed.

End lsteps.

Create HintDb lsteps.
Hint Constructors lsteps : lsteps.
