From Coq.Logic Require Import FunctionalExtensionality.
From ITree Require Import ITree Eqit Exception.
Require Import lang monads free eval handle div spec wp.

(* This file establishes that the [spec] monad offers a sound abstract
   interpretation of the [div] monad. *)

(* -------------------------------------------------------------------------- *)

(* A computation [m] is safe with respect to a postcondition [φ] if
   1- [m] does not fail; and 2- if [m] produces a value [v] then [φ v]
   holds. This is a partial correctness interpretation: divergence is
   permitted. *)

(* We first define what it means to be safe for [n] steps. *)

Fixpoint initially_safe {A} (n : nat) (m : div A) (φ : A → Prop) : Prop :=
  match n, observe m with
  | 0, _ =>
      (* Every computation is safe for zero steps. *)
      True
  | _, RetF v =>
      (* The computation produces a value [v]. *)
      φ v
  | S n, TauF m =>
      (* The computation performs a step and continues. *)
      initially_safe n m φ
  | _, VisF _tt _k =>
      (* The computation fails. *)
      False
  end.

(* A paraphrase lemma. *)

Lemma unfold_initially_safe_S {A} (n : nat) (m : div A) (φ : A → Prop) :
  initially_safe (S n) m φ =
  match observe m with
  | RetF v =>
      φ v
  | TauF m =>
      initially_safe n m φ
  | VisF _tt _k =>
      False
  end.
Proof.
  reflexivity.
Qed.

(* If, for every [n], a computation is safe for [n] steps,
   then this computation is safe. *)

Definition safe {A} (m : div A) (φ : A → Prop) :=
  ∀ n, initially_safe n m φ.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [initially_safe (S n) m φ] under a hypothesis about
   the observable behavior of the computation [m]. *)

Lemma invert_initially_safe_RetF {A} {n} {m : div A} {a} (φ : A → Prop) :
  initially_safe (S n) m φ →
  observe m = RetF a →
  φ a.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

Lemma invert_initially_safe_TauF {A} {n} {m m' : div A} {φ : A → Prop} :
  initially_safe (S n) m φ →
  observe m = TauF m' →
  initially_safe n m' φ.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

Lemma invert_initially_safe_VisF {A X} {n} {m : div A} {e} {k : X → div A} {φ : A → Prop} :
  initially_safe (S n) m φ →
  observe m = VisF e k →
  False.
Proof.
  intros Hsafe Hm. simpl in Hsafe. rewrite Hm in Hsafe. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [safe m φ] under a hypothesis about the observable
   behavior of the computation [m]. *)

Lemma invert_safe_RetF {A} {m : div A} {a} (φ : A → Prop) :
  safe m φ →
  observe m = RetF a →
  φ a.
Proof.
  unfold safe. intros Hsafe Hm. specialize (Hsafe 1).
  eauto using (invert_initially_safe_RetF φ).
Qed.

Lemma invert_safe_TauF {A} {m m' : div A} {φ : A → Prop} :
  safe m φ →
  observe m = TauF m' →
  safe m' φ.
Proof.
  unfold safe. eauto using invert_initially_safe_TauF.
Qed.

Lemma invert_safe_VisF {A X} {m : div A} {e} {k : X → div A} {φ : A → Prop} :
  safe m φ →
  observe m = VisF e k →
  False.
Proof.
  unfold safe. intros Hsafe Hm. specialize (Hsafe 1).
  eauto using invert_initially_safe_VisF.
Qed.

(* -------------------------------------------------------------------------- *)

(* Two high-level inversion lemmas. *)

Lemma invert_safe_ret {A} (a : A) (φ : A → Prop) :
  safe (ret a) φ →
  φ a.
Proof.
  intros Hsafe. specialize (invert_safe_RetF _ Hsafe eq_refl). tauto.
Qed.

Lemma invert_safe_mzero {A} (φ : A → Prop) :
  safe mzero φ →
  False.
Proof.
  intros Hsafe. specialize (invert_safe_VisF Hsafe eq_refl). tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* An alternative definition of [safe] as a coinductive predicate can be
   given. This definition is technically not needed, but we offer it and
   prove its equivalence, as a sanity check. *)

CoInductive alt_safe {A} : div A → (A → Prop) → Prop :=
  | AltSafeRetF :
      ∀ m v (φ : A → Prop),
      observe m = RetF v →
      φ v →
      alt_safe m φ
  | AltSafeTauF :
      ∀ m m' (φ : A → Prop),
      observe m = TauF m' →
      alt_safe m' φ →
      alt_safe m φ
.

(* The following lemmas prove that [safe] and [alt_safe] are equivalent. *)

Lemma safe_implies_alt_safe {A} (φ : A → Prop) :
  ∀ m,
  safe m φ →
  alt_safe m φ.
Proof.
  cofix CIH.
  intro m; case_eq (observe m); [ clear CIH | | clear CIH ].
  { eauto using (invert_safe_RetF φ), AltSafeRetF. }
  { intros; eapply AltSafeTauF; eauto using invert_safe_TauF. }
  { intros. elimtype False. eauto using invert_safe_VisF. }
Qed.

Lemma alt_safe_implies_initially_safe {A} (φ : A → Prop) :
  ∀ n m,
  alt_safe m φ →
  initially_safe n m φ.
Proof.
  induction n; simpl; [ tauto |].
  intros m Hsafe.
  destruct Hsafe;
  match goal with Hm: observe m = _ |- _ => rewrite Hm end;
  eauto.
Qed.

Lemma alt_safe_implies_safe {A} (φ : A → Prop) :
  ∀ m, alt_safe m φ → safe m φ.
Proof.
  unfold safe. eauto using alt_safe_implies_initially_safe.
Qed.

Lemma alt_safe_iff_safe {A} (φ : A → Prop) :
  ∀ m, alt_safe m φ ↔ safe m φ.
Proof.
  split; eauto using safe_implies_alt_safe, alt_safe_implies_safe.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [n1 ≤ n2] holds, then a computation that is safe for [n2] steps is
   also safe for [n1] steps. *)

Lemma initially_safe_monotonic {A} (φ : A → Prop) :
  ∀ n1 n2 m,
  initially_safe n2 m φ →
  n1 ≤ n2 →
  initially_safe n1 m φ.
Proof.
  induction n1; simpl; intros n2 m Hsafe Hleq; [ tauto |].
  destruct n2 as [| n2 ]; [ lia |].
  simpl in Hsafe.
  destruct (observe m); eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [φ] entails [φ'], then a computation that is safe with respect to [φ]
   is also safe with respect to [φ']. *)

Lemma initially_safe_covariant {A} (φ φ' : A → Prop) :
  (∀ a, φ a → φ' a) →
  ∀ n m,
  initially_safe n m φ →
  initially_safe n m φ'.
Proof.
  induction n; simpl; intros; [ tauto |].
  destruct (observe m); eauto.
Qed.

Lemma safe_covariant {A} (m : div A) (φ φ' : A → Prop) :
  (∀ a, φ a → φ' a) →
  safe m φ → safe m φ'.
Proof.
  unfold safe. eauto using initially_safe_covariant.
Qed.

(* Because [safe m] is covariant in [φ], it can be viewed as an inhabitant
   of the [spec] monad. *)

Program Definition safety {A} (m : div A) : spec A :=
  safe m.
Next Obligation.
  simpl. eauto using safe_covariant.
Qed.

Lemma unfold_safety {A} (m : div A) (φ : A → Prop) :
  safety m ∋ φ ↔ safe m φ.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO WIP the relation [admits] should now disappear: [admits m s]
   is just [s ≤ safety m], I think. *)

(* The relation [admits m s] relates a computation [m] in the [div] monad
   and a specification [s] in the [spec] monad. This relation means that the
   specification [s] is a sound description of the computation [m]. This
   relation holds when every postcondition [φ] that is contained in [s] is
   respected by [m]. *)

Definition admits {A} (m : div A) (s : spec A) :=
  ∀ φ, s ∋ φ → safe m φ.

(* A step-indexed version of [admits] seems necessary in the proof of
   the lemma [admits_iter]. *)

Definition initially_admits {A} n (m : div A) (s : spec A) :=
  ∀ φ, s ∋ φ → initially_safe n m φ.

(* The four properties defined above form a diamond. *)

Lemma unfold_admits {A} (m : div A) (s : spec A) :
  admits m s ↔
  ∀ n, initially_admits n m s.
Proof.
  unfold admits, initially_admits. firstorder.
Qed.

Lemma unfold_admits_one_way {A} (m : div A) (s : spec A) :
  admits m s →
  ∀ n, initially_admits n m s.
Proof.
  rewrite unfold_admits. eauto.
Qed.

(* [initially_admits] is monotonic in its step index. *)

Lemma initially_admits_monotonic {A} (s : spec A) :
  ∀ n1 n2 m,
  initially_admits n2 m s →
  n1 ≤ n2 →
  initially_admits n1 m s.
Proof.
  unfold initially_admits.
  eauto using initially_safe_monotonic.
Qed.

(* -------------------------------------------------------------------------- *)

(* [ret a] and [ret a] are related. That is, the computation [ret a] admits
   the specification [ret a]. *)

Lemma admits_ret {A} :
  ∀ (a : A),
  admits (ret a) (ret a).
Proof.
  intros a φ. simpl. intros Hφa n.
  destruct n as [| n ]; simpl; eauto.
Qed.

(* TODO *)

Lemma safety_ret {A} :
  ∀ (a : A),
  safety (ret a : div A) = (ret a : spec A).
Proof.
  intros. eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  split; intros H.
  { simpl. eapply invert_safe_ret. assumption. }
  { simpl in H. intros [| n]; simpl; eauto. }
Qed.

(* [mzero] and [mzero] are related. *)

Lemma admits_mzero {A} :
  @admits A mzero mzero.
Proof.
  unfold mzero. simpl.
  unfold div_mzero, spec_fail.
  unfold admits. simpl. tauto.
Qed.

(* TODO *)

Lemma safety_mzero {A} :
  safety (mzero : div A) = (mzero : spec A).
Proof.
  eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  split; intros H.
  { simpl. eapply invert_safe_mzero. eauto. }
  { simpl in H. tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [admits m s] under a hypothesis about the observable
   behavior of the computation [m]. *)

(* We state these lemmas in a strong form where they are able to exploit the
   weak judgement [initially_admits], as opposed to the stronger judgement
   [admits]. *)

(* If [ret a] admits spec [s] then [ret a ≤ s]. That is, [ret a] is the best
   specification for [ret a]. *)

Lemma invert_admits_RetF {A} n (m : div A) (s : spec A) (a : A) φ :
  initially_admits (S n) m s →
  observe m = RetF a →
  s ∋ φ →
  φ a.
Proof.
  unfold initially_admits. eauto using (invert_initially_safe_RetF φ).
Qed.

(* [throw ()] cannot admit a nonempty specification. That is, if [throw ()]
   admits the specification [s] and if [s] is nonempty, then a contradiction
   is obtained. *)

Lemma invert_admits_VisF {A X} n (m : div A) (s : spec A) e (k : X → div A) φ :
  initially_admits (S n) m s →
  observe m = VisF e k →
  s ∋ φ →
  False.
Proof.
  unfold initially_admits. eauto using invert_initially_safe_VisF.
Qed.

(* The relation [admits m s] is stable under reduction of [m] to [m']. *)

Lemma invert_admits_TauF {A} n (m m' : div A) (s : spec A) :
  initially_admits (S n) m s →
  observe m = TauF m' →
  initially_admits n m' s.
Proof.
  unfold initially_admits. eauto using invert_initially_safe_TauF.
Qed.

(* -------------------------------------------------------------------------- *)

(* Interaction of safety and [bind]. *)

(* If [m1] is safe for [n1] steps and [m2 a] is safe for [n2] steps then
   [bind m1 m2] is safe for [min n1 n2] steps. (One cannot expect to obtain
   safety for [n1+n2] steps! To see this, consider the case where [n1] is
   zero.) This is stated, in a simpler way, by the following lemma. *)

Lemma initially_safe_bind_aux_1 {A B} (m2 : A → div B) :
  ∀ n (m1 : div A) (φ : B → Prop),
  initially_safe n m1 (λ a, initially_safe n (m2 a) φ) →
  initially_safe n (bind m1 m2) φ.
Proof.
  induction n; [tauto |]. intros m1 φ Hsafe.
  (* Expose two occurrences of [observe m1]. *)
  rewrite unfold_bind.
  unfold initially_safe at 1 in Hsafe;
  fold @initially_safe in Hsafe.
  (* Proceed by cases on [m1]. Three cases arise. *)
  destruct (observe m1); [ clear IHn | | clear IHn ].

  (* Case: [m1] is [ret a]. *)
  { tauto. }

  (* Case: [m1] is [skip m'1]. *)
  { (* The goal is to prove that [bind m'1 m2] is safe for [n] steps. *)
    simpl.
    (* This follows from the induction hypothesis and from the fact that
       [initially_safe] is covariant in its postcondition and monotonic
       in its step index. *)
    eapply IHn; clear IHn.
    eapply initially_safe_covariant; [| exact Hsafe ]; clear Hsafe.
    intros a Hm2a.
    eapply initially_safe_monotonic; [ exact Hm2a |].
    lia. }

  (* Case: [m1] fails. *)
  { (* The goal is to show that this cannot happen. *)
    simpl. tauto. }

Qed.

(* Conversely, if [bind m1 m2] is safe for [n1 + n2] steps then [m1] is safe
   for [n1] steps and [m2 a] is safe for [n2] steps. *)

Lemma initially_safe_bind_aux_2 {A B} (m2 : A → div B) :
  ∀ n1 n2 (m1 : div A)  (φ : B → Prop),
  initially_safe (n1 + n2) (bind m1 m2) φ →
  initially_safe n1 m1 (λ a, initially_safe n2 (m2 a) φ).
Proof.
  induction n1; intros n2 m1 φ.
  (* The base case is trivial. *)
  { intros _. simpl. tauto. }

  (* Expose two occurrences of [observe m1]. *)
  rewrite unfold_bind.
  unfold initially_safe at 2; fold @initially_safe.
  (* Proceed by cases on [m1]. Three cases arise. *)
  destruct (observe m1); [ clear IHn1 | | clear IHn1 ].

  (* Case: [m1] is [ret a]. *)
  { eauto using initially_safe_monotonic with lia. }

  (* Case: [m1] is [skip m'1]. *)
  { simpl. intros Hsafe. apply IHn1. exact Hsafe. }

  (* Case: [m1] fails. *)
  { intros Hsafe. eauto using invert_initially_safe_VisF. }

Qed.

(* The intersection rule of Hoare logic: if for every [x] the computation
   [m] admits the postcondition [φ x], then [m] admits the postcondition
   [∀ x, φ x]. *)

Lemma initially_safe_intersection {A X} {_ : Inhabited X} (φ : X → A → Prop) :
  ∀ n m,
  (∀ x, initially_safe n m (φ x)) →
  initially_safe n m (λ a, ∀ x, φ x a).
Proof.
  induction n; [ simpl; tauto |]; intros m Hsafe.

  (* Expose two occurrences of [observe m]. *)
  unfold initially_safe in *; fold @initially_safe in *.
  (* Proceed by cases on [m]. Three cases arise. *)
  destruct (observe m); [ clear IHn | | clear IHn ].

  (* Case: [m] is [ret a]. *)
  { assumption. }
  (* Case: [m] is [skip m']. *)
  { eauto. }
  (* Case: [m1] fails. *)
  (* The fact that the type [X] is inhabited is exploited. *)
  { specialize (Hsafe inhabitant). tauto. }
Qed.

(* A sequence [bind m1 m2] is safe if and only if [m1] and [m2] are safe.
   The safety of [m2 a] is stated inside the postcondition of [m1], so it
   must hold only in the situations where [m1] terminates. *)

Lemma safe_bind {A B} (m1 : div A) (m2 : A → div B) (φ : B → Prop) :
  safe (bind m1 m2) φ ↔ safe m1 (λ a, safe (m2 a) φ).
Proof.
  unfold safe.
  split; intros Hsafe.
  (* This implication corresponds to the completeness of the program logic.
     It is interesting to note that the intersection rule is used here. *)
  { intros n1.
    eapply initially_safe_intersection. intros n2.
    eapply initially_safe_bind_aux_2.
    eapply Hsafe. }
  (* This implication corresponds to the soundness of the program logic. *)
  { intros n.
    eapply initially_safe_bind_aux_1.
    eapply initially_safe_covariant; [| eauto ]; intros a Hm2a.
    eapply Hm2a. }
Qed.

(* [safety] commutes with [bind]. *)

Lemma safety_bind {A B} (m1 : div A) (m2 : A → div B) :
  safety (bind m1 m2) = bind (safety m1) (λ a, safety (m2 a)).
Proof.
  eapply prove_spec_eq_ext. intros φ. rewrite unfold_safety. apply safe_bind.
Qed.

(* -------------------------------------------------------------------------- *)

(* [bind] preserves relatedness. *)

(* This is a beautiful proof. *)

(* We state this lemma in a strong form by requiring only the weak
   hypothesis [∀ a, initially_admits n (m2 a) (s2 a)] instead of the stronger
   hypothesis [∀ a, admits (m2 a) (s2 a)]. The weak form of this lemma would
   suffice to prove [admits_bind]. However, the strong form of this
   lemma is needed in the proof of [admits_iter]. *)

Lemma initially_admits_bind {A B}
  (m2 : A → div B) (s1 : spec A) (s2 : A → spec B) φ :
  bind s1 s2 ∋ φ →
  ∀ n (m1 : div A),
  initially_admits n m1 s1 →
  (∀ a : A, initially_admits n (m2 a) (s2 a)) →
  initially_safe n (bind m1 m2) φ.
Proof.
  intros Hbφ.
  induction n; intros m1 Hms1 Hms2; [ simpl; tauto |].
  (* The goal is to prove that [bind m1 m2] is safe for [n+1] steps. *)
  rewrite unfold_bind.
  (* Proceed by cases on [m1]. Three cases arise. *)
  case_eq (observe m1).

  (* Case: [m1] is [ret a]. *)
  { clear IHn. intros a Hm1.
    (* The goal is to prove that [m2 a] is safe for [n + 1] steps. *)
    (* From the fact that [ret a] admits the specification [s1],
       and from the fact that [s1] contains the postcondition
       [λ a, s2 a ∋ φ], we deduce that [s2 a ∋ φ] holds. *)
    unfold bind in Hbφ; simpl in Hbφ.
    assert (s2 a ∋ φ).
    { apply (invert_admits_RetF _ m1 s1 a _ Hms1 Hm1 Hbφ). }
    clear Hms1 Hm1 Hbφ.
    specialize (Hms2 a).
    (* The goal follows by definition of [initially_admits]. *)
    eauto. }

  (* Case: [m1] is [Skip m'1]. *)
  { intros m'1 Hm1.
    (* The goal is to prove that [bind m'1 m2] is safe for [n] steps. *)
    simpl.
    (* This follows from the induction hypothesis and from the fact
       that [admits] is stable under reduction. *)
    eapply IHn.
    { eauto using invert_admits_TauF. }
    { eauto using initially_admits_monotonic with lia. }
  }

  (* Case: [m1] fails. *)
  { clear IHn. intros X e k Hm1.
    (* The goal is to show that this cannot happen. *)
    simpl.
    destruct e as (u). destruct u.
    unfold bind in Hbφ; simpl in Hbφ.
    eauto using invert_admits_VisF. }

Qed.

Lemma admits_bind {A B}
  (m1 : div A) (m2 : A → div B) (s1 : spec A) (s2 : A → spec B) :
  admits m1 s1 →
  (∀ a, admits (m2 a) (s2 a)) →
  admits (bind m1 m2) (bind s1 s2).
Proof.
  intros.
  rewrite unfold_admits. unfold initially_admits.
  eauto using initially_admits_bind, unfold_admits_one_way.
Qed.

(* -------------------------------------------------------------------------- *)

(* [skip] preserves relatedness. *)

Lemma safe_skip {A} (m : div A) (φ : A → Prop) :
  safe (skip m) φ ↔ safe m φ.
Proof.
  unfold safe. split; intros Hsafe n.
  { specialize (Hsafe (S n)). tauto. }
  { destruct n as [| n ]; simpl; eauto. }
Qed.

Lemma safety_skip {A} (m : div A) :
  safety (skip m) = safety m.
Proof.
  eapply prove_spec_eq_ext. intros φ.
  rewrite !unfold_safety.
  apply safe_skip.
Qed.

Lemma initially_admits_skip {A} n (m : div A) (s : spec A) :
  initially_admits n m s →
  initially_admits (S n) (skip m) (skip s).
Proof.
  unfold initially_admits.
  intros Hms.
  unfold skip, monadskip_div, monadskip_spec, div_skip.
  intros φ Hsφ. simpl. eauto.
Qed.

Lemma admits_skip {A} (m : div A) (s : spec A) :
  admits m s →
  admits (skip m) (skip s).
Proof.
  rewrite !unfold_admits.
  intros. destruct n as [| n].
  { unfold initially_admits. simpl. eauto. }
  { eauto using initially_admits_skip. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [iter] preserves relatedness. *)

Lemma initially_admits_iter {I A}
  (body1 : I → div (I + A))
  (body2 : I → spec (I + A)) :
  (∀ i, admits (body1 i) (body2 i)) →
  ∀ n i φ,
  iter body2 i ∋ φ →
  initially_safe n (iter body1 i) φ.
Proof.
  intros Hbody.
  induction n; [ simpl; tauto |].
  intros i φ Hφ.
  erewrite unfold_iter by typeclasses eauto.
  erewrite unfold_iter in Hφ by typeclasses eauto.
  eapply initially_admits_bind.
  { eexact Hφ. }
  { eauto using unfold_admits_one_way. }
  (* We must study two cases: continuing and finishing. *)
  clear i φ Hφ. intros [ i | a ].
  (* Case: the loop body wants to continue. *)
  { eapply initially_admits_skip.
    unfold initially_admits.
    eapply IHn. }
  (* Case: the loop body is done. *)
  { eauto using unfold_admits_one_way, admits_ret. }
Qed.

Lemma admits_iter {I A}
  (body1 : I → div (I + A))
  (body2 : I → spec (I + A)) :
  (∀ i, admits (body1 i) (body2 i)) →
  ∀ i, admits (iter body1 i) (iter body2 i).
Proof.
  intros.
  rewrite unfold_admits.
  unfold initially_admits.
  eauto using initially_admits_iter.
Qed.

(* -------------------------------------------------------------------------- *)

(* [handle] preserves relatedness. *)

(* This is a beautiful abstract proof. *)

Lemma admits_handle {A} (m : free A) :
  admits (handle m) (handle m).
Proof.
  unfold handle.
  apply admits_iter.
  clear m. intros m.
  unfold handle_body.
  destruct m.
  (* Case: returning a value. *)
  { apply admits_ret. }
  (* Case: hard failure. *)
  { apply admits_mzero. }
  (* Case: soft failure. *)
  { apply admits_mzero. }
  (* Case: recursive evaluation request. *)
  { destruct req. apply admits_ret. }
Qed.

(* An immediate corollary. *)

Lemma admits_run η e :
  admits (run η e) (run η e).
Proof.
  unfold run. apply admits_handle.
Qed.

(* -------------------------------------------------------------------------- *)

(* The final soundness statement follows. *)

Lemma soundness η e φ :
  wp η e φ →
  safe (run η e) φ.
Proof.
  unfold wp. apply admits_run.
Qed.

(* -------------------------------------------------------------------------- *)

Global Opaque handle.
