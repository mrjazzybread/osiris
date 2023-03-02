From ITree Require Import ITree Eqit Exception.
Require Import lang monads free eval handle div spec.

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

(* If, for every [n], a computation is safe for [n] steps,
   then this computation is safe. *)

Definition safe {A} (m : div A) (φ : A → Prop) :=
  ∀ n, initially_safe n m φ.

(* -------------------------------------------------------------------------- *)

(* TODO it should be possible to give an alternative definition of [safe] as
   a coinductive predicate. Do it and prove the equivalence. *)

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

(* The relation [admits m s] relates a computation [m] in the [div] monad
   and a specification [s] in the [spec] monad. This relation means that the
   specification [s] is a sound description of the computation [m]. This
   relation holds when every postcondition [φ] that is contained in [s] is
   respected by [m]. *)

Definition admits {A} (m : div A) (s : spec A) :=
  ∀ φ, s ∋ φ → safe m φ.

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

(* -------------------------------------------------------------------------- *)

(* The following three lemmas are inversion lemmas. They extract information
   out of the judgement [admits m s] under a hypothesis about the observable
   behavior of the computation [m]. *)

(* If [ret a] admits spec [s] then [ret a ≤ s]. That is, [ret a] is the best
   specification for [ret a]. *)

Lemma invert_admits_RetF {A} (m : div A) (s : spec A) (a : A) φ :
  admits m s →
  observe m = RetF a →
  s ∋ φ →
  φ a.
Proof.
  unfold admits, safe. intros Hsafe Hm Hsφ.
  specialize (Hsafe φ Hsφ 1).
  simpl in Hsafe.
  rewrite Hm in Hsafe.
  tauto.
Qed.

(* [throw ()] cannot admit a nonempty specification. That is, if [throw ()]
   admits the specification [s] and if [s] is nonempty, then a contradiction
   is obtained. *)

Lemma invert_admits_Throw {A} (m : div A) (s : spec A) (k : void → div A) φ :
  admits m s →
  observe m = VisF (Throw ()) k →
  s ∋ φ →
  False.
Proof.
  (* The proof script is the same as that of the previous lemma! *)
  unfold admits, safe. intros Hsafe Hm Hsφ.
  specialize (Hsafe φ Hsφ 1).
  simpl in Hsafe.
  rewrite Hm in Hsafe.
  tauto.
Qed.

(* The relation [admits m s] is stable under reduction of [m] to [m']. *)

Lemma invert_admits_TauF {A} (m m' : div A) (s : spec A) :
  admits m s →
  observe m = TauF m' →
  admits m' s.
Proof.
  (* The proof script is almost the same as in the previous two lemmas. *)
  unfold admits, safe. intros Hsafe Hm φ Hsφ n.
  specialize (Hsafe φ Hsφ (S n)).
  simpl in Hsafe.
  rewrite Hm in Hsafe.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [bind] preserves relatedness. *)

(* This is a beautiful proof. *)

Lemma admits_bind_aux {A B}
  (m2 : A → div B) (s1 : spec A) (s2 : A → spec B) φ :
  (∀ a : A, admits (m2 a) (s2 a)) →
  bind s1 s2 ∋ φ →
  ∀ n (m1 : div A),
  admits m1 s1 →
  initially_safe n (bind m1 m2) φ.
Proof.
  intros Hms2 Hbφ.
  induction n; intros m1 Hms1; [ simpl; tauto |].
  (* The goal is to prove that [bind m1 m2] is safe for [n+1] steps. *)
  rewrite unfold_bind.
  (* Proceed by cases on [m1]. Three cases arise. *)
  case_eq (observe m1).

  (* Case: [m1] is [ret a]. *)
  { clear IHn. intros a Hm1.
    (* The goal is to prove that [m2 a] is safe for [n + 1] steps. *)
    match goal with |- ?goal =>
      change goal with (initially_safe (S n) (m2 a) φ)
    end.
    (* From the fact that [ret a] admits the specification [s1],
       and from the fact that [s1] contains the postcondition
       [λ a, s2 a ∋ φ], we deduce that [s2 a ∋ φ] holds. *)
    unfold bind in Hbφ; simpl in Hbφ.
    assert (s2 a ∋ φ).
    { apply (invert_admits_RetF m1 s1 a _ Hms1 Hm1 Hbφ). }
    clear Hms1 Hm1 Hbφ.
    specialize (Hms2 a).
    (* The goal follows by definition of [admits]. *)
    unfold admits, safe in Hms2. eauto. }

  (* Case: [m1] is [Skip m'1]. *)
  { intros m'1 Hm1.
    (* The goal is to prove that [bind m'1 m2] is safe for [n] steps. *)
    simpl.
    (* This follows from the induction hypothesis and from the fact
       that [admits] is stable under reduction. *)
    eapply IHn.
    eauto using invert_admits_TauF. }

  (* Case: [m1] fails. *)
  { clear IHn. intros X e k Hm1.
    (* The goal is to show that this cannot happen. *)
    simpl.
    destruct e as (u). destruct u.
    unfold bind in Hbφ; simpl in Hbφ.
    eauto using invert_admits_Throw. }

Qed.

Lemma admits_bind {A B} :
  ∀ (m1 : div A) (m2 : A → div B) (s1 : spec A) (s2 : A → spec B),
  admits m1 s1 →
  (∀ a, admits (m2 a) (s2 a)) →
  admits (bind m1 m2) (bind s1 s2).
Proof.
  unfold admits at 3. unfold safe.
  eauto using admits_bind_aux.
Qed.
