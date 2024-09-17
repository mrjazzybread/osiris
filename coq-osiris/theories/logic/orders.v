Require Import stdpp.orders.
From iris.base_logic.lib Require Import iprop.

(* This file establishes some properties of ordering relations. *)

(* -------------------------------------------------------------------------- *)

(* Definition of a preorder over carrier type [A], where the ordering is
    persistent. *)

Section PreOrder.

  Class preorder Σ (A : Type)  :=
    { order : A -d> A -d> iProp Σ;
      refl : (⊢ ∀ a, order a a)%I;
      trans : (⊢ ∀ a b c, order a b -∗ order b c -∗ order a c)%I;
      order_persistent :: forall a b, Persistent (order a b)}.

  Notation "P ⊆ Q" := (order P Q)%I : bi_scope.

End PreOrder.

(* -------------------------------------------------------------------------- *)

(* Some properties of strict orders. *)

Section StrictOrders.

  Variable A : Type.
  Variable lt : A → A → Prop.
  Context `{Slt : StrictOrder A lt}.
  Notation "x '<' y" := (lt x y).

  (* A strict order is irreflexive: [x < x] is a contradiction. *)

  Lemma strict_order_irreflexive x :
    x < x → False.
  Proof.
    intros Hxx.
    apply irreflexivity in Hxx; [| typeclasses eauto ].
    tauto.
  Qed.

End StrictOrders.

(* -------------------------------------------------------------------------- *)

(* This section studies how to obtain a strict order [<]
   out of a preorder [≤]. *)

Section StrictConstruction.

  (* Assume that [≤] is a preorder, that is, that the relation [≤]
     is reflexive and transitive. *)

  Context {A : Type}.
  Variable le : A → A → Prop.
  Context `{Ple : PreOrder A le}.

  Local Set Warnings "-notation-overridden".
  Notation "x '≤' y" := (le x y).

  (* Define its irreflexive kernel by [x < y  ↔  x ≤ y ∧ ¬ y ≤ x]. *)

  (* This definition exists in stdpp under the name [strict],
     so we re-use it. *)

  Goal ∀ x y, strict le x y ↔ x ≤ y ∧ ¬ y ≤ x.
  Proof. reflexivity. Qed.

  Notation "x '<' y" := (strict le x y).

  (* We obtain the following compatibility properties. *)

  Lemma strict_include x y :
    x < y → x ≤ y.
  Proof.
    (* This lemma also exists in stdpp.orders. *)
    unfold strict. tauto.
  Qed.

  Lemma strict_transitive_l x y z :
    x < y → y ≤ z → x < z.
  Proof.
    (* This lemma also exists in stdpp.orders. *)
    intros (Hxy & Hnyx) Hyz.
    split.
    + transitivity y; eauto.
    + intro Hzx.
      (* We have [x ≤ y ≤ z ≤ x]. By transitivity, we get [y ≤ x],
         which contradicts one of our hypotheses. *)
      assert (y ≤ x) by (transitivity z; eauto). tauto.
  Qed.

  Lemma strict_transitive_r x y z :
    x ≤ y → y < z → x < z.
  Proof.
    (* This lemma also exists in stdpp.orders. *)
    intros Hxy (Hyz & Hnzy).
    split.
    + transitivity y; eauto.
    + intro Hzx.
      (* We have [x ≤ y ≤ z ≤ x]. By transitivity, we get [z ≤ y],
         which contradicts one of our hypotheses. *)
      assert (z ≤ y) by (transitivity x; eauto). tauto.
  Qed.

  (* The irreflexive kernel [<] is a strict order: that is,
     it is irreflexive and transitive). *)

  Global Instance:
    StrictOrder (strict le).
  Proof.
    (* This lemma also exists in stdpp.orders. *)
    constructor.
    (* Irreflexivity. *)
    { intros x (? & ?). tauto. }
    (* Transitivity. *)
    { eauto using strict_include, strict_transitive_l. }
  Qed.

  (* Let us write [x ≡ y] when [x] are [y] are related in both directions
     by the preorder [≤]. (This is an equivalence relation.) *)

  Definition equivalent : A → A → Prop :=
    λ x y, (x ≤ y ∧ y ≤ x).

  Notation "x '≡' y" := (equivalent x y).

  Global Instance : Reflexive equivalent.
  Proof.
    intros x. split; apply reflexivity.
  Qed.

  Global Instance : Symmetric equivalent.
  Proof.
    intros x y. unfold equivalent. tauto.
  Qed.

  Global Instance : Transitive equivalent.
  Proof.
    intros x y z. do 2 intros (? & ?). split; transitivity y; eauto.
  Qed.

  Global Instance : Equivalence equivalent.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  Lemma equivalent_include x y :
    x ≡ y → x ≤ y.
  Proof.
    unfold equivalent. tauto.
  Qed.

  Lemma equivalent_include_reverse x y :
    x ≡ y → y ≤ x.
  Proof.
    unfold equivalent. tauto.
  Qed.

  (* The preorder [≤] is the union of the strict order [<] and of the
     equivalence relation [≡]. *)

  Lemma le_lteq {Hdec : RelDecision le} x y :
     x ≤ y  ↔  x < y ∨ x ≡ y.
  Proof.
    split.
    + intros Hxy.
      destruct (Hdec y x).
      - unfold equivalent. tauto.
      - unfold strict. tauto.
    + intros [|].
      - eauto using strict_include.
      - unfold equivalent in *. tauto.
  Qed.

  (* If the preorder [≤] is total then the strict order [<] enjoys a
     trichotomy principle: either [x] is less than [y], or [x] and [y]
     are equivalent, or [y] is less than [x]. *)

  (* We cannot use the class [Trichotomy] defined in stdpp.base because
     it requires Leibniz equality in the central case. *)

  Lemma lt_total {Hdec : RelDecision le} {Htotal : Total le} x y :
    x < y ∨ x ≡ y ∨ y < x.
  Proof.
    unfold strict, equivalent.
    destruct (Hdec x y); destruct (Hdec y x).
    + tauto.
    + tauto.
    + tauto.
    + exfalso. pose proof (Htotal x y). tauto.
  Qed.

End StrictConstruction.

(* -------------------------------------------------------------------------- *)

(* Conversely, this section studies how to obtain a preorder [≤]
   out of a strict order [<]. *)

(* It is not clear that this construction is useful,
   but I explore it out of curiosity. *)

Section LargeConstruction.

  Context {A : Type}.
  Variable lt : A → A → Prop.
  Context `{Slt : StrictOrder A lt}.
  Notation "x '<' y" := (lt x y).

  (* Let us view [x] and [y] as equivalent, and write [x ≡ y],
     if [x] and [y] are unrelated (in either direction) by the
     strict order [<]. *)

  (* Caveat: this relation is not necessarily transitive; see below. *)

  Definition equivalent' : A → A → Prop :=
    λ x y, ¬ x < y ∧ ¬ y < x.

  Notation "x '≡' y" := (equivalent' x y).

  (* Then, let us define the preorder [x ≤ y] as the union of the
     strict order [x < y] and the equivalence relation [x ≡ y]. *)

  Definition large : A → A → Prop :=
    λ x y, x < y ∨ x ≡ y.

  Local Set Warnings "-notation-overridden".
  Notation "x '≤' y" := (large x y).

  (* The composition of the constructions [large] and [strict] is the
     identity, and yields the strict order that we started with. *)

  Lemma strict_large x y :
    strict large x y ↔ x < y.
  Proof.
    unfold strict.
    unfold large.
    split.
    + intros ([|] & ?).
      - tauto.
      - exfalso. unfold equivalent' in *. tauto. (* symmetry of [≡] *)
    + intros. split.
      - tauto.
      - intros [|].
        { assert (x < x) by (transitivity y; eauto).
          eauto using strict_order_irreflexive. }
        { unfold equivalent' in *. tauto. }
  Qed.

  (* [equivalent'] is reflexive and symmetric. *)

  Global Instance : Reflexive equivalent'.
  Proof.
    intros x. split; eauto using strict_order_irreflexive.
  Qed.

  Global Instance : Symmetric equivalent'.
  Proof.
    intros x y. unfold equivalent'. tauto.
  Qed.

  (* [equivalent'] is in general NOT transitive. E.g., if we have three elements
     [a], [b], [c] with [a < b] and no other strict ordering relation [<]
     between them, then we get [a ≡ c] and [c ≡ b] but not [a ≡ b]. *)

  (* However, if we require the following compatibility properties between
     [≡] and [<], then we can prove that [≡] and [large] are transitive. *)

  Variable equivalent'_lt_compat : ∀ x y z,
    x ≡ y → y < z → x < z.

  Variable lt_equivalent'_compat : ∀ x y z,
    x < y → y ≡ z → x < z.

  Global Instance : Transitive equivalent'.
  Proof.
    intros x y z ? ?.
    split; intro;
    eauto 6 using strict_order_irreflexive, equivalent'_lt_compat, symmetry.
  Qed.

  Global Instance : Reflexive large.
  Proof.
    intros x. unfold large.
    right. apply reflexivity.
  Qed.

  Global Instance : Transitive large.
  Proof.
    intros x y z. unfold large.
    intros [|] [|].
    + left. transitivity y; eauto.
    + eauto using lt_equivalent'_compat.
    + eauto using equivalent'_lt_compat.
    + right. transitivity y; eauto.
  Qed.

  Global Instance : PreOrder large.
  Proof.
    econstructor; typeclasses eauto.
  Qed.

End LargeConstruction.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

Ltac destruct_equivalent :=
  lazymatch goal with h: equivalent _ _ _ |- _ =>
    unfold equivalent in h; destruct h
  end.
