From stdpp Require Import options.
From stdpp Require Import list_basics list_monad.

(* -------------------------------------------------------------------------- *)

(* TODO The following material should be moved into stdpp/list_basics.v. *)

Module list_basics_extra.

(** [init_segment i n f] is a list of length [n] whose elements are [f(i)],
    [f(i+1)], etc., up to [f(i+n-1)]. *)
Fixpoint init_segment {A} (i : nat) (n : nat) (f : nat → A) : list A :=
  match n with 0 => [] | S n => f i :: init_segment (i + 1) n f end.

(** [init n f] is a list of length [n] whose elements are [f(0)],
    [f(1)], etc., up to [f(n-1)]. *)
Definition init {A} (n : nat) (f : nat → A) : list A :=
  init_segment 0 n f.

(** ** Properties of [init_segment] and [init] *)

Section general_properties.
Context {A : Type}.
Implicit Types l : list A.

Lemma length_init_segment i n (f : nat → A) :
  length (init_segment i n f) = n.
Proof.
  revert i.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma length_init n (f : nat → A) : length (init n f) = n.
Proof. unfold init. apply length_init_segment. Qed.

Lemma lookup_init_segment_lt i n (f : nat → A) : forall (k : nat),
  k < n →
  (init_segment i n f) !! k = Some (f (i + k)).
Proof.
  revert i. induction n; simpl; intros.
  - exfalso. lia.
  - rewrite lookup_cons. destruct k as [| k].
    + rewrite Nat.add_0_r. eauto.
    + rewrite IHn by lia. do 2 f_equal. lia.
Qed.

Lemma lookup_init_segment_ge i n (f : nat → A) : forall (k : nat),
  n ≤ k →
  (init_segment i n f) !! k = None.
Proof.
  revert i. induction n; simpl; intros.
  - eauto.
  - rewrite lookup_cons. destruct k as [| k].
    + exfalso. lia.
    + rewrite IHn by lia. eauto.
Qed.

Lemma lookup_init_lt n (f : nat → A) : forall (k : nat),
  k < n →
  (init n f) !! k = Some (f k).
Proof.
  unfold init. intros. rewrite lookup_init_segment_lt by eauto. eauto.
Qed.

Lemma lookup_init_ge n (f : nat → A) : forall (k : nat),
  n ≤ k →
  (init n f) !! k = None.
Proof.
  unfold init. intros. rewrite lookup_init_segment_ge by eauto. eauto.
Qed.

(* Other lemmas *)

Lemma list_alter_out_of_bounds f l i : length l ≤ i → alter f i l = l.
Proof.
  unfold alter.
  revert i. induction l as [| x l]; simpl; [ eauto |]; intros.
  destruct i as [| i]; [ lia |].
  rewrite IHl by lia. eauto.
Qed.

Lemma list_delete_out_of_bounds l i : length l ≤ i → delete i l = l.
Proof.
  revert i.
  induction l as [| x l]; simpl; [ eauto |]; intros.
  destruct i as [| i]; [ lia |].
  unfold delete, list_delete.
  rewrite IHl by lia. eauto.
Qed.

End general_properties.

End list_basics_extra.
Import list_basics_extra.

(* -------------------------------------------------------------------------- *)

Local Open Scope Z_scope.

(* This library complements list_basics.v. Several operations that work
   with indices or lengths are redefined to work at type [Z] instead of
   type [nat]. *)

(* -------------------------------------------------------------------------- *)

(* Some lemmas and tactics about integers. *)

Local Ltac arith_refinement_hook :=
  idtac.

Local Ltac contradict :=
  exfalso; solve [ lia | congruence | eapply is_Some_None; eauto ].

Local Ltac case_decide' :=
  case_decide;
  arith_refinement_hook;
  try solve [ contradict ].

Local Ltac destruct_decide' P :=
  destruct_decide (decide P);
  arith_refinement_hook;
  try solve [ contradict ].

Lemma prove_to_nat_lt i n : 0 ≤ i → i < Z.of_nat n → (Z.to_nat i < n)%nat.
Proof. lia. Qed.
Local Hint Resolve prove_to_nat_lt : lia.

Lemma prove_lt_of_nat i n : 0 ≤ i → (Z.to_nat i < n)%nat → i < Z.of_nat n.
Proof. lia. Qed.
Local Hint Resolve prove_lt_of_nat : lia.

Lemma add_simpl_l' n1 n2 m : n1 = n2 → n1 + m - n2 = m.
Proof. lia. Qed.

(* [clip k i j] forces the index [k] into the semi-open interval [i, j). *)

Global Notation clip k i j :=
  ((k `max` i) `min` j).

(* -------------------------------------------------------------------------- *)

(* Operations on lists. *)

(* We define a function [singleton], which we (later) declare opaque. We
   recommend using [singleton x] instead of the notation [ [x] ], which is
   sugar for [x :: nil]. We recommend using list concatenation rather than
   [cons], so, for example, [xs ++ singleton y ++ zs] should be preferred to
   [xs ++ y :: zs]. This is more uniform. *)

(* We remark that in the case of lists, [insert] is really an update,
   not an insertion. We keep the name [insert] for compatibility with
   list_basics; but we name the simplification tactic [update]. *)

(* [take] and [drop] are special cases of [seg]. We advise the user
   to systematically prefer [seg] to [take] and [drop] so as to work
   with fewer functions and lemmas. *)

Definition singleton {A} (x : A) := [x].

Definition length {A} (xs : list A) : Z :=
  Z.of_nat (length xs).

Global Arguments length {_} _ : assert.
Global Instance: Params (@length) 1 := {}.

Global Instance listz_lookup {A} : Lookup Z A (list A) :=
  λ i xs, if decide (i < 0) then None else xs !! (Z.to_nat i).

Global Instance listz_lookup_total `{!Inhabited A} : LookupTotal Z A (list A) :=
  λ i xs, if decide (i < 0) then inhabitant else xs !!! (Z.to_nat i).

Global Instance listz_alter {A} : Alter Z A (list A) :=
  λ f i xs, if decide (i < 0) then xs else alter f (Z.to_nat i) xs.

Global Instance listz_insert {A} : Insert Z A (list A) :=
  λ i y xs, if decide (i < 0) then xs else insert (Z.to_nat i) y xs.

Global Instance listz_delete {A} : Delete Z (list A) :=
  λ i xs, if decide (i < 0) then xs else delete (Z.to_nat i) xs.

Definition init {A} (n : Z) (f : Z → A) : list A :=
  if decide (n < 0) then [] else init (Z.to_nat n) (λ i, f (Z.of_nat i)).

Definition replicate {A} (n : Z) (x : A) : list A :=
  init n (λ _i, x).

Definition take {A} (n : Z) (xs : list A) : list A :=
  if decide (n < 0) then [] else take (Z.to_nat n) xs.

Definition drop {A} (n : Z) (xs : list A) : list A :=
  if decide (n < 0) then xs else drop (Z.to_nat n) xs.

Global Arguments take {_} !_ !_ / : assert.
Global Instance: Params (@take) 1 := {}.

Global Arguments drop {_} !_ !_ / : assert.
Global Instance: Params (@drop) 1 := {}.

(* We define [seg i j] as the list segment whose start and end indices
   are [i] and [j]. As usual, this is a semi-open interval. *)

(* The use of [Z.max i 0] instead of [i] ensures that we obtain the
   correct segment even if [i] is negative. At the other end of the
   segment, if [j] exceeds [length xs], no precaution need be taken,
   as [take] already behaves correctly when [j] is too great.
   These precautions let us prove a nice lemma [seg_app]. *)

Definition seg {A} (i j : Z) (xs : list A) : list A :=
  take (j - (Z.max i 0)) (drop i xs).

(* Furthermore, we define [sub i n] as the list segment whose start index
   is [i] and whose length is [n]. It is sugar for [seg i (i + n)]. *)

Definition sub {A} (i n : Z) (xs : list A) : list A :=
  seg i (i + n) xs.

Lemma sub_seg {A} i n (xs : list A) :
  sub i n xs = seg i (i + n) xs.
Proof. reflexivity. Qed.

Lemma sub_take_drop {A} i n (xs : list A) :
  0 ≤ i →
  sub i n xs = take n (drop i xs).
Proof.
  intros. unfold sub, seg. f_equal. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* [valid_seg i j xs] means that [i] and [j] delimit a valid segment
   of the list [xs]. *)

Global Notation valid_seg i j xs :=
  (0 ≤ i ≤ j ≤ length xs).

(* [valid i xs] means that [i] is a valid index into the list [xs].
   In other words, this index can be used for reading or updating
   one element; it is the start index of a valid segment of length 1. *)

Global Notation valid i xs :=
  (0 ≤ i < length xs).

Lemma valid_valid_seg {A} (i : Z) (xs : list A) :
  valid i xs ↔ valid_seg i (i+1) xs.
Proof. lia. Qed.

Section Valid.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

Lemma lookup_lt_Some xs i x : xs !! i = Some x → valid i xs.
Proof.
  unfold length, lookup, listz_lookup. intros.
  case_decide'. apply lookup_lt_Some in H. lia.
Qed.

(* The following lemmas are analogous to [lookup_lt_is_Some]
   and its variants. *)

Lemma valid_is_Some_1 i xs : is_Some (xs !! i) → valid i xs.
Proof.
  unfold length, lookup, listz_lookup. intros.
  case_decide'. eauto using lookup_lt_is_Some_1 with lia.
Qed.

Lemma valid_is_Some_2 i xs : valid i xs → is_Some (xs !! i).
Proof.
  unfold length, lookup, listz_lookup. intros.
  case_decide'. eauto using lookup_lt_is_Some_2 with lia.
Qed.

Lemma valid_is_Some i xs : valid i xs ↔ is_Some (xs !! i).
Proof. split; eauto using valid_is_Some_1, valid_is_Some_2. Qed.

(* The following lemmas are analogous to [lookup_ge_None]
   and its variants. *)

Lemma lookup_None_invalid_1 xs i : xs !! i = None → ¬ valid i xs.
Proof.
  intros ? Hvalid. rewrite valid_is_Some in Hvalid.
  destruct Hvalid. congruence.
Qed.

Lemma lookup_None_invalid_2 xs i : ¬ valid i xs → xs !! i = None.
Proof.
  intros Hinvalid.
  destruct (xs !! i) eqn:?; intros; [ exfalso | eauto ].
  eauto using valid_is_Some_1.
Qed.

Lemma lookup_None_invalid xs i : xs !! i = None ↔ ¬ valid i xs.
Proof. split; eauto using lookup_None_invalid_1, lookup_None_invalid_2. Qed.

(* Updating at an invalid index. *)

Lemma insert_invalid xs i x :
  ¬ valid i xs → <[i:=x]>xs = xs.
Proof.
  unfold length, insert, listz_insert. case_decide'; intros; eauto.
  rewrite list_insert_ge by lia. eauto.
Qed.

Lemma alter_invalid xs i f :
  ¬ valid i xs → alter f i xs = xs.
Proof.
  unfold length, alter, listz_alter. case_decide'; intros; eauto.
  rewrite list_alter_out_of_bounds by lia. eauto.
Qed.

Lemma delete_invalid xs i :
  ¬ valid i xs → delete i xs = xs.
Proof.
  unfold length, delete, listz_delete. case_decide'; intros; eauto.
  rewrite list_delete_out_of_bounds by lia. eauto.
Qed.

End Valid.

(* At this point, [length] does nothing. *)

Global Ltac length :=
  autorewrite with length.

Global Tactic Notation "length" "in" hyp(h) :=
  autorewrite with length in h.

Global Tactic Notation "length" "in" "*" :=
  autorewrite with length in *.

(* At this point, [lookup] can prove that a lookup [xs !! i] yields [None]. *)

Global Hint Rewrite
  @lookup_None_invalid_2
  using (length; lia)
: lookup.

Global Ltac lookup :=
  autorewrite with lookup.

(* We can now improve [arith_refinement_hook]. *)

Local Ltac arith_refinement_hook ::=
  try subst; lookup.

(* -------------------------------------------------------------------------- *)

(* Properties of [length]. *)

Section Length.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

Lemma length_nonneg xs : 0 ≤ length xs.
Proof. unfold length. lia. Qed.

Lemma length_nil : length (@nil A) = 0.
Proof. reflexivity. Qed.

Lemma length_cons x xs : length (x :: xs) = length xs + 1.
Proof. unfold length. rewrite length_cons. lia. Qed.

Lemma length_singleton x : length (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma length_app xs ys : length (xs ++ ys) = length xs + length ys.
Proof. unfold length. rewrite length_app. lia. Qed.

Lemma length_alter f xs i : length (alter f i xs) = length xs.
Proof.
  unfold length, alter, listz_alter. case_decide'; eauto.
  by rewrite length_alter.
Qed.

Lemma length_insert xs i x : length (<[i:=x]>xs) = length xs.
Proof.
  unfold length, insert, listz_insert. case_decide'; eauto.
  by rewrite length_insert.
Qed.

Lemma length_delete xs i : valid i xs → length (delete i xs) = length xs - 1.
Proof.
  intros.
  assert (is_Some (xs !! i)) by eauto using valid_is_Some_2.
  unfold length, delete, listz_delete, lookup, listz_lookup in *.
  case_decide'.
  rewrite length_delete by eauto.
  lia.
Qed.

Lemma length_reverse xs : length (reverse xs) = length xs.
Proof. unfold length. by rewrite length_reverse. Qed.

Lemma length_init n (f : Z → A) : length (init n f) = Z.max n 0.
Proof.
  intros. unfold length, init. case_decide'.
  - simpl. lia.
  - rewrite length_init. lia.
Qed.

Lemma length_replicate n x :
  length (replicate n x) = Z.max n 0.
Proof. intros. unfold replicate. rewrite length_init. eauto. Qed.

Lemma length_take xs n :
  length (take n xs) = clip n 0 (length xs).
Proof.
  intros. unfold length, take. case_decide'.
  - simpl. lia.
  - rewrite length_take. lia.
Qed.

Lemma length_take_le xs n : 0 ≤ n ≤ length xs → length (take n xs) = n.
Proof. intros. rewrite length_take by lia. lia. Qed.

Lemma length_take_ge xs n : length xs ≤ n → length (take n xs) = length xs.
Proof.
  intros. generalize (length_nonneg xs); intro.
  rewrite length_take by lia. lia.
Qed.

Lemma length_drop xs n :
  length (drop n xs) = Z.max (length xs - (Z.max n 0)) 0.
Proof.
  unfold length, drop. generalize (length_nonneg xs); intro.
  case_decide'.
  - lia.
  - rewrite length_drop. lia.
Qed.

Lemma length_drop' xs n :
  0 ≤ n ≤ length xs → length (drop n xs) = length xs - n.
Proof.
  intros. rewrite length_drop. lia.
Qed.

Lemma length_seg i j xs :
  length (seg i j xs) = (j `min` (length xs) - i `max` 0) `max` 0.
Proof.
  intros. unfold seg. rewrite length_take, length_drop. lia.
Qed.

Lemma length_seg' i j xs :
  valid_seg i j xs →
  length (seg i j xs) = j - i.
Proof.
  intros. unfold seg. rewrite length_take, length_drop by lia. lia.
Qed.

Lemma length_fmap {A'} xs (g : A → A') :
  length (g <$> xs) = length xs.
Proof.
  unfold length. rewrite length_fmap. eauto.
Qed.

Lemma app_inj_1 xs1 ys1 xs2 ys2 :
  length xs1 = length ys1 →
  xs1 ++ xs2 = ys1 ++ ys2 →
  xs1 = ys1 ∧ xs2 = ys2.
Proof. intros Heq. apply Nat2Z.inj in Heq. auto using app_inj_1. Qed.

Lemma app_inj_2 xs1 ys1 xs2 ys2 :
  length xs2 = length ys2 →
  xs1 ++ xs2 = ys1 ++ ys2 →
  xs1 = ys1 ∧ xs2 = ys2.
Proof. intros Heq. apply Nat2Z.inj in Heq. auto using app_inj_2. Qed.

Lemma nil_or_length_pos xs : xs = [] ∨ length xs ≠ 0.
Proof. destruct xs as [| x xs]; simpl; auto. Qed.

Lemma nil_length_inv xs : length xs = 0 → xs = [].
Proof. by destruct xs. Qed.

Lemma list_eq_same_length xs ys n :
  length xs = n → length ys = n →
  (∀ i, 0 ≤ i < n → xs !! i = ys !! i) →
  xs = ys.
Proof.
  unfold length.
  intros ? ? Heq.
  apply list_eq_same_length with (n := Z.to_nat n).
  - lia.
  - lia.
  - intros i x y Hi Hxs Hys.
    cut (xs !! i = ys !! i). { congruence. } clear Hxs Hys.
    specialize Heq with (Z.of_nat i).
    unfold lookup, listz_lookup in Heq.
    rewrite Nat2Z.id in Heq.
    case_decide'.
    apply Heq. lia. (* phew *)
Qed.

End Length.

(* The tactic [listx i] proves that two lists are equal by checking that
   they are extensionally equal: same length and same elements.
   The parameter [i] is the name of the index that is looked up. *)

Global Ltac listx i :=
  eapply list_eq_same_length;
  length;
  [ eauto | eauto with lia | intros i ? ].

(* The tactic [length] simplifies applications of the form [length _]
   by using the following rewrite rules. *)

Global Hint Rewrite
  Z.sub_diag
  @length_nil
  @length_cons
  @length_app
  @length_singleton
  @length_alter
  @length_insert
  @length_reverse
  @length_init
  @length_replicate
  @length_take
  @length_drop
  @length_seg
  @length_fmap
: length.

Global Hint Rewrite
  Z.min_l Z.min_r Z.max_l Z.max_r
  using (length; lia)
: length.

(* [autorewrite] seems to miss some rewriting opportunities,
   so it is unable to prove these idempotence properties when
   they appear within a larger context. *)

Lemma max_idempotent_lr i j :
  (i `max` j) `max` j = i `max` j.
Proof.
  autorewrite with length. eauto.
Qed.

Lemma sum_of_maxes i j k :
  0 ≤ k →
  (i `max` k + j `max` k) `max` k = i `max` k + j `max` k.
Proof.
  intros. length. eauto.
Qed.

Global Hint Rewrite
  max_idempotent_lr
  sum_of_maxes
: length.

(* The tactic [lookup] includes the same rewrite rules as [length],
   plus more. *)

Global Hint Rewrite
  Z.sub_diag
  @length_nil
  @length_cons
  @length_app
  @length_singleton
  @length_alter
  @length_insert
  @length_reverse
  @length_init
  @length_replicate
  @length_take
  @length_drop
  @length_seg
  @length_fmap
: lookup.

Global Hint Rewrite
  Z.sub_0_r Z.sub_diag
  Z.min_l Z.min_r Z.max_l Z.max_r
  max_idempotent_lr
  sum_of_maxes
  using (length; lia)
: lookup.

(* The tactic [length_nonneg xs] asserts that the length of the list [xs]
   is nonnegative. This can help [lia]. *)

Ltac length_nonneg xs :=
  generalize (length_nonneg xs); intro.

(* -------------------------------------------------------------------------- *)

(* Properties of [lookup]. *)

Section Lookup.
Context {A : Type}.
Implicit Types i : Z.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* Interaction of [lookup] and [nil]. *)

Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.

(* Interaction of [lookup] and [app]. *)

Lemma lookup_app xs ys i :
  (xs ++ ys) !! i =
    match xs !! i with
    | Some x => Some x
    | None => ys !! (i - length xs)
    end.
Proof.
  length_nonneg xs.
  unfold lookup at 1. unfold listz_lookup at 1.
  case_decide'; [ eauto |].
  unfold lookup at 2. unfold listz_lookup.
  case_decide'.
  rewrite lookup_app.
  destruct (xs !! Z.to_nat i) eqn:Heq; [ eauto |].
  apply lookup_ge_None_1 in Heq.
  unfold lookup at 2. unfold length. case_decide'.
  f_equal. lia.
Qed.

Lemma lookup_app_l xs ys i : i < length xs → (xs ++ ys) !! i = xs !! i.
Proof.
  intros.
  rewrite lookup_app.
  destruct_decide' (i < 0); [ eauto |].
  destruct (xs !! i) eqn:Heq; [ eauto |].
  apply lookup_None_invalid_1 in Heq.
  lia.
Qed.

Lemma lookup_app_l_Some xs ys i x :
  xs !! i = Some x → (xs ++ ys) !! i = Some x.
Proof. rewrite lookup_app. by intros ->. Qed.

Lemma lookup_app_r xs ys i :
  i < 0 ∨ length xs ≤ i → (xs ++ ys) !! i = ys !! (i - length xs).
Proof.
  length_nonneg xs.
  intros [|].
  - lookup. eauto.
  - rewrite lookup_app. lookup. eauto.
Qed.

Lemma lookup_app' xs ys i :
  (xs ++ ys) !! i =
    if decide (0 <= i ∧ i < length xs) then xs !! i
    else ys !! (i - length xs).
Proof.
  length_nonneg xs.
  intros. case_decide.
  - rewrite lookup_app_l by lia. eauto.
  - rewrite lookup_app_r by lia. eauto.
Qed.

Lemma lookup_app_Some xs ys i x :
  (xs ++ ys) !! i = Some x ↔
    xs !! i = Some x ∨ length xs ≤ i ∧ ys !! (i - length xs) = Some x.
Proof.
  length_nonneg xs.
  rewrite lookup_app. destruct (xs !! i) eqn:Hi.
  - apply lookup_lt_Some in Hi. naive_solver lia.
  - apply lookup_None_invalid_1 in Hi.
    destruct_decide' (i < 0); naive_solver lia.
Qed.

Lemma lookup_valid_is_Some xs i :
  valid i xs →
  is_Some (xs !! i).
Proof.
  intros.
  unfold lookup, listz_lookup.
  case_decide'.
  apply lookup_lt_is_Some.
  unfold length in H.
  lia.
Qed.

(* Interaction of [lookup] and [singleton]. *)

Lemma list_lookup_singleton_eq_0 x :
  singleton x !! 0 = Some x.
Proof.
  unfold lookup, listz_lookup, singleton. case_decide'.
  by rewrite list_lookup_singleton.
Qed.

Lemma list_lookup_singleton_ne_0 x i :
  i ≠ 0 → singleton x !! i = None.
Proof.
  intros. lookup. eauto.
Qed.

Lemma list_lookup_singleton x i :
  singleton x !! i =
    if decide (i = 0) then Some x else None.
Proof.
  case_decide';
  eauto using list_lookup_singleton_eq_0, list_lookup_singleton_ne_0.
Qed.

(* Interaction of [lookup] and [cons]. *)

Lemma cons_is_append x xs :
  x :: xs = singleton x ++ xs.
Proof. eauto. Qed.

Lemma lookup_cons_eq_0 x xs :
  (x :: xs) !! 0 = Some x.
Proof.
  rewrite cons_is_append.
  rewrite lookup_app_l by (length; lia).
  apply list_lookup_singleton_eq_0.
Qed.

Lemma lookup_cons_ne_0 xs x i :
  i ≠ 0 → (x :: xs) !! i = xs !! (i - 1).
Proof.
  intros. rewrite cons_is_append.
  rewrite lookup_app_r; length; eauto with lia.
Qed.

Lemma lookup_cons x xs i :
  (x :: xs) !! i =
    if decide (i = 0) then Some x else xs !! (i - 1).
Proof.
  case_decide'; eauto using lookup_cons_eq_0, lookup_cons_ne_0.
Qed.

(* Interaction of [lookup] and [init]. *)

Lemma lookup_init_lt n (f : Z → A) k :
  0 ≤ k < n →
  (init n f) !! k = Some (f k).
Proof.
  unfold init, lookup, listz_lookup. intros. repeat case_decide'.
  rewrite lookup_init_lt by lia.
  do 2 f_equal. lia.
Qed.

Lemma lookup_init_ge n (f : Z → A) k :
  k < 0 ∨ n ≤ k →
  (init n f) !! k = None.
Proof.
  unfold init, lookup, listz_lookup. intros. repeat case_decide'; eauto.
  rewrite lookup_init_ge by lia. eauto.
Qed.

(* Interaction of [lookup] and [replicate]. *)

Lemma lookup_replicate_lt n x k :
  0 ≤ k < n →
  (replicate n x) !! k = Some x.
Proof.
  unfold replicate. intros. by rewrite lookup_init_lt by eauto.
Qed.

Lemma lookup_replicate_ge n x k :
  k < 0 ∨ n ≤ k →
  (replicate n x) !! k = None.
Proof.
  unfold replicate. intros. by rewrite lookup_init_ge by eauto.
Qed.

(* Interaction of [lookup] and [alter]. *)

Lemma list_lookup_alter_eq f xs i :
  alter f i xs !! i = f <$> xs !! i.
Proof.
  intros. unfold alter, listz_alter, lookup, listz_lookup.
  case_decide'; [ eauto |].
  apply list_lookup_alter_eq.
Qed.

Lemma list_lookup_alter_eq' f xs i j :
  i = j →
  alter f i xs !! j = f <$> xs !! i.
Proof.
  intro. subst. apply list_lookup_alter_eq.
Qed.

Lemma list_lookup_alter_ne f xs i j : i ≠ j → alter f i xs !! j = xs !! j.
Proof.
  intros. unfold alter, listz_alter, lookup, listz_lookup.
  do 2 (case_decide'; [ eauto |]).
  apply list_lookup_alter_ne. lia.
Qed.

Lemma list_lookup_alter f xs i j :
  alter f i xs !! j = if decide (i = j) then f <$> xs !! i else xs !! j.
Proof.
  case_decide'; auto using list_lookup_alter_eq, list_lookup_alter_ne.
Qed.

(* Interaction of [lookup] and [insert]. *)

Lemma list_lookup_insert_eq xs i x :
  valid i xs → <[i:=x]>xs !! i = Some x.
Proof.
  unfold length.
  intros. unfold insert, listz_insert, lookup, listz_lookup. case_decide'.
  rewrite list_lookup_insert_eq by lia.
  eauto.
Qed.

Lemma list_lookup_insert_eq' xs i j x :
  valid i xs → i = j → <[i:=x]>xs !! j = Some x.
Proof.
  intros. subst. eauto using list_lookup_insert_eq.
Qed.

Lemma list_lookup_insert_ne xs i j x :
  i ≠ j → <[i:=x]>xs !! j = xs !! j.
Proof.
  intros. unfold insert, listz_insert, lookup, listz_lookup.
  repeat case_decide'; eauto.
  rewrite list_lookup_insert_ne by lia.
  eauto.
Qed.

Lemma list_lookup_insert xs i j x :
  <[i:=x]>xs !! j =
    if decide (i = j ∧ valid i xs) then Some x else xs !! j.
Proof.
  case_decide'.
  - eauto using list_lookup_insert_eq' with lia.
  - assert (i ≠ j ∨ ¬ valid i xs) as [|] by lia.
    + rewrite list_lookup_insert_ne by lia. eauto.
    + rewrite insert_invalid by lia. eauto.
Qed.

(* Interaction of [lookup] and [delete]. *)

Lemma list_lookup_delete_lt xs i j :
  j < i → delete i xs !! j = xs !! j.
Proof.
  intros. unfold delete, listz_delete, lookup, listz_lookup.
  repeat case_decide'; eauto.
  rewrite list_lookup_delete_lt by lia.
  eauto.
Qed.

Lemma list_lookup_delete_ge xs i j :
  0 ≤ i ≤ j → delete i xs !! j = xs !! (j + 1).
Proof.
  intros. unfold delete, listz_delete, lookup, listz_lookup.
  repeat case_decide'; eauto.
  rewrite list_lookup_delete_ge by lia.
  f_equal. lia.
Qed.

Lemma list_lookup_delete xs i j :
  delete i xs !! j =
    if decide (i < 0 ∨ j < i) then xs !! j
    else xs !! (j + 1).
Proof.
  case_decide'.
  - destruct H.
    + rewrite delete_invalid by lia. eauto.
    + eauto using list_lookup_delete_lt.
  - eauto using list_lookup_delete_ge with lia.
Qed.

(* Interaction of [lookup] and [take]. *)

Lemma lookup_take_lt xs n i : i < n → take n xs !! i = xs !! i.
Proof.
  intros. unfold take, lookup, listz_lookup. repeat case_decide'; eauto.
  rewrite lookup_take_lt by lia. eauto.
Qed.

Lemma lookup_take_ge xs n i : n ≤ i → take n xs !! i = None.
Proof.
  intros. unfold take, lookup, listz_lookup. repeat case_decide'; eauto.
  rewrite lookup_take_ge by lia. eauto.
Qed.

Lemma lookup_take xs i n :
  take n xs !! i = if decide (i < n) then xs !! i else None.
Proof.
  case_decide'; auto using lookup_take_lt, lookup_take_ge with lia.
Qed.

(* Interaction of [lookup] and [drop]. *)

(* The condition [0 ≤ n] is not required. *)

Lemma lookup_drop xs n i : 0 ≤ i → drop n xs !! i = xs !! (n `max` 0 + i).
Proof.
  intros. unfold drop, lookup, listz_lookup. repeat case_decide'; eauto.
  rewrite lookup_drop. f_equal. lia.
Qed.

(* Interaction of [lookup] and [seg]. *)

(* The condition [valid_seg i j xs] is not required. *)

Lemma lookup_seg i j xs k :
  valid k (seg i j xs) →
  seg i j xs !! k = xs !! (i `max` 0 + k).
Proof.
  length. intros. unfold seg.
  rewrite lookup_take_lt, lookup_drop by lia.
  eauto.
Qed.

(* Interaction of [lookup] and [fmap] *)

Lemma list_lookup_fmap {B} (f : A → B) (xs : list A) (i : Z) :
  (f <$> xs) !! i = f <$> (xs !! i).
Proof.
  unfold lookup, listz_lookup. case_decide'; eauto.
  rewrite list_lookup_fmap. eauto.
Qed.

End Lookup.

Global Opaque singleton.
  (* [singleton x] is not rewritten to [x :: nil], *)
  (* so [cons_is_append] does not affect [singleton]. *)

(* The tactic [lookup] simplifies a lookup [xs !! i] when this does not
   introduce a conditional expression. *)

Global Hint Rewrite
  @cons_is_append
  @lookup_nil
  @list_lookup_singleton_eq_0
  @list_lookup_alter_eq
  @list_lookup_insert_eq
  @list_lookup_fmap
: lookup.

Global Hint Rewrite
  @lookup_None_invalid_2
  @lookup_app_l
  @lookup_app_r
  @lookup_init_lt
  @lookup_init_ge
  @lookup_replicate_lt
  @lookup_replicate_ge
  @list_lookup_alter_eq'
  @list_lookup_alter_ne
  @list_lookup_insert_eq'
  @list_lookup_insert_ne
  @list_lookup_delete_lt
  @list_lookup_delete_ge
  @lookup_take_lt
  @lookup_take_ge
  @lookup_drop
  @lookup_seg
  using (length; lia)
: lookup.

(* -------------------------------------------------------------------------- *)

(* Properties of [lookup_total]. *)

Section LookupTotal.
Context `{Inhabited A}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* A generic reformulation of [lookup_total] in terms of [lookup]. *)

Lemma list_lookup_total_alt xs i :
  xs !!! i = default inhabitant (xs !! i).
Proof.
  unfold lookup_total, listz_lookup_total.
  case_decide'; [ eauto |].
  rewrite list_lookup_total_alt.
  unfold lookup at 2, listz_lookup. case_decide'. eauto.
Qed.

(* More lemmas about the connection between [lookup_total] and [lookup]. *)

Lemma list_lookup_total_correct xs i x :
  xs !! i = Some x → xs !!! i = x.
Proof.
  rewrite list_lookup_total_alt. intros ->. eauto.
Qed.

Lemma list_lookup_lookup_total xs i :
  is_Some (xs !! i) → xs !! i = Some (xs !!! i).
Proof.
  destruct 1. by erewrite list_lookup_total_correct by eauto.
Qed.

Lemma list_lookup_lookup_total_valid xs i :
  valid i xs → xs !! i = Some (xs !!! i).
Proof.
  rewrite valid_is_Some. eauto using list_lookup_lookup_total.
Qed.

Lemma list_lookup_alt xs i x :
  xs !! i = Some x ↔ valid i xs ∧ xs !!! i = x.
Proof.
  split.
  - intros; split.
    + rewrite valid_is_Some. eauto.
    + eauto using list_lookup_total_correct.
  - intros [ ? ? ]. subst.
    eauto using list_lookup_lookup_total_valid.
Qed.

Lemma lookup_total_None_invalid_2 xs i :
  ¬ valid i xs → xs !!! i = inhabitant.
Proof.
  intros Hinvalid. rewrite list_lookup_total_alt. lookup. eauto.
Qed.

Local Ltac easy :=
  length; intros; rewrite !list_lookup_total_alt; lookup; eauto.

(* Interaction of [lookup_total] and [nil]. *)

Lemma lookup_total_nil i : @nil A !!! i = inhabitant.
Proof. easy. Qed.

(* Interaction of [lookup_total] and [app]. *)

Lemma lookup_total_app_l xs ys i :
  i < length xs → (xs ++ ys) !!! i = xs !!! i.
Proof. easy. Qed.

Lemma lookup_total_app_r xs ys i :
  i < 0 ∨ length xs ≤ i → (xs ++ ys) !!! i = ys !!! (i - length xs).
Proof. easy. Qed.

(* Interaction of [lookup] and [singleton]. *)

Lemma lookup_total_singleton_eq_0 x :
  singleton x !!! 0 = x.
Proof. easy. Qed.

(* Interaction of [lookup_total] and [cons]. *)

Lemma lookup_total_cons_eq_0 xs x :
  (x :: xs) !!! 0 = x.
Proof. easy. Qed.

Lemma lookup_total_cons_ne_0 xs x i :
  i ≠ 0 → (x :: xs) !!! i = xs !!! (i - 1).
Proof. easy. Qed.

Lemma lookup_total_cons x xs i :
  (x :: xs) !!! i =
    if decide (i = 0) then x else xs !!! (i - 1).
Proof. case_decide'; easy. Qed.

(* Interaction of [lookup_total] and [init]. *)

Lemma lookup_total_init_lt n (f : Z → A) k :
  0 ≤ k < n →
  (init n f) !!! k = f k.
Proof. easy. Qed.

(* Interaction of [lookup_total] and [replicate]. *)

Lemma lookup_total_replicate_lt n x k :
  0 ≤ k < n →
  (replicate n x) !!! k = x.
Proof. easy. Qed.

(* Interaction of [lookup_total] and [alter]. *)

Lemma lookup_total_alter_eq f xs i :
  valid i xs →
  alter f i xs !!! i = f (xs !!! i).
Proof.
  easy.
  (* We must argue that [xs !! i] is [Some _]. *)
  rewrite !list_lookup_lookup_total_valid by eauto. eauto.
Qed.

Lemma lookup_total_alter_eq' f xs i j :
  i = j →
  valid i xs →
  alter f i xs !!! j = f (xs !!! i).
Proof.
  intro. subst. apply lookup_total_alter_eq.
Qed.

Lemma lookup_total_alter_ne f xs i j :
  i ≠ j →
  alter f i xs !!! j = xs !!! j.
Proof. easy. Qed.

Lemma lookup_total_alter f xs i j :
  alter f i xs !!! j =
    if decide (i = j ∧ valid i xs) then f (xs !!! i) else xs !!! j.
Proof.
  case_decide'.
  - match goal with h: _ ∧ _ |- _ => destruct h end. subst.
    eauto using lookup_total_alter_eq.
  - assert (i ≠ j ∨ ¬ valid i xs) as [|] by lia.
    + eauto using lookup_total_alter_ne.
    + rewrite alter_invalid by eauto. eauto.
Qed.

(* Interaction of [lookup_total] and [insert]. *)

Lemma lookup_total_insert_eq x xs i :
  valid i xs →
  <[i:=x]>xs !!! i = x.
Proof. easy. Qed.

Lemma lookup_total_insert_eq' x xs i j :
  i = j →
  valid i xs →
  <[i:=x]>xs !!! j = x.
Proof. easy. Qed.

Lemma lookup_total_insert_ne x xs i j :
  i ≠ j →
  <[i:=x]>xs !!! j = xs !!! j.
Proof. easy. Qed.

Lemma lookup_total_insert x xs i j :
  <[i:=x]>xs !!! j =
    if decide (i = j ∧ valid i xs) then x else xs !!! j.
Proof.
  case_decide'.
  - match goal with h: _ ∧ _ |- _ => destruct h end. subst.
    eauto using lookup_total_insert_eq.
  - assert (i ≠ j ∨ ¬ valid i xs) as [|] by lia.
    + eauto using lookup_total_insert_ne.
    + rewrite insert_invalid by eauto. eauto.
Qed.

(* Interaction of [lookup_total] and [delete]. *)

Lemma lookup_total_delete_lt xs i j :
  j < i → delete i xs !!! j = xs !!! j.
Proof. easy. Qed.

Lemma lookup_total_delete_ge xs i j :
  0 ≤ i ≤ j → delete i xs !!! j = xs !!! (j + 1).
Proof. easy. Qed.

Lemma lookup_total_delete xs i j :
  delete i xs !!! j =
    if decide (¬ valid i xs ∨ j < i) then xs !!! j
    else xs !!! (j + 1).
Proof.
  case_decide'.
  - match goal with h: _ ∨ _ |- _ => destruct h end.
    + rewrite delete_invalid by eauto. eauto.
    + eauto using lookup_total_delete_lt.
  - eauto using lookup_total_delete_ge with lia.
Qed.

(* Interaction of [lookup_total] and [take]. *)

Lemma lookup_total_take_lt xs n i : i < n → take n xs !!! i = xs !!! i.
Proof. easy. Qed.

Lemma lookup_total_take_ge xs n i : n ≤ i → take n xs !!! i = inhabitant.
Proof. easy. Qed.

Lemma lookup_total_take xs i n :
  take n xs !!! i = if decide (i < n) then xs !!! i else inhabitant.
Proof.
  case_decide'; auto using lookup_total_take_lt, lookup_total_take_ge with lia.
Qed.

(* Interaction of [lookup_total] and [drop]. *)

Lemma lookup_total_drop xs n i : 0 ≤ n → 0 ≤ i → drop n xs !!! i = xs !!! (n + i).
Proof. easy. Qed.

(* Interaction of [lookup_total] and [seg]. *)

(* The condition [valid_seg i j xs] is not required. *)

Lemma lookup_total_seg i j xs k :
  valid k (seg i j xs) →
  seg i j xs !!! k = xs !!! (i `max` 0 + k).
Proof. easy. Qed.

End LookupTotal.

(* The tactic [lookup] is extended to simplify a total lookup [xs !!! i]
   when this does not introduce a conditional expression. *)

Global Hint Rewrite
  @lookup_total_nil
  @cons_is_append
  @lookup_total_singleton_eq_0
: lookup.

Global Hint Rewrite
  @lookup_total_None_invalid_2
  @lookup_total_app_l
  @lookup_total_app_r
  @lookup_total_init_lt
  @lookup_total_replicate_lt
  @lookup_total_alter_eq'
  @lookup_total_alter_ne
  @lookup_total_insert_eq'
  @lookup_total_insert_ne
  @lookup_total_delete_lt
  @lookup_total_delete_ge
  @lookup_total_take_lt
  @lookup_total_drop
  @lookup_total_seg
  using (length; lia)
: lookup.

(* -------------------------------------------------------------------------- *)

(* Properties of [take]. *)

Section Take.
Context {A : Type}.
Implicit Types x : A.
Implicit Types xs ys zs : list A.

Lemma take_0 xs : take 0 xs = [].
Proof. reflexivity. Qed.

Lemma take_le_0 xs n : n ≤ 0 → take n xs = [].
Proof.
  intros. unfold take. case_decide'; eauto.
  assert (n = 0) by lia. subst. reflexivity.
Qed.

Lemma take_ge xs n : length xs ≤ n → take n xs = xs.
Proof.
  unfold length. intros. length_nonneg xs. unfold take.
  case_decide'; eauto. rewrite take_ge by lia. eauto.
Qed.

(* Interaction of [take] and [nil]. *)

Lemma take_nil n : take n (@nil A) = [].
Proof. unfold take. case_decide'; eauto. rewrite take_nil. eauto. Qed.

(* Interaction of [take] and [app]. *)

Lemma take_app xs ys n :
  take n (xs ++ ys) = take n xs ++ take (n - length xs) ys.
Proof.
  unfold length, take. repeat case_decide'; eauto.
  - rewrite take_app.
    replace (Z.to_nat n - Datatypes.length xs)%nat with 0%nat by lia.
    rewrite list.take_0. eauto.
  - rewrite take_app. do 2 f_equal. lia.
Qed.

(* Interaction of [take] and [insert]. *)

Lemma take_insert_ge xs n i x :
  0 ≤ n ≤ i →
  take n (<[i:=x]>xs) = take n xs.
Proof. intros. listx j. lookup. eauto. Qed.

Lemma take_insert_lt xs n i x :
  0 ≤ i < n →
  take n (<[i:=x]>xs) = <[i:=x]>(take n xs).
Proof.
  intros. listx j. lookup. destruct_decide' (i = j); eauto.
Qed.

(* Interaction of [take] and [init]. *)

Lemma take_init n m (f : Z → A) :
  0 ≤ n → 0 ≤ m →
  take n (init m f) = init (Z.min n m) f.
Proof.
  intros. listx j. lookup. eauto.
Qed.

(* Interaction of [take] and [replicate]. *)

Lemma take_replicate n m x :
  0 ≤ n → 0 ≤ m →
  take n (replicate m x) = replicate (Z.min n m) x.
Proof.
  intros. listx j. lookup. eauto.
Qed.

End Take.

(* The tactic [take] simplifies an application of [take]. *)

Global Hint Rewrite
  Z.add_simpl_l
  @cons_is_append
  @app_nil_l
  @app_nil_r
  @take_0
  @take_nil
  @take_app
: take.

Global Hint Rewrite
  add_simpl_l'
  @take_le_0
  @take_ge
  @take_insert_ge
  @take_insert_lt
  @take_init
  @take_replicate
  Z.min_l Z.min_r Z.max_l Z.max_r
  using (length; lia)
: take.

Ltac take :=
  autorewrite with take.

Section TakeExtra.
Context {A : Type}.
Implicit Types xs ys zs : list A.

Lemma take_app_add xs ys m :
  0 ≤ m →
  take (length xs + m) (xs ++ ys) = xs ++ take m ys.
Proof. intros. take. eauto. Qed.

Lemma take_app_add' xs ys n m :
  0 ≤ m →
  n = length xs →
  take (n + m) (xs ++ ys) = xs ++ take m ys.
Proof. intros. take. eauto. Qed.

Lemma take_app_length xs ys :
  take (length xs) (xs ++ ys) = xs.
Proof. intros. take. eauto. Qed.

Lemma take_app3_length xs1 xs2 xs3 :
  take (length xs1) ((xs1 ++ xs2) ++ xs3) = xs1.
Proof. length_nonneg xs2. take. eauto. Qed.

Lemma take_app3_length_r xs1 xs2 xs3 :
  take (length xs1) (xs1 ++ xs2 ++ xs3) = xs1.
Proof. length_nonneg xs2. take. eauto. Qed.

Lemma take_take xs n m : take n (take m xs) = take (Z.min n m) xs.
Proof.
  unfold take. repeat case_decide'; eauto using list.take_nil.
  rewrite take_take. f_equal. lia.
Qed.

End TakeExtra.

Global Hint Rewrite
  @take_app_add
  @take_app3_length
  @take_app3_length_r
  @take_take
: take.

Global Hint Rewrite
  @take_app_add'
  using (length; lia)
: take.

(* -------------------------------------------------------------------------- *)

(* Properties of [drop]. *)

Section Drop.
Context {A : Type}.
Implicit Types x : A.
Implicit Types xs ys zs : list A.

Lemma drop_ge xs n : length xs ≤ n → drop n xs = [].
Proof.
  unfold length. intros. length_nonneg xs. unfold drop. case_decide'.
  rewrite drop_ge by lia. eauto.
Qed.

Lemma drop_none xs : drop 0 xs = xs.
Proof. reflexivity. Qed.

Lemma drop_none' n xs : n ≤ 0 → drop n xs = xs.
Proof.
  intros. unfold drop. case_decide'; eauto.
  assert (n = 0) by lia. subst. apply drop_none.
Qed.

Lemma drop_max n xs : drop (n `max` 0) xs = drop n xs.
Proof.
  assert (n ≤ 0 ∨ 0 ≤ n) as [|] by lia.
  - do 2 rewrite drop_none' by lia. eauto.
  - f_equal. lia.
Qed.

Lemma drop_clip n xs : drop (clip n 0 (length xs)) xs = drop n xs.
Proof.
  assert (n ≤ 0 ∨ 0 ≤ n) as [|] by lia.
  - do 2 rewrite drop_none' by lia. eauto.
  - assert (n ≤ length xs ∨ length xs ≤ n) as [|] by lia.
    + f_equal. lia.
    + do 2 rewrite drop_ge by lia. eauto.
Qed.

Lemma drop_all xs : drop (length xs) xs = [].
Proof. by apply drop_ge. Qed.

(* Interaction of [drop] and [app]. *)

Lemma drop_app xs ys n :
  drop n (xs ++ ys) = drop n xs ++ drop (n - length xs) ys.
Proof.
  length_nonneg xs. unfold length in *.
  unfold drop. repeat case_decide'; eauto.
  - rewrite drop_app.
    replace (Z.to_nat n - Datatypes.length xs)%nat with 0%nat by lia.
    rewrite drop_0. eauto.
  - rewrite drop_app. do 2 f_equal. lia.
Qed.

(* Interaction of [drop] and [insert]. *)

Lemma drop_insert_ge xs n i x :
  0 ≤ n ≤ i →
  n ≤ length xs →
  drop n (<[i:=x]>xs) = <[i-n := x]> (drop n xs).
Proof.
  intros. listx j. lookup.
  rewrite !list_lookup_insert. repeat case_decide'; lookup; eauto.
Qed.

Lemma drop_insert_lt xs n i x :
  0 ≤ i < n → n ≤ length xs →
  drop n (<[i:=x]>xs) = drop n xs.
Proof.
  intros. listx j. lookup. eauto.
Qed.

(* Interaction of [drop] and [init]. *)

Lemma drop_init n m (f : Z → A) :
  0 ≤ n ≤ m →
  drop n (init m f) = init (m - n) (λ i, f (n + i)).
Proof.
  intros. listx j. lookup. eauto.
Qed.

(* Interaction of [drop] and [replicate]. *)

Lemma drop_replicate n m x :
  0 ≤ n ≤ m →
  drop n (replicate m x) = replicate (m - n) x.
Proof.
  intros. listx j. lookup. eauto.
Qed.

End Drop.

Global Hint Rewrite
  @drop_all
: drop.

Global Hint Rewrite
  @drop_none'
  @drop_ge
  @drop_app
  @drop_insert_ge
  @drop_insert_lt
  @drop_init
  @drop_replicate
  using (length; lia)
: drop.

Ltac drop :=
  autorewrite with drop.

(* -------------------------------------------------------------------------- *)

(* Properties of [take] and [drop]. *)

Section TakeDrop.
Context {A : Type}.
Implicit Types x : A.
Implicit Types xs ys zs : list A.

Lemma take_drop n xs : take n xs ++ drop n xs = xs.
Proof.
  unfold take, drop. repeat case_decide'; eauto. apply take_drop.
Qed.

Lemma take_drop_commute xs n m :
  0 ≤ n → 0 ≤ m →
  take n (drop m xs) = drop m (take (m + n) xs).
Proof.
  intros. unfold take, drop. repeat case_decide'; eauto.
  rewrite take_drop_commute. do 2 f_equal. lia.
Qed.

End TakeDrop.

(* -------------------------------------------------------------------------- *)

(* Properties of [seg]. *)

Section Seg.
Context {A : Type}.
Implicit Types x : A.
Implicit Types xs ys zs : list A.

(* [take] and [drop] are special cases of [seg]. *)

Lemma take_seg n xs : take n xs = seg 0 n xs.
Proof. unfold seg. drop. rewrite Z.sub_0_r. eauto. Qed.

Lemma drop_seg n xs : drop n xs = seg n (length xs) xs.
Proof. unfold seg. listx j. lookup. eauto. Qed.

Lemma seg_none i j xs : j ≤ i → seg i j xs = [].
Proof. intros. unfold seg. take. eauto. Qed.

Lemma seg_all i j xs : i ≤ 0 → length xs ≤ j → seg i j xs = xs.
Proof. intros. unfold seg. drop. take. eauto. Qed.

Lemma seg_intro xs : xs = seg 0 (length xs) xs.
Proof. rewrite seg_all by lia. eauto. Qed.

(* Any segment is equal to a valid segment. *)

Lemma seg_valid i j xs :
  seg i j xs =
    let i := clip i 0 (length xs) in
    let j := clip j i (length xs) in
    seg i j xs.
Proof.
  unfold seg. listx k. lookup. eauto.
Qed.

Goal forall i j xs,
  let i := clip i 0 (length xs) in
  let j := clip j i (length xs) in
  valid_seg i j xs.
Proof.
  intros. length_nonneg xs. lia.
Qed.

(* A segment can be split anywhere. *)

Lemma split_seg j xs i k :
  valid_seg i j xs →
  valid_seg j k xs →
  seg i k xs = seg i j xs ++ seg j k xs.
Proof.
  intros. length_nonneg xs. listx o. lookup.
  rewrite lookup_app'. length. case_decide'; lookup; eauto.
  f_equal. lia.
Qed.

(* A singleton segment is a singleton. *)

Lemma seg_is_singleton `{Inhabited A} i j xs :
  valid i xs →
  i + 1 = j →
  seg i j xs = singleton (xs !!! i).
Proof.
  intros. subst. listx k. assert (k = 0) by lia. subst. lookup.
  rewrite Z.add_0_r.
  eauto using list_lookup_lookup_total_valid with lia.
Qed.

(* Interaction of [seg] and [app]. *)

Lemma seg_app i j xs ys :
  seg i j (xs ++ ys) =
    let n := length xs in
    seg i j xs ++ seg (i - n) (j - n) ys.
Proof.
  length_nonneg xs.
  intros. unfold seg. drop. take. f_equal.
  listx k. lookup. eauto. (* yes! *)
  (* This is just as good as an SMT solver...! *)
Qed.

(* Interaction of [seg] and [insert]. *)

Lemma seg_insert_outside xs i j k x :
  valid_seg i j xs →
  ¬ (i ≤ k < j) →
  seg i j (<[k:=x]>xs) = seg i j xs.
Proof.
  intros. listx o. lookup. eauto.
Qed.

Lemma seg_insert_inside xs i j k x :
  valid_seg i j xs →
  seg i j (<[k:=x]>xs) = <[k-i:=x]>(seg i j xs).
Proof.
  intros. listx o. lookup.
  rewrite list_lookup_insert. case_decide'; lookup; eauto.
Qed.

Lemma seg_insert xs i j k x :
  valid_seg i j xs →
  seg i j (<[k:=x]>xs) =
    if decide (i ≤ k < j) then <[k-i:=x]>(seg i j xs)
    else seg i j xs.
Proof.
  intros. case_decide'; eauto using seg_insert_inside, seg_insert_outside.
Qed.

(* Interaction of [seg] and [init]. *)

Lemma seg_init n i j (f : Z → A) :
  0 ≤ i ≤ j ≤ n →
  seg i j (init n f) = init (j - i) (λ k, f (i + k)).
Proof.
  intros. listx k. lookup. eauto.
Qed.

(* Interaction of [seg] and [replicate]. *)

Lemma seg_replicate n i j x :
  0 ≤ i ≤ j ≤ n →
  seg i j (replicate n x) = replicate (j - i) x.
Proof.
  intros. listx k. lookup. eauto.
Qed.

(* Interaction of [seg] with itself. *)

(* [seg_seg'] is simpler but weaker. *)

Lemma seg_seg' i j k l xs :
  valid_seg k l xs →
  valid_seg i j (seg k l xs) →
  seg i j (seg k l xs) =
  seg (k + i) (k + j) xs.
Proof.
  length. intros. listx o. lookup. f_equal. lia.
Qed.

Lemma seg_seg i j k l xs :
  seg i j (seg k l xs) =
  (* The right-hand side could be written like this:
       let k := k `max` 0 in
       let n := length (seg k l xs) in
       seg (k + (clip i 0 n)) (k + (clip j 0 n)) xs
     But we prefer to avoid introducing [let]s: *)
  seg
    (k `max` 0 + (clip i 0 ((l `min` (length xs) - k `max` 0) `max` 0)))
    (k `max` 0 + (clip j 0 ((l `min` (length xs) - k `max` 0) `max` 0)))
    xs.
Proof.
  listx o. lookup. rewrite Z.add_assoc. eauto. (* not too shabby! *)
Qed.

End Seg.

Global Hint Rewrite
  Z.sub_0_r Z.sub_diag
  @seg_none
  @seg_all
  @seg_app
  @seg_insert_outside
  @seg_insert_inside
  @seg_init
  @seg_replicate
  @seg_seg
  using (length; lia)
: seg.

Ltac seg :=
  autorewrite with seg.

(* The tactic [lookup_app_split] performs a case split in a situation where
   the goal contains a lookup in a concatenation [(xs ++ ys) !! i]. *)

Global Ltac lookup_app_split :=
  rewrite lookup_app'; length; case_decide'; lookup; eauto.

(* The tactic [split_seg j xs] splits a list [xs] or a list segment
   [seg i k xs] at index [j]. *)

Global Ltac split_seg j xs :=
  first [
    (* case: [xs] is already a segment *)
    rewrite (split_seg j xs) by (length; lia)
  | (* case: introduce a list segment first *)
    rewrite (seg_intro xs); length;
    rewrite (split_seg j xs) by (length; lia)
  ];
  seg.

(* -------------------------------------------------------------------------- *)

(* Properties of [init] and [replicate]. *)

Section Replicate.
Context {A : Type}.
Implicit Types x : A.
Implicit Types f : Z → A.
Implicit Types xs ys zs : list A.

(* [init] applied to length 0 or 1. *)

Lemma init_nil n f :
  n ≤ 0 →
  init n f = [].
Proof.
  unfold init. case_decide'; eauto; intro.
  assert (n = 0) by lia. subst. reflexivity.
Qed.

Lemma init_singleton f :
  init 1 f = singleton (f 0).
Proof. reflexivity. Qed.

(* [replicate] applied to length 0 or 1. *)

Lemma replicate_nil n x :
  n ≤ 0 →
  replicate n x = [].
Proof. unfold replicate. eauto using init_nil. Qed.

Lemma replicate_singleton x i :
  i = 1 →
  replicate i x = singleton x.
Proof. intros ->. reflexivity. Qed.

(* Splitting [replicate n x] into two segments. *)

Lemma split_replicate x n i :
  0 ≤ i ≤ n  →
  replicate n x = replicate i x ++ replicate (n - i) x.
Proof.
  intros. listx k. destruct_decide' (k < i); eauto.
Qed.

Goal forall x n i,
  0 ≤ i ≤ n  →
  replicate n x = replicate i x ++ replicate (n - i) x.
Proof.
  (* An alternate proof, for fun. *)
  intros. split_seg i (replicate n x). eauto.
Qed.

(* Interaction of [fmap] and [replicate]. *)

Lemma fmap_replicate {B} x n (g : A → B) :
  g <$> (replicate n x) = replicate n (g x).
Proof.
  listx k. lookup. eauto.
Qed.

(* Interaction of [insert] and [replicate]. *)

Lemma insert_replicate n i x y :
  0 ≤ i < n →
  <[i := y]> (replicate n x) =
  replicate i x ++ singleton y ++ replicate (n - 1 - i) x.
Proof.
  intros. listx k.
  assert (k < i ∨ k = i ∨ i < k) as [|[|]] by lia; try subst; lookup; eauto.
Qed.

End Replicate.

Global Hint Rewrite
  Z.sub_0_r Z.sub_diag
  app_nil_l app_nil_r
  @replicate_nil
  @replicate_singleton
  @insert_replicate
  using (length; lia)
: replicate.

Ltac replicate :=
  autorewrite with replicate.

(* The following lemmas are optional, as they can be proved on the fly
   by the tactic [replicate]. *)

Lemma insert_replicate_nil {A} n (x y : A) :
  0 < n →
  <[0 := y]> (replicate n x) =
  singleton y ++ replicate (n-1) x.
Proof. intros. replicate. reflexivity. Qed.

Lemma insert_replicate_last {A} n (x y : A) :
  0 < n →
  <[n-1 := y]> (replicate n x) =
  replicate (n-1) x ++ singleton y.
Proof. intros. replicate. eauto. Qed.

Global Hint Rewrite
  @insert_replicate_nil
  @insert_replicate_last
  using (length; lia)
: replicate.

(* -------------------------------------------------------------------------- *)

(* Properties of [insert]. *)

Section Insert.
Context {A : Type}.
Implicit Types x : A.
Implicit Types xs ys zs : list A.

(* Interaction of [insert] and [singleton]. *)

Lemma insert_singleton_0 x y i :
  i = 0 →
  <[i:=y]> (singleton x) = singleton y.
Proof. intros. subst. reflexivity. Qed.

Lemma insert_singleton i x y :
  <[i:=y]> (singleton x) =
  if decide (i = 0) then singleton y else singleton x.
Proof.
  case_decide'; eauto.
  rewrite insert_invalid by (length; lia). eauto.
Qed.

(* Interaction of [insert] and [app]. *)

Lemma insert_app xs ys i x :
  <[i:=x]> (xs ++ ys) =
  if decide (i < length xs)
  then <[i:=x]> xs ++ ys
  else xs ++ <[i - length xs := x]> ys.
Proof.
  length_nonneg xs. unfold length in *.
  unfold insert, listz_insert. repeat case_decide'; eauto.
  - rewrite insert_app_l by lia. eauto.
  - rewrite insert_app_r_alt by lia. do 2 f_equal. lia.
Qed.

Lemma insert_app_l xs ys i x :
  i < length xs →
  <[i:=x]> (xs ++ ys) = <[i:=x]> xs ++ ys.
Proof.
  intros. rewrite insert_app. case_decide'. eauto.
Qed.

Lemma insert_app_r xs ys i x :
  length xs ≤ i →
  <[i:=x]> (xs ++ ys) = xs ++ <[i-length xs:=x]> ys.
Proof.
  intros. rewrite insert_app. case_decide'. eauto.
Qed.

(* This lemma is a port of [list_basics.insert_take_drop]. We recommend
   using [seg] rather than [take] and [drop]; see the next lemma. *)

Lemma insert_take_drop xs i x :
  valid i xs →
  <[i:=x]> xs = take i xs ++ x :: drop (i + 1) xs.
Proof.
  unfold length.
  intros.
  unfold insert, listz_insert. case_decide'.
  rewrite insert_take_drop by lia.
  rewrite cons_is_append.
  unfold take. case_decide'.
  unfold drop. case_decide'.
  repeat f_equal. lia.
Qed.

Lemma insert_split_seg xs i x :
  valid i xs →
  <[i:=x]> xs =
  seg 0 i xs ++ singleton x ++ seg (i + 1) (length xs) xs.
Proof.
  (* One nice proof: *)
  intros.
  listx k.
  rewrite list_lookup_insert. case_decide'.
  - assert (i = k) by lia. subst. lookup. eauto.
  - lookup_app_split. f_equal. lia.
Qed.

End Insert.

Global Hint Rewrite
  @cons_is_append
  @app_nil_r
  @app_nil_l
: insert.

Global Hint Rewrite
  @insert_invalid
  @insert_singleton_0
  @insert_app_l
  @insert_app_r
  @insert_replicate
  @replicate_nil
  @replicate_singleton
  @list_lookup_fmap
  using (length; lia)
: insert.

(* The tactic [update] simplifies an update [<[i:=x]> xs] when this does not
   introduce a conditional expression. *)

Global Ltac update :=
  autorewrite with insert.
