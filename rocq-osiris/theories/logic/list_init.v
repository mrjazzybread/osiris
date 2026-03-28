From stdpp Require Import list.

(** [init_segment i n f] is a list of length [n] whose elements are [f(i)],
    [f(i+1)], etc., up to [f(i+n-1)]. *)
Fixpoint init_segment {A} (i : nat) (n : nat) (f : nat → A) : list A :=
  match n with 0 => [] | S n => f i :: init_segment (i + 1) n f end.

(** [init n f] is a list of length [n] whose elements are [f(0)],
    [f(1)], etc., up to [f(n-1)]. *)
Definition init {A} (n : nat) (f : nat → A) : list A :=
  init_segment 0 n f.

(** ** Properties of [init_segment] and [init] *)

Section Init.
Context {A : Type}.
Implicit Types xs : list A.
Implicit Types f : nat → A.

(* Interaction with [length]. *)

Lemma length_init_segment i n f : length (init_segment i n f) = n.
Proof.
  revert i. induction n; simpl; congruence.
Qed.

Lemma length_init n f : length (init n f) = n.
Proof. unfold init. apply length_init_segment. Qed.

(* Interaction with [lookup]. *)

Lemma lookup_init_segment_lt i n f k :
  k < n →
  init_segment i n f !! k = Some (f (i + k)).
Proof.
  revert i k. induction n; simpl; intros; [ lia |].
  rewrite lookup_cons.
  destruct k as [| k]; try rewrite IHn by lia;
  do 2 f_equal; lia.
Qed.

Lemma lookup_init_segment_ge i n f k :
  n ≤ k →
  init_segment i n f !! k = None.
Proof.
  revert i k. induction n; simpl; intros; [ eauto |].
  rewrite lookup_cons.
  destruct k as [| k]; try rewrite IHn by lia;
  eauto with lia.
Qed.

Lemma lookup_init_segment i n f k :
  init_segment i n f !! k =
    if decide (k < n) then Some (f (i + k)) else None.
Proof.
  case_decide;
  eauto using lookup_init_segment_lt, lookup_init_segment_ge with lia.
Qed.

Lemma lookup_init_lt n f k :
  k < n →
  init n f !! k = Some (f k).
Proof.
  unfold init. eauto using lookup_init_segment_lt.
Qed.

Lemma lookup_init_ge n f k :
  n ≤ k →
  init n f !! k = None.
Proof.
  unfold init. eauto using lookup_init_segment_ge.
Qed.

Lemma lookup_init n f k :
  init n f !! k =
    if decide (k < n) then Some (f k) else None.
Proof.
  case_decide; eauto using lookup_init_lt, lookup_init_ge with lia.
Qed.

(* Interaction with [lookup_total]. *)

Section LookupTotal.
Context `{Inhabited A}.

Local Ltac translate lemma :=
  intros; rewrite !list_lookup_total_alt;
  rewrite lemma by lia; repeat case_decide; eauto.

Lemma lookup_total_init_segment_lt i n f k :
  k < n →
  init_segment i n f !!! k = f (i + k).
Proof.
  translate lookup_init_segment_lt.
Qed.

Lemma lookup_total_init_segment_ge i n f k :
  n ≤ k →
  init_segment i n f !!! k = inhabitant.
Proof.
  translate lookup_init_segment_ge.
Qed.

Lemma lookup_total_init_segment i n f k :
  init_segment i n f !!! k =
    if decide (k < n) then f (i + k) else inhabitant.
Proof.
  translate lookup_init_segment.
Qed.

Lemma lookup_total_init_lt n f k :
  k < n →
  init n f !!! k = f k.
Proof.
  translate lookup_init_lt.
Qed.

Lemma lookup_total_init_ge n f k :
  n ≤ k →
  init n f !!! k = inhabitant.
Proof.
  translate lookup_init_ge.
Qed.

Lemma lookup_total_init n f k :
  init n f !!! k =
    if decide (k < n) then f k else inhabitant.
Proof.
  translate lookup_init.
Qed.

End LookupTotal.

(* Interaction of [take] and [init]. *)

Lemma take_init n m f :
  take n (init m f) = init (n `min` m) f.
Proof.
  eapply list_eq_same_length.
  + rewrite length_init. eauto.
  + rewrite length_take, length_init. eauto.
  + intros i x y ?.
    rewrite lookup_take, !lookup_init.
    repeat case_decide; congruence.
Qed.

(* Interaction of [drop] and [init]. *)

Lemma drop_init n m f :
  drop n (init m f) = init (m - n) (λ i, f (n + i)).
Proof.
  eapply list_eq_same_length.
  + rewrite length_init. eauto.
  + rewrite length_drop, length_init. eauto.
  + intros i x y ?.
    rewrite lookup_drop, !lookup_init.
    repeat case_decide; congruence.
Qed.

(* Extension of [init] with one more element. *)

Lemma init_segment_app_singleton i n f x :
  f (i + n) = x →
  init_segment i n f ++ [x] = init_segment i (n + 1) f.
Proof.
  revert i.
  induction n as [| n]; simpl; intros; subst x; do 2 f_equal.
  + lia.
  + rewrite IHn by (f_equal; lia). eauto.
Qed.

Lemma init_app_singleton n f x :
  f n = x →
  init n f ++ [x] = init (n + 1) f.
Proof.
  intros. subst x. unfold init. eapply init_segment_app_singleton. eauto.
Qed.

End Init.
