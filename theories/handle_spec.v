From Coq.Logic Require Import PropExtensionality.
Require Import lang monads free eval handle spec.
Set Warnings "-notation-overridden".
Import spec.Notations.

(* This file proves certain properties of [handle] in the special case
   where the target monad is [spec]. *)

(* ------------------------------------------------------------------------ *)

(* The following notation is required for the following statement to be
   type-checked by Coq. Otherwise, the type-checker enters an infinite
   loop. *)

(* TODO fix this *)

Local Notation handle :=
  (@handle spec _ _ _ _).

(* ------------------------------------------------------------------------ *)

(* A paraphrase lemma about [handle]. *)

Lemma unfold_handle {A} (m : free A) (φ : A → Prop) :
  handle m ∋ φ ↔
  handle_body m ∋ spec_iter_body_post handle φ.
Proof.
  rewrite handle_fixed_point. simpl.
  apply descend_post. intros [|]; simpl; tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* [handle] interacts with [ret] in the following (trivial) way. *)

Lemma prove_handle_ret {A} (a : A) (φ : A → Prop) :
  φ a →
  handle (ret a) ∋ φ.
Proof.
  intros. rewrite handle_fixed_point. simpl. tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* We might wish to state that [handle] commutes with [bind] in a direct
   way, as an equality:

   Lemma handle_bind {A B} (m : free A) (f : A → free B) :
     handle (bind m f) =
     bind (handle m) (λ v, handle (f v)).

   We did so in the case of the divergence monad (see handle_div.v),
   and we were able to prove this fact via a co-inductive argument,
   because the equality of two computations in the [div] monad is a
   co-inductive relation.

   Here, however, the equality of two inhabitants of the [spec] is
   not co-inductively defined, so we cannot use such an argument. *)

(* Instead, we split this equality into two implications, and we prove
   one implication, arguably the most important one, the Bind rule.
   The proof, which involves an inductive invariant, is nontrivial
   (see below). It feels as though, to establish the Bind rule, we
   essentially have to prove the equivalence between small-step and
   big-step semantics. *)

(* TODO think about the proof of the reverse implication;
        think about proving both directions at once (unlikely). *)

(* ------------------------------------------------------------------------ *)

(* The statement that we want to prove is roughly
   that [bind (handle m) (handle f)] implies
        [handle (bind m f)].

   That is, we want to prove that [handle f]
   is able to swallow [handle m]
   when it comes in contact with it, in front of it. *)

(* To prove this fact, we must invent an invariant. This is a proof by
   semantic co-induction: [handle] has been defined as a greatest fixed point;
   so, to prove that [handle] holds, we must find a property that holds
   initially and that is preserved. *)

(* To express this invariant, we invent the property [stack n c φ]. This
   property is intuitively similar to [handle c ∋ φ]: that is, it means that
   the computation [c], transported by [handle] from the [free] monad to the
   [spec] monad, satisfies the postcondition [φ]. However, [handle c ∋ φ] is
   just the base case. In general, we allow the computation [c] to be a
   sequence of [n+1] computation segments, separated by [bind]s, and the
   specifications are chained. The specification of each segment is that it
   eventually produces a result [a] out of which the remaining segments are
   able to reach [φ]. *)

Local Fixpoint stack {B} (n : nat) (c : free B) (φ : B → Prop) : Prop :=
  match n with
  | 0 =>
      (* The base case: [c] guarantees [φ]. *)
      handle c ∋ φ
  | S n =>
      (* The step case: [c] is a sequence [bind m k]
         and [m] promises to produce a value [a]
         out of which the remaining segments, represented by [k a],
         guarantee [φ]. *)
      ∃ A (m : free A) (k : A → free B),
      c = bind m k ∧
      handle m ∋ (λ a, stack n (k a) φ)
  end.

(* The assertion [stack n c φ] is obviously covariant in [φ]. *)

Local Lemma stack_covariant {B} (φ φ' : B → Prop) :
  (∀ a, φ a → φ' a) →
  ∀ (n : nat) (c : free B),
  stack n c φ →
  stack n c φ'.
Proof.
  intros Hφφ'.
  induction n; intros c; simpl.
  { eauto using exploit_upward_closed. }
  { intros (A & m & k & ? & Hself).
    exists A, m, k. split; [ assumption |].
    eapply exploit_upward_closed; [| eauto ].
    simpl. eauto. }
Qed.

(* The invariant that we need is obtained by existentially quantifying
   over the height [n] of the stack. *)

(* [invariant] has type [free B → spec B]. *)

Local Program Definition invariant {B} (c : free B) : spec B :=
  λ (φ : B → Prop), ∃ n, stack n c φ.
Next Obligation.
  intros. simpl.
  intros φ φ' Hφφ'.
  intros (n & ?). exists n.
  eauto using stack_covariant.
Qed.

(* [handle] is contained in this invariant. *)

Local Lemma initialization {B} :
  handle ≼ @invariant B.
Proof.
  (* This amounts to creating a stack of height 0. *)
  intros i φ ?. exists 0. tauto.
Qed.

(* This invariant is preserved by [spec_iter_body handle_body],
   a function of type [(free B → spec B) → (free B → spec B)]. *)

Local Lemma preservation {B} :
  @invariant B ≼ spec_iter_body handle_body (@invariant B).
Proof.
  (* Put the goal into a suitable form for induction over [n]. *)
  intros i ψ.
  intros (n & H). revert n i ψ H.
  (* Reduction by induction over [n]. *)
  induction n; intros i ψ.
  (* Base case. *)
  { unfold stack.
    rewrite unfold_handle.
    rewrite unfold_spec_iter_body.
    eapply exploit_upward_closed; intros signal.
    eapply monotone_spec_iter_body_post.
    eapply initialization. }
  (* Step case. *)
  { intros (A & m & k & ? & Hm). subst i.
    rewrite unfold_spec_iter_body.
    (* By cases over [m]. *)
    destruct m as [ | | | [ η e ]].
    { rewrite bind_of_return by typeclasses eauto.
      rewrite handle_ret in Hm. simpl in Hm.
      specialize (IHn _ _ Hm).
      rewrite unfold_spec_iter_body in IHn.
      exact IHn. }
    { rewrite bind_fail.
      rewrite handle_fail in Hm. simpl in Hm.
      tauto. }
    { rewrite bind_next.
      rewrite handle_next in Hm. simpl in Hm.
      tauto. }
    { rewrite bind_stop. unfold handle_body. simpl.
      rewrite handle_stop, unfold_skip in Hm.
      (* Build a higher stack. *)
      exists (S n). do 3 eexists. split; [| eauto ].
      rewrite bind_bind. reflexivity. }
  }
Qed.

(* Thanks to this invariant, the proof is easy. *)

(* Yet, coming up with this invariant was hard. *)

Lemma prove_handle_bind :
  ∀ {A B} (m : free A) (f : A → free B) (φ : B → Prop),
  handle m ∋ (λ v, handle (f v) ∋ φ) →
  handle (bind m f) ∋ φ.
Proof.
  intros A B m f φ Hm.
  unfold handle.
  rewrite unfold_spec_iter_preliminary.
  exists invariant.
  split.
  (* Initialization. The invariant is initialized at height 1. *)
  { exists 1. simpl. eauto. }
  (* Preservation. *)
  { apply preservation. }
Qed.
