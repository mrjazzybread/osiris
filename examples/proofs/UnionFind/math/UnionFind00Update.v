From stdpp Require Import base tactics decidable.
From Stdlib Require Import FunctionalExtensionality.

(* ------------------------------------------------------------------------ *)
(* Updating a function on a whole equivalence class. *)

(* This file is shared between the SEQUENTIAL development (UnionFind.v) and
   the CONCURRENT one (UnionFind12GhostInv.v, ConcurrentUnionFind.v). Both
   expose the same abstract state — a representative function [R], and a
   value function [V] constrained by [V u = V (R u)] — and both therefore
   face the same problem: no client-visible update to [V], or to [R]
   itself, can be a point update, because every member of a class must
   keep the same image. Every such update is an update to a whole class,
   and this is the algebra of that one operation.

   Every abstract transition either structure ever makes is an instance:

     make    V.[x  -/R/> v]        (the fresh vertex's class is [x] alone)
     set     V.[x  -/R/> v]
     union   R.[x  -/R/> z]  and  V.[x  -/R/> V z]

   — the last being the only one that moves [R], and the reason the
   operation is stated for an arbitrary [f] rather than for a value
   function specifically. *)

(* [f] is idempotent. For a representative function this is what makes its
   fibres a partition — i.e. what makes "same class" mean anything — and
   it is what the lemmas below about [R x] rest on. *)

Class Idempotent {A : Type} (f : A → A) :=
  { idempotent : ∀ x, f (f x) = f x }.

(* [fcupdate f P b] coincides with [f] everywhere, except that it maps every
   point satisfying the (decidable) predicate [P] to [b]. *)

Definition fcupdate {A B : Type} (f : A → B) (P : A → Prop)
    `{!∀ a, Decision (P a)} (b : B) : A → B :=
  λ a, if decide (P a) then b else f a.

(* [update_class R x f b] coincides with [f] everywhere, except on the
   equivalence class of [x], whose elements are all mapped to [b]. *)

Definition update_class {A B : Type} `{EqDecision A}
    (R : A → A) (x : A) (f : A → B) (b : B) : A → B :=
  fcupdate f (λ z, R z = R x) b.

Notation "f .[ x -/ R /> b ]" :=
    (update_class R x f b)
      (at level 2, left associativity, format "f .[ x  -/ R />  b ]").

Lemma lookup_update_class {A B : Type} `{EqDecision A}
    (f : A → B) x R (b : B) :
  f.[ x -/R/> b ] x = b.
Proof.
  unfold update_class, fcupdate.
  rewrite decide_True; reflexivity.
Qed.

Lemma lookup_update_class_ne {A B : Type} `{EqDecision A}
    (f : A → B) R x (b : B) a :
  R a ≠ R x →
  f.[x -/R/> b] a = f a.
Proof.
  intros.
  unfold update_class, fcupdate.
  rewrite decide_False; [ reflexivity | assumption ].
Qed.

(* Naming a class by its representative or by any of its members is the
   same thing. *)

Lemma update_class_root {A B : Type} `{EqDecision A} {R : A → A}
    `{@Idempotent A R} (f : A → B) x (b : B) :
  f.[R x -/R/> b] = f.[x -/R/> b].
Proof.
  unfold update_class, fcupdate.
  extensionality a.
  rewrite idempotent.
  case_decide; reflexivity.
Qed.

(* An update to a whole class preserves "reads through the representative":
   this is what keeps the invariant [V u = V (R u)] true across [make],
   [set] and [update]. *)

Lemma lookup_class_root {A B : Type} `{EqDecision A} {R : A → A}
    `{@Idempotent A R} (f : A → B) r x (b : B) :
  f x = f (R x) →
  f.[r -/R/> b] x = f.[r -/R/> b] (R x).
Proof.
  intros Hequiv.
  unfold update_class, fcupdate.
  rewrite idempotent.
  case_decide; first reflexivity.
  apply Hequiv.
Qed.

(* A class may be named by any of its members. [update_class_root] is the
   special case where one of the two names is the representative. *)

Lemma update_class_congr_class {A B : Type} `{EqDecision A}
    (R : A → A) x y (f : A → B) (b : B) :
  R x = R y →
  f.[x -/R/> b] = f.[y -/R/> b].
Proof. unfold update_class, fcupdate. by intros ->. Qed.

(* We can reorder updates if they are to the same value [b]. *)

Lemma update_classes_comm {A B : Type} `{EqDecision A}
    (f : A → B) R x y (b : B) :
  f.[x -/R/> b].[y -/R/> b] = f.[y -/R/> b].[x -/R/> b].
Proof.
  unfold update_class, fcupdate.
  extensionality a.
  case_decide; case_decide; tauto.
Qed.

(* Updating [x]'s class to [R x] is a no-op on [R]. *)

Lemma update_class_R_diag {A : Type} `{EqDecision A} (R : A → A) x :
  R.[ x -/R/> (R x)] = R.
Proof.
  unfold update_class, fcupdate.
  extensionality a. case_decide; eauto.
Qed.

(* Redirecting a class only ever MERGES classes: whatever was equivalent
   before still is. This is the obligation the linking CAS discharges, and
   it is the reason recorded equivalences may be kept forever. *)

Lemma update_class_R_congr {A : Type} `{EqDecision A} (R : A → A) x z u w :
  R u = R w →
  R.[x -/R/> z] u = R.[x -/R/> z] w.
Proof. unfold update_class, fcupdate. by intros ->. Qed.
