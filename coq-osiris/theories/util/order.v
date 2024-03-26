From iris.base_logic.lib Require Import iprop.

(* Definition of a preorder over carrier type [A], where the ordering is
    persistent. *)
Class preorder Σ (A : Type)  :=
  { order : A -d> A -d> iProp Σ;
    refl : (⊢ ∀ a, order a a)%I;
    trans : (⊢ ∀ a b c, order a b -∗ order b c -∗ order a c)%I;
    order_persistent :: forall a b, Persistent (order a b)}.

Notation "P ⊆ Q" := (order P Q)%I : bi_scope.
(* TODO: Add RewriteRelation? *)
