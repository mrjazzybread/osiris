From Coq Require Import Morphisms.
From ExtLib.Structures Require Export Monads MonadLaws.
From ITree Require Export Monad Basics.

(* TODO this file needs cleaning up *)

Ltac false :=
  elimtype False.

Section MonadFixLaws.

Context {m : Type -> Type}.

(* The type class MonadFixLaws in coq-ext-lib does not work for us,
   so we replace it with the following class. *)

Class MonadFixLaws (MF : MonadFix m) := {
  mleq :
    forall {A}, m A -> m A -> Prop;
  mleq_reflexive :
    forall {A} (m : m A),
    mleq m m;
  mleq_transitive :
    forall {A} (m1 m2 m3 : m A),
    mleq m1 m2 -> mleq m2 m3 -> mleq m1 m3;
  mfix_fixed_point :
    forall {T A} (ff : (T -> m A) -> (T -> m A)),
    (forall p1 p2,
      (forall t, mleq (p1 t) (p2 t)) ->
      (forall t, mleq (ff p1 t) (ff p2 t))) ->
    mfix ff = ff (mfix ff)
}.

Class MonadFixCoinduction (MF : MonadFix m) (MFL : MonadFixLaws MF) := {
  mfix_coinduction :
    forall {T A} (ff : (T -> m A) -> (T -> m A)) (p : T -> m A),
    (forall t, mleq (p t) (ff p t)) ->
    (forall t, mleq (p t) (mfix ff t))
}.

End MonadFixLaws.

Polymorphic Class MonadSkip (m : Type -> Type) : Type :=
  skip : forall {A}, m A -> m A.

Section MonadSkipLaws.

Context {m : Type -> Type}.

Context (M : Monad m).
Context (MS : MonadSkip m).

Class MonadSkipLaws := {
  bind_skip :
    forall A B (c : m A) (f : A -> m B),
    bind (skip c) f = skip (bind c f)
}.

End MonadSkipLaws.

(* ITree.Basics.CategoryTheory defines the type class [IterUnfold],
   which is related to the statement below, but is unfortunately
   stated in a more abstract way. *)

Section MonadIterLaws.

Context {m : Type -> Type}.

Context (M : Monad m).
Context (MI : MonadIter m).
Context (MS : MonadSkip m).

Class MonadIterLaws := {
  unfold_iter :
    forall {R I} (body : I -> m (I + R)) (i : I),
    iter body i =
      (* Evaluate [body] out the state [i]. *)
      bind (body i) (fun (signal : I + R) =>
        match signal with
        | inl j =>
            (* If the body yields a new state [j], continue. *)
            skip (iter body j)
        | inr r =>
            (* If the body yields a result [r], return this result. *)
            ret r
        end)
  }.

End MonadIterLaws.
