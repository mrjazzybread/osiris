From ExtLib.Structures Require Export Monads MonadLaws.

(* The type class MonadFix in coq-ext-lib does not work for us,
   so we replace it with the following class. *)

Section MonadFixLaws.

  Context {m : Type -> Type}.
  Context (MF : MonadFix m).

  Class MonadFixLaws :=
    {
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

End MonadFixLaws.
