From orisis.semantics Require Import semantics.

(* -------------------------------------------------------------------------- *)

(* A Gallina function to simplify a term. *)


(* [maxsimp_aux _ m] computes a simplification of [m] as well as a proof that
   its result [r] is such that [simp m r].
   The treatment of [ko] in [Par _ _ _ ko] requires the Functional
   Extentionality axiom.

   This fixpoint is defined as a match over the term to simplify.
   It could have been defined in an interactive way, but the result was very
   hard to understand. Providing the term of the function directly helps
   understand what the function does.
   In the comments, "m ==> m'" means [simp m m'],
                    "m'1" means [(`m'1)], and
                    "m'2" means [(`m'2)].
 *)

Axiom TODO: forall A, A.
Require Import FunctionalExtensionality.

Fixpoint maxsimp_aux {A} (m: micro A):
  { m': micro A | simp m m' } :=
  match m as m0
        return (m = m0 → {m' : micro A | simp m0 m'}) with
  | @Stop _ X Y c x k => (* TODO! *)
      λ (Heq: m = Stop c x k),
      eq_rect m
              (λ m, { m': micro A | simp m m' })
              (exist _ m (SimpReflexive m))
              (Stop c x k) Heq

  (* In order to simplify [Par m1 m2 k ko], one should first simplify [m1]
     (resp. [m2]) into [m'1] (resp. [m'2]). Then:
     1. either [ko () <> Next],
        in which case one can only use the aforementioned simplifications of
        [m1] and [m2] ;
     2. either [ko () = Next], but [m'1 <> Ret _] and [m'2 <> Ret _],
        in which case one can only use the aforementioned simplifications of
        [m1] and [m2] ;
     3. either [ko () = Next] and
        a. [m'1 = Ret _] and [m'2 = Ret _],
           in which case, one should use [simp_par_ret_ret] ;
        b. [m'1 = Ret _] and [m'2 <> Ret _],
           in which case, one should use [SimpParRetLeft] ;
        c. [m'1 <> Ret _] and [m'2 = Ret _],
           in which case, one should use [SimpParRetRight]. *)
  | @Par _ A1 A2 m1 m2 k ko =>
      λ (_ : m = Par m1 m2 k ko),

        (* Simplifications of [m1] and [m2] *)
        let m'1 := @maxsimp_aux A1 m1 in
        let m'2 := @maxsimp_aux A2 m2 in

        (* Compute the value of ko. *)
        let ko_val := ko () in
        let Eko: ko () = ko_val := eq_refl in

        (* Check whether or not [ko = λ (), Next]. *)
        match ko_val as kov
              return (ko tt = kov → {m' : micro A | simp (Par m1 m2 k ko) m'})
        with
        | Next => (* [ko = λ tt, Next]. *)
            λ (Eq_ko: ko tt = Next),

            (* TODO: define a function that does not use the functional
               extensionality to get the required equality.
               (or at least, finish the proof by replacing the TODO below...) *)
            let Hko : forall x : unit, eq (ko x) Next := TODO _ in
            let Hko : ko = λ (_: ()), Next := functional_extensionality
                                                ko (λ _: (), Next)
                                                Hko in


            let H_m_m' : simp (Par m1 m2 k ko)
                              (Par (`m'1) (`m'2) k ko) :=
              SimpPar m1 (`m'1) m2 (`m'2) k ko
                      (proj2_sig m'1) (proj2_sig m'2) in

            (* Checking whether [m'1] or [m'2] is a [Ret _]. *)
            match (is_ret (`m'1), is_ret (`m'2))
                  as o return
                  let '(o1, o2) := o in
                  is_ret (`m'1) = o1 →
                  is_ret (`m'2) = o2 →
                  {m': micro A | simp (Par m1 m2 k ko) m'}
            with
            | (None, None) => (* Case (2.) *)
                fun _ => fun _ =>
                  (Par (`m'1) (`m'2) k ko ↾
                   SimpPar m1 (`m'1) m2 (`m'2) k ko
                               (proj2_sig m'1) (proj2_sig m'2))

            | (Some v1, Some v2) => (* Case (3.a.) *)
                λ (H1: is_ret (`m'1) = Some v1)
                  (H2: is_ret (`m'2) = Some v2),
                let H1: (`m'1) = Ret v1 := invert_is_ret_Some H1 in
                let H2: (`m'2) = Ret v2 := invert_is_ret_Some H2 in

                (* Prove that [Par (Ret v1) (Ret v2) k ko] ==> [k (v1, v2)]. *)
                let H_m'_m''_r_r : simp (Par (Ret v1) (Ret v2) k ko)
                                        (k (v1, v2)) :=
                  eq_ind_r (λ ko, simp (Par (Ret v1) (Ret v2) k ko)
                                       (k (v1, v2)))
                           (simp_par_ret_ret v1 v2 k) Hko in

                (* Prove that [Par (`m'1) (Ret v2) k ko] ==> [k (v1, v2)]. *)
                let H_m'_m''_m_r : simp (Par (`m'1) (Ret v2) k ko) (k (v1, v2)) :=
                  eq_ind_r (λ m, simp (Par m (Ret v2) k ko) (k (v1, v2)))
                           H_m'_m''_r_r H1 in

                (* Prove that [Par (`m'1) (Ret v2) k ko] ==> [k (v1, v2)]. *)
                let H_m'_m''_m_m : simp (Par (`m'1) (`m'2) k ko) (k (v1, v2)) :=
                  eq_ind_r (λ m, simp (Par (`m'1) m k ko) (k (v1, v2)))
                           H_m'_m''_m_r H2 in

                (* Use the transitivity to prove
                   [Par m1 m2 k ko] ==> [Par (`m'1) (`m'2) k ko]
                                    ==> [k (v1, v2)]. *)
                let H := SimpTransitive (Par m1 m2 k ko)
                                        (Par (`m'1) (`m'2) k ko)
                                        (k (v1, v2))
                                        H_m_m' H_m'_m''_m_m in

                k (v1, v2) ↾ H

            | (Some v1, None) => (* Case (3.b.) *)
                λ (H1: is_ret (`m'1) = Some v1)
                  (H2: is_ret (`m'2) = None),
                let H1: (`m'1) = Ret v1 := invert_is_ret_Some H1 in

                (* Prove that [Par (Ret v1) m'2] ==> [v2 ← m'2; k (v1, v2)]. *)
                let H2_r: simp (Par (Ret v1) (`m'2) k ko)
                               (v2 ← (`m'2);  (k (v1, v2))) :=
                  eq_ind_r (λ ko, simp (Par (Ret v1) (`m'2) k ko)
                                       (v2 ← (`m'2);  k (v1, v2)))
                           (SimpParRetLeft v1 (`m'2) k) Hko in

                (* Prove that [Par m'1 m'2] ==> [v2 ← m'2; k (v1, v2)]. *)
                let H2_m: simp (Par (`m'1) (`m'2) k ko)
                               (v2 ← (`m'2);  (k (v1, v2))) :=
                  eq_ind_r (λ m, simp (Par m (`m'2) k ko)
                                      (v2 ← (`m'2);  k (v1, v2)))
                           H2_r H1 in

                (* Use the transitivity to prove
                   [Par m1 m2 k ko] ==> [Par (`m'1) (`m'2) k ko]
                                    ==> [v2 ← m'2; k (v1, v2)]. *)
                (v2 ← (`m'2);  (k (v1, v2))) ↾
                SimpTransitive _ _ _ H_m_m' H2_m

            | (None, Some v2) => (* Case (3.c.) *)
                λ (H1: is_ret (`m'1) = None)
                  (H2: is_ret (`m'2) = Some v2),
                let H2: (`m'2) = Ret v2 := invert_is_ret_Some H2 in

                (* Prove that [Par m'1 (Ret v2)] ==> [v1 ← m'1; k (v1, v2)]. *)
                let H1_r: simp (Par (`m'1) (Ret v2) k ko)
                               (v1 ← (`m'1);  (k (v1, v2))) :=
                  eq_ind_r (λ ko, simp (Par (`m'1) (Ret v2) k ko)
                                       (v1 ← (`m'1);  k (v1, v2)))
                           (SimpParRetRight (`m'1) v2 k) Hko in

                (* Prove that [Par m'1 m'2] ==> [v2 ← m'2; k (v1, v2)]. *)
                let H1_m: simp (Par (`m'1) (`m'2) k ko)
                               (v1 ← (`m'1);  (k (v1, v2))) :=
                  eq_ind_r (λ m, simp (Par (`m'1) m k ko)
                                      (v1 ← (`m'1);  k (v1, v2)))
                           H1_r H2 in

                (* Use the transitivity to prove
                   [Par m1 m2 k ko] ==> [Par (`m'1) (`m'2) k ko]
                                    ==> [v2 ← m'2; k (v1, v2)]. *)
                (v1 ← (`m'1);  (k (v1, v2))) ↾
                SimpTransitive _ _ _ H_m_m' H1_m
            end eq_refl eq_refl

        (* 1. Matches [Par _ _ _ _], [Ret _], [Crash] *)
        | m0 =>
            λ (_: ko () = m0),
            exist _ (Par (`m'1) (`m'2) k ko) $
                  SimpPar _ _ _ _ _ _ (proj2_sig m'1) (proj2_sig m'2)
        end Eko

  (* Matches [Ret _], [Next] and [Crash] *)
  | m0 =>
      λ (Heq: m = m0),
      eq_rect m (λ m, { m': micro A | simp m m' }) (m ↾ SimpReflexive m) m0 Heq
  end eq_refl.

(* [maxsimp m] returns a simplified term [r] such that [simp m r]. *)
Definition maxsimp {A} (m: micro A) : micro A :=
  proj1_sig (maxsimp_aux m).

Lemma maxsimp_correct {A} (m: micro A):
    simp m (maxsimp m).
Proof. exact (proj2_sig (maxsimp_aux m)). Qed.

Global Opaque maxsimp_aux.
