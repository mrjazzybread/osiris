Require Import lang base free eval step steps Setoid Morphisms.
Require Import safe.

(* Refinement *)

Definition Par' {A1 A2 A3} (e: free A1) (e': free A2) (k: A1 * A2 -> free A3) :=
  Par e e' k (λ _, Next).

Definition refinement {A: Type} (m m': free A): Prop :=
  forall (φ: A -> Prop), safe m' φ -> safe m φ.

Class Refinement {A} (e e': free A) := { refine_expr : refinement e' e }.
Set Typeclasses Depth 10.
Set Typeclasses Strict Resolution.
Set Typeclasses Debug.



(** TODO: define a nice notation *)
Infix "◁" := (refinement) (at level 60).




#[global]
Instance safe_refinement_par {A1 A2 A}
  (m1 m1' : free A1) (m2 m2' : free A2)
  (φ : A1 * A2 → Prop)
  (k : A1 * A2 → free A)
  (ko: () -> free A)
  (R1: Refinement m1 m1')
  (R2: Refinement m2 m2'):
  Refinement (par m1 m2) (par m1' m2').
Proof.
  constructor.
  intros φ' (φ1 & φ2 & Hm1' & Hm2 & H)%invert_safe_par.
  inversion R1 as [H1]. inversion R2 as [H2].
  rewrite safe_par'.
  exists φ1, φ2.
  repeat split; eauto.
  intros v1 v2 H'1 H'2.
  now pose proof (H v1 v2 H'1 H'2) as H'%invert_safe_result.
Qed.

#[global]
Instance refinement_sym A: Reflexive (@refinement A).
Proof. now intros???. Qed.

Lemma safe_refinement_refl {A}
  (m: free A) : Refinement m m.
Proof. constructor. reflexivity. Qed.

#[global]
Instance refinement_trans A: Transitive (@refinement A).
Proof. intros???????; auto. Qed.

#[global]
Instance safe_refinement_trans {A}
(m m' m'': free A) (R1: Refinement m m') (R2: Refinement m' m''): Refinement m m''.
Proof. constructor. transitivity m'; apply refine_expr. Qed.

#[global]
Instance refinement_proper_par A B:
  Proper (@refinement A ==> @refinement B ==> @refinement (A * B)) par.
Proof.
  intros a1 a2 Ha b1 b2 Hb φ (φ1 & φ2 & Ha2 & Hb2 & H)%invert_safe_par.
  rewrite safe_par'.
  exists φ1, φ2.
  repeat split; eauto.
  intros v1 v2 H'1 H'2.
  now pose proof (H v1 v2 H'1 H'2) as H'%invert_safe_result.
Qed.

#[global]
Instance refinement_proper_Par' A B:
  Proper (@refinement A ==> @refinement B ==> eq ==> @refinement A) Par'.
Proof.
  intros a1 a2 Ha1 b1 b2 Hb1 ? φ -> φ' H2.

  pose proof (invert_safe_par a2 b2 φ φ' H2) as (φ1 & φ2 & Ha2 & Hb2 & H2').
  apply prove_safe_par with φ1 φ2; eauto.
Qed.

#[global]
Instance safe_refinement_Par A B C (ko: A * B -> free C) (a a': free A) (b b': free B)
  (R1: Refinement a a')
  (R2: Refinement b b'):
  Refinement (Par a b ko next) (Par a' b' ko next).
Proof.
  constructor.
  intros φ (φ1&φ2&Ha&Hb&H)%invert_safe_par.
  rewrite safe_par.
  exists φ1, φ2.
  repeat split; eauto;
  now apply refine_expr.
Qed.

#[global]
Instance refinement_proper_safe A:
Proper (@refinement A ==> eq ==> (Basics.flip impl)) safe.
Proof.
  intros x y Hxy φ ? -> H.
  auto.
Qed.

#[global]
Instance safe_refinement_call_ret_ret A B C
  (a: A) (b: B) (k: A * B -> free C):
  Refinement (k (a, b)) (Par (Ret a) (Ret b) k next).
Proof.
  constructor.
  intros φ H.
  now apply prove_safe_par_ret_ret.
Qed.
