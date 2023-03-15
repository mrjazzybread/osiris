Require Import lang monads free eval step safe spec.

(* This file defines [safety], a function of type [free A → spec A], and
   establishes some of its properties. *)

(* We probably do not need [safety]: we could work with [safe] everywhere.
   Still, it is interesting to know that [safety] coincides with [handle],
   a fact that we prove in handle_safety.v. *)

(* -------------------------------------------------------------------------- *)

(* Because [safe m] is covariant in [φ], it can be viewed as an inhabitant
   of the [spec] monad. In other words, [safety] can be viewed as function
   of type [free A → spec A]. *)

Program Definition safety {A} (m : free A) : spec A :=
  safe m.
Next Obligation.
  simpl. eauto using safe_covariant.
Qed.

Lemma unfold_safety {A} (m : free A) (φ : A → Prop) :
  safety m ∋ φ ↔ safe m φ.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [safety] commutes with [ret]. *)

Lemma safety_ret {A} (a : A) :
  safety (ret a) = (ret a).
Proof.
  intros. eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  rewrite safe_ret.
  tauto.
Qed.

(* [safety] commutes with [mzero]. *)

Lemma safety_stuck {A} (m : free A) :
  stuck m →
  safety m = mzero.
Proof.
  intros Hstuck.
  eapply prove_spec_eq_ext. intros.
  rewrite unfold_safety.
  apply safe_stuck.
  assumption.
Qed.

Lemma safety_mzero {A} :
  safety (mzero : free A) = mzero.
Proof.
  eauto using safety_stuck, stuck_Fail.
Qed.

(* [safety] commutes with [bind]. *)

Lemma safety_bind {A B} (m1 : free A) (m2 : A → free B) :
  safety (bind m1 m2) = bind (safety m1) (λ a, safety (m2 a)).
Proof.
  eapply prove_spec_eq_ext. intros φ. rewrite unfold_safety. apply safe_bind.
Qed.
