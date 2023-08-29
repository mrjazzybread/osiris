(* Equality on computations in the micro monad. *)

Inductive eq {A} : mon A → mon A → Prop :=
| EqRet a :
    eq (Ret a) (Ret a)
| EqFail :
    eq Fail Fail
| EqNext :
    eq Next Next
| EqStop req k1 k2 :
    (∀ v, eq (k1 v) (k2 v)) →
    eq (Stop req k1) (Stop req k2)
.

Local Hint Constructors eq : eq.

Local Infix "~" := eq (at level 70, no associativity).

(* Equality is reflexive and transitive. *)

Lemma eq_reflexive {A} (m : mon A) :
  m ~ m.
Proof.
  induction m; constructor; eauto.
Qed.

Lemma eq_transitive {A} (m1 m2 : mon A) :
  m1 ~ m2 → ∀ m3, m2 ~ m3 → m1 ~ m3.
Proof.
  induction 1; inversion 1; subst; constructor; eauto.
Qed.

Local Hint Resolve eq_reflexive : eq.
