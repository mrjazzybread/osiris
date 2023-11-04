(* -------------------------------------------------------------------------- *)

(* Encoding propositions as Boolean values. *)

(* It is doubtful whether this is a good idea. Allowing the tactic [encode] to
   use [solve_encode_False] and [solve_encode_True], when [P] is a
   metavariable, leads Coq to instantiate [P] with an arbitrary proposition
   that happens to be provably false or provably true. *)

Require Import Epsilon.

Definition inh_bool : inhabited bool.
Proof. constructor. constructor. Qed.

Definition switch P (b : bool) :=
  if b then P else ¬ P.

Definition Prop2bool (P : Prop) : bool :=
  epsilon inh_bool (switch P).

Lemma Prop2bool_False (P : Prop) :
  ¬ P →
  Prop2bool P = false.
Proof.
  intros H.
  unfold Prop2bool.
  assert (existence: exists b, switch P b).
  { exists false. unfold switch. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  generalize (epsilon inh_bool (switch P)).
  unfold switch. intros [|]; tauto.
Qed.

Lemma Prop2bool_True (P : Prop) :
  P →
  Prop2bool P = true.
Proof.
  intros H.
  unfold Prop2bool.
  assert (existence: exists b, switch P b).
  { exists true. unfold switch. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  generalize (epsilon inh_bool (switch P)).
  unfold switch. intros [|]; tauto.
Qed.

Global Instance Encode_Prop : Encode Prop :=
  { encode := λ P, VBool (Prop2bool P) }.

Lemma solve_encode_False (P : Prop) :
  ¬ P →
  VFalse = #P.
Proof.
  intros H. apply Prop2bool_False in H. simpl. rewrite H. reflexivity.
Qed.

Lemma solve_encode_True (P : Prop) :
  P →
  VTrue = #P.
Proof.
  intros H. apply Prop2bool_True in H. simpl. rewrite H. reflexivity.
Qed.

Global Hint Resolve solve_encode_False solve_encode_True : encode.
