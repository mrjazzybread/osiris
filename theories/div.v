From stdpp Require Import base.
From ITree Require Import ITree Eq EqAxiom Exception ITreeMonad.
Require Import monads.

(* ------------------------------------------------------------------------ *)

(* A divergence and failure monad. *)

(* This type is co-inductive and offers a [skip] operation for silent steps,
   as usual in a divergence monad. It also offers a hard failure operation,
   modeled as an exception that carries a unit argument. *)

Definition div A :=
  itree (exceptE unit) A.

(* ------------------------------------------------------------------------ *)

(* Because [itree] is a monad, [div] is a monad. *)

Global Instance monad_div : Monad div :=
  Monad_itree.

Arguments monad_div /.

(* ------------------------------------------------------------------------ *)

(* [skip] is a silent step. *)

Definition div_skip {A} (m : div A) :=
  Tau m.

Arguments div_skip {A} m /.

Global Instance monadskip_div : MonadSkip div :=
  { skip := @div_skip }.

Arguments monadskip_div /.

Local Ltac msimpl :=
  unfold Proper, eq1; simpl;
  unfold Eq1_ITree; simpl.

Global Instance monadskiplaws_div :
  MonadSkipLaws monad_div monadskip_div.
Proof.
  constructor.
  (* bind_skip *)
  { msimpl. intros. unfold skip; simpl.
    (* The lemma [bind_tau] is a strong bisimulation statement. *)
    eapply bisimulation_is_eq. eapply bind_tau. }
Qed.

(* ------------------------------------------------------------------------ *)

(* An iteration combinator [iter] is available. *)

Global Instance monaditer_div : MonadIter div :=
  MonadIter_itree.

Arguments monaditer_div /.

Global Instance monaditerlaws_div :
  MonadIterLaws _ _ _.
Proof.
  constructor. msimpl. unfold skip, iter; simpl. intros.
  (* The lemma [Eqit.unfold_iter] is a strong bisimulation statement. *)
  eapply bisimulation_is_eq. eapply Eqit.unfold_iter.
Qed.
