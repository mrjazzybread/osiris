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

Global Instance monadlaws_div : MonadLaws _.
Proof.
  (* The monad laws hold with respect to strong bisimulation [≅],
     which is the same as equality [=]. *)
  constructor; intros; eapply bisimulation_is_eq.
  { eapply Eqit.bind_ret_l. }
  { eapply Eqit.bind_ret_r. }
  { eapply Eqit.bind_bind. }
Qed.

(* This inversion lemma is used to simplify applications of [bind]
   in situations where an equation on [observe m] is known. *)

Lemma unfold_bind {A B} (m : div A) (f : A -> div B) :
  bind m f = bind_ m f.
Proof.
  apply bisimulation_is_eq. apply unfold_bind.
Qed.

(* ------------------------------------------------------------------------ *)

(* [skip] is a silent step. *)

Definition div_skip {A} (m : div A) :=
  Tau m.

Global Instance monadskip_div : MonadSkip div :=
  { skip := @div_skip }.

Local Ltac msimpl :=
  unfold Proper, eq1; simpl;
  unfold Eq1_ITree; simpl.

Global Instance monadskiplaws_div :
  MonadSkipLaws _ _.
Proof.
  constructor.
  (* bind_skip *)
  { msimpl. intros. unfold skip; simpl.
    (* The lemma [bind_tau] is a strong bisimulation statement. *)
    eapply bisimulation_is_eq. eapply bind_tau. }
Qed.

(* ------------------------------------------------------------------------ *)

(* The hard failure combinator [mzero]. *)

Program Definition div_mzero {A} : div A :=
  throw tt.

Global Instance div_monad_zero : MonadZero div :=
  { mzero := @div_mzero }.

Global Instance monadzerolaws_div :
  MonadZeroLaws _ _.
Proof.
  constructor; intros; simpl.
  eapply bisimulation_is_eq.
  unfold div_mzero.
  (* [bind (throw v) k] is [throw v]. *)
  (* This lemma seems to be missing in Interaction Trees. *)
  unfold throw.
  rewrite bind_vis.
  (* [vis (Throw v) k1 ≅ vis (Throw v) k2]. *)
  (* This lemma seems to be missing in Interaction Trees. *)
  (* The equality holds even if [k1] and [k2] are apparently distinct
     functions. They are functions of type [void → ...], so they are
     in fact extensionally equal. *)
  eapply fold_eqitF; [| simpl; reflexivity | simpl; reflexivity ].
  constructor. intros v. destruct v.
Qed.

(* ------------------------------------------------------------------------ *)

(* An iteration combinator [iter] is available. *)

Global Instance monaditer_div : MonadIter div :=
  MonadIter_itree.

Global Instance monaditerlaws_div :
  MonadIterLaws _ _ _.
Proof.
  constructor. msimpl. unfold skip, iter; simpl. intros.
  (* The lemma [Eqit.unfold_iter] is a strong bisimulation statement. *)
  eapply bisimulation_is_eq. eapply Eqit.unfold_iter.
Qed.
