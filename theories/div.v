From stdpp Require Import base.
From ITree Require Import ITree Eq Exception ITreeMonad.
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

(* We use [eutt], also known as [≈], as the natural notion of equality
   between computations. That said, some of the statements below would
   hold also with a stronger equality; e.g. [MonadSkipLawE] would hold
   with strong bisimulation [≅]. *)

Global Instance eq1_div : Eq1 div :=
  Eq1_ITree.

Arguments eq1_div /.

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
  MonadSkipLawsE monad_div monadskip_div.
Proof.
  constructor.
  (* Proper_skip *)
  { msimpl. intros A m1 m2. unfold skip; simpl. intros.
    (* We exploit the fact that equality ignores [Tau] steps. That said,
       this congruence property would be true even if we used a stronger
       equality that does not ignore silent steps. *)
    do 2 rewrite tau_eutt. assumption. }
  (* bind_skip *)
  { msimpl. intros. unfold skip; simpl.
    (* The lemma [bind_tau] is a strong bisimulation statement. A fortiori,
       a weak bisimulation statement holds as well. *)
    rewrite bind_tau. reflexivity. }
Qed.

(* ------------------------------------------------------------------------ *)

(* An iteration combinator [iter] is available. *)

Global Instance monaditer_div : MonadIter div :=
  MonadIter_itree.

Arguments monaditer_div /.

Global Instance monaditerlaws_div :
  MonadIterLawsE _ _ _.
Proof.
  constructor. msimpl. unfold skip, iter; simpl. intros.
  (* The lemma [Eqit.unfold_iter] is a strong bisimulation statement. *)
  rewrite Eqit.unfold_iter. reflexivity.
Qed.
