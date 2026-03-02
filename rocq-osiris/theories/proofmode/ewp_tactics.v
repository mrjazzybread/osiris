From iris.proofmode Require Import proofmode environments ltac_tactics.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import specifications pure_tactics.

From osiris.tactics Require Import tactics.

(** *Utility *)

Section helper_lemmas.

Context `{!osirisGS Σ}.

Lemma bi_sep_intro (P Q : iProp Σ) :
  P -∗
  Q -∗
  P ∗ Q.
Proof.
  iIntros "H1 H2".
  iFrame.
Qed.

Lemma bi_emp_intro :
  ⊢ @bi_emp (iProp Σ).
Proof.
  done.
Qed.

End helper_lemmas.

From Ltac2 Require Import Ltac2.


Create HintDb osiris.

Set Default Proof Mode "Classic".

(* Some hints used for resolving [repr] expressions *)
Global Hint Rewrite eq_repr_repr sub_repr_repr mul_repr_repr: osiris.
Global Hint Extern 1 (representable _) => representable : osiris.
Global Hint Unfold val_as_int : osiris.

(* -------------------------------------------------------------------------- *)

(** *Automation *)
(* Extending the [by] and [done] tactics to solve trivial things in proof mode *)

(* Useful for goals of the shape (⊢ ∀ (e : void), _), _.) which come up when
  reasoning about exceptional continuations *)
Global Hint Extern 0 (envs_entails _ (bi_forall (fun _ : void => _))) => iIntros (?)
; try done : core.

(** *Set postcondition *)

(* Force a postcondition, for example when the postcondition is an evar and one
   wants to perform an induction *)
Ltac2 set_postcondition_tac (φ : constr) : unit :=
  lazy_match! get_iris_goal () with
  | impure ?_e ?_m ?_Ψ ?_ζ ?Φ =>
      Std.unify Φ φ
  | _ => Control.zero
           (Tactic_failure (Some (Message.of_string "Expected goal of the form [imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}]")))
  end.
Ltac2 Notation "set_postcondition" φ(constr) := set_postcondition_tac φ.
Tactic Notation "set_postcondition" uconstr(φ) :=
  let tac := ltac2:(φ |- set_postcondition_tac (Option.get (Ltac1.to_constr φ))) in
  tac φ.


(* -------------------------------------------------------------------------- *)

(** *Proving Handlers and Matches *)

(* Proving that a handler satisfies its specification involves proving
   the effectful case and the return/exceptional case. *)

Ltac prove_handler_spec :=
  rewrite deep_handler_spec_unfold; iSplit.


(* -------------------------------------------------------------------------- *)

(** *Entering and Skipping Handler Branches *)

Ltac2 do_iintros () :=
  try (iModIntro);
  lazy_match! get_iris_goal () with
  | bi_wand ?h _ =>
      lazy_match! h with
      | ⌜True⌝%I => iIntros "_"
      | True => iIntros "_"
      | ⌜False⌝%I => iIntros "[]"
      | False => iIntros "[]"
      | ⌜_⌝%I =>
          ltac1:(_iIntros0 (intro_patterns.IPure (intro_patterns.IGallinaAnon)))
      | _ => iIntros "?"
      end
  | _ => ()
  end.

(* [apply_deep_handle_cons] expects an iris goal of the form
   [EWP deep_eval_match η (b :: bs) ...]. It applies the
   [deep_handle_cons_unary] lemma before progressing through the
   pattern matching.

   It is the iris proofmode analog of [pure_match] in the pure mode. *)

Ltac2 apply_deep_handle_cons () :=
  iApply deep_handle_cons;
  Control.focus 1 1
    (fun _ =>
       iPureIntro;
       let n := specify_cpattern () in
       if (Int.gt n 0)
       then
         (* [specify_cpattern] resolves
            a [cpattern] and leaves behind a [pattern] which needs
            to be solved with a [pattern_match0] here;
            and since [pattern_match0] does not return an integer
            of how many goals are left, we must use [try] which is not
            ideal. *)
         Control.focus 1 n pattern_match0;
         try (Control.focus 1 n
                (fun _ =>
                   match! goal with
                   | [ |- ?g ] =>
                       if Constr.is_evar g then
                         apply I
                       else
                         iStartProof
                   end))
       else ());
  last (iSplit; do_iintros).


Ltac2 Notation "next_branch" := apply_deep_handle_cons ().
Tactic Notation "next_branch" := ltac2:(next_branch).
