From iris.proofmode Require Import proofmode environments ltac_tactics.

From osiris.lang Require Import lang.

From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import pure_tactics.

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
  | bi_forall _ =>
      (* Match case: [∀ η', ⌜Hη η'⌝ -∗ imp (eval η' e) ...].
         When [Hη] is a concrete equality [λ η', η' = δ], rewrite with it.
         When [Hη] is still an evar (unreachable branch), close via [False]. *)
      Control.plus
        (fun _ => ltac1:(iIntros (? ->)))
        (fun _ => ltac1:(iIntros (? [])))
  | bi_wand ?h _ =>
      lazy_match! h with
      | ⌜True⌝%I => iIntros "_"
      | True => iIntros "_"
      | ⌜False⌝%I => iIntros "[]"
      | False => iIntros "[]"
      | ⌜not _⌝%I =>
          (* [⌜¬P⌝ -∗ Q]: introduce [H : ¬P] and apply [([])], leaving
             sub-goal [P].  This lets the user close the no-match case
             with [auto]/[reflexivity] when P is a tautology (e.g. [1 = 1]). *)
          ltac1:(iIntros ([]))
      | ⌜_⌝%I =>
          ltac1:(_iIntros0 (intro_patterns.IPure (intro_patterns.IGallinaAnon)));
          (* If the introduced hypothesis is False-valued (e.g. [(False ∨ False) ∨ False]
             from a no-match branch), close the goal immediately via exfalso. *)
          try ltac1:(exfalso; tauto)
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
                         (* [?Hη δ] — the match postcondition evar applied to the
                            matched environment.  Instantiate [?Hη := λ η', η' = δ]
                            by proving the goal via [apply eq_refl] (Ltac1, which
                            uses full higher-order unification), so the continuation's
                            match case becomes [∀ η', ⌜η' = δ⌝ -∗ imp …].
                            If this fails the cleanup is simply skipped. *)
                         Control.plus
                           (fun _ => ltac1:(apply eq_refl))
                           (fun _ => ())
                   end))
       else ());
  (* Beta-reduce any redexes introduced by evar instantiation
     (e.g. [⌜(λ η', η' = δ) η'⌝] → [⌜η' = δ⌝]) so that [do_iintros]
     can recognise the equality and apply [iIntros (? ->)]. *)
  try (last (fun _ => ltac1:(cbn beta)));
  last (fun _ => iSplit; Control.enter do_iintros).


Ltac2 Notation "next_branch" := apply_deep_handle_cons ().
Tactic Notation "next_branch" := ltac2:(next_branch).
