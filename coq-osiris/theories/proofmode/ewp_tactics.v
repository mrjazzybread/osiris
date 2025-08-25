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

From Ltac2 Require Import Ltac2.

(* -------------------------------------------------------------------------- *)

(** *Ltac2 bindings for Iris Proofmode tactics *)

Ltac2 iapply (lem : constr) (sel : constr option) :=
  match sel with
  | None => ltac1:(lem |- iApply lem) (Ltac1.of_constr lem)
  | Some sel =>
      ltac1:(lem sel |- iApply (lem with sel))
              (Ltac1.of_constr lem) (Ltac1.of_constr sel)
  end.

Ltac2 Notation "iApply" "(" lem(constr) "with" sel(constr) ")" := iapply lem (Some sel).
Ltac2 Notation "iApply" lem(constr) := iapply lem None.

Ltac2 iintros (pat : constr) :=
  ltac1:(pat |- iIntros pat) (Ltac1.of_constr pat).

Ltac2 Notation "iIntros" pat(constr) := iintros pat.

Ltac2 iFrame () := ltac1:(iFrame).
Ltac2 Notation "iFrame" := iFrame ().

Ltac2 iSplit () := ltac1:(iSplit).
Ltac2 Notation "iSplit" := iSplit ().

Ltac2 iSplitL (selpat : constr) := ltac1:(selpat |- iSplitL selpat) (Ltac1.of_constr selpat).
Ltac2 Notation "iSplitL" pat(constr) := iSplitL pat.

Ltac2 iSplitR (selpat : constr) := ltac1:(selpat |- iSplitR selpat) (Ltac1.of_constr selpat).
Ltac2 Notation "iSplitR" pat(constr) := iSplitR pat.

Ltac2 iDestruct (lem : constr) (pat : constr) :=
  ltac1:(lem pat |- iDestruct (lem) as pat)
    (Ltac1.of_constr lem) (Ltac1.of_constr pat).
Ltac2 Notation "iDestruct" "(" lem(constr) ")" "as" pat(constr) := iDestruct lem pat.

Ltac2 iRevert (h : constr) :=
  ltac1:(h |- iRevert h) (Ltac1.of_constr h).
Ltac2 Notation "iRevert" h(constr) := iRevert h.

Ltac2 iPureIntro () := ltac1:(iPureIntro).
Ltac2 Notation "iPureIntro" := iPureIntro ().

Ltac2 iStartProof () := ltac1:(iStartProof).
Ltac2 Notation "iStartProof" := iStartProof ().

Ltac2 iModIntro () := ltac1:(iModIntro).
Ltac2 Notation "iModIntro" := iModIntro ().

Tactic Notation "iIntros_RET" :=
  iIntros ([|]); [ simpl | iIntros "[]" ].
Tactic Notation "iIntros_RET" constr(pat) :=
  iIntros ([|]); [ simpl; iIntros pat | iIntros "[]" ].
Tactic Notation "iIntros_RET" "(" simple_intropattern(v) ")" :=
  iIntros ([ v |]); [ simpl | iIntros "[]" ].
Tactic Notation "iIntros_RET" "(" simple_intropattern(v) ")" constr(pat) :=
  iIntros ([ v |]); [ simpl; iIntros pat | iIntros "[]" ].


(** *Utility *)

Section helper_lemmas.

Context `{!osirisGS Σ}.

Set Default Proof Mode "Classic".

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

Ltac2 all (tac : unit -> unit) :=
  Control.extend [] tac [].

(* [iris_goal] gives the current iris goal. *)

Ltac2 iris_goal () : constr :=
  lazy_match! goal with
  | [ |- environments.envs_entails _ ?g ] => g
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected an iris proofmode goal")))
  end.

Ltac2 iris_env () : constr :=
  lazy_match! goal with
  | [ |- environments.envs_entails ?env _ ] => env
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected an iris proofmode goal")))
  end.

(* Given a constr of the form [▷^n c] (where [n] might equal 0),
   [strip_laters] returns [c]. *)

Ltac2 rec strip_laters (g : constr) :=
  lazy_match! g with
  | bi_later ?c => strip_laters c
  | _ => g
  end.

Create HintDb osiris.

(* Some hints used for resolving [repr] expressions *)
Global Hint Rewrite eq_repr_repr sub_repr_repr mul_repr_repr: osiris.
Global Hint Extern 1 (representable _) => representable : osiris.
Global Hint Unfold val_as_int : osiris.

(** *"WP" tactics

  These tactics operate on [WP] goals are Hoare-style;

  All tactics that are not "Hoare-style" are internal and should not be exposed
  to the user. *)

(** [uchange A with B] is an untyped version of [change A with B]: it guesses
  types in [A = B] instead of trying to type [A] and [B] independently *)
Tactic Notation "uchange" uconstr(A) "with" uconstr(B) :=
  let Heq := fresh "Heq" in
  assert (A = B) as Heq;
  [ | rewrite Heq; clear Heq ];
  [ reflexivity | ].

(** Use [iExactEq "H"] if the Iris goal is provably equal, but not convertible
   to, an Iris hypothesis ["H" : hyp], which will replace your [goal] with
   [⌜goal = hyp⌝] *)
Tactic Notation "iExactEq" constr(irisHyp) :=
  match goal with
  | |- envs_entails ?Δ ?goal =>
    match Δ with
    | context[Esnoc _ (INamed irisHyp) ?hyp] =>
      iAssert ⌜goal = hyp⌝%I as %->; [ | iApply irisHyp ]
    end
  end.

(** Use [iExactEq "H" n] to perform [iPureIntro] and n [f_equal]s just after *)
Tactic Notation "iExactEq" constr(irisHyp) int_or_var(n) :=
  iExactEq irisHyp; iPureIntro; do n f_equal.

(* -------------------------------------------------------------------------- *)

(* If anything has been added to the hint data base of [osiris], using
    [Hint Rewrite] or [Hint Extern], then apply the automation. *)
Ltac Auto :=
  autorewrite with osiris;
  auto with osiris.

(* [EWP normal form]
    An assertion that checks whether the current goal is in normal form, i.e.
    of the form ewp [..] *)
(* Turn expression to normal form; (i.e. apply monadic unit/associativity
  properties) *)
Ltac Normalize :=
  (* Normalize monadic [bind] and [ret] *)
  cbn [bind];
  repeat
  match goal with
  | |- envs_entails _ (ewp_def _ (Par _ _ _ _) _ _) => Par
  | |- envs_entails _ (ewp_def _ (bind _ _) _ _) => Bind
  | |- envs_entails _ (ewp_def _ (ret _) _ _) => Ret
  end;
  Auto.

(* -------------------------------------------------------------------------- *)
(* If the branch guard in [if _ then _ else _] can be resolved, we can decide
   which branch to take. *)
Ltac IfThenElse :=
  match goal with
  | |- envs_entails _ (ewp_def _ (if ?b then _ else _) _ _) =>
      try (assert (b = false) as ->; first done);
      try (assert (b = true) as ->; first done)
  end.

(* -------------------------------------------------------------------------- *)

(* Store-related tactics. *)

Ltac Alloc l H :=
  iApply ewp_alloc; iNext; iIntros (l) H.
Ltac Load H :=
  iApply (ewp_load with H); iNext; iIntros H.
Ltac Store H :=
  iApply (ewp_store with H); iNext; iIntros H.

(* -------------------------------------------------------------------------- *)

(* Apply a [ewp] tactic; maybe we want to add in more checks or normalization
  here *)
Tactic Notation "ewp:" tactic(H) := try H.

(* -------------------------------------------------------------------------- *)

(** *Automation *)
(* Extending the [by] and [done] tactics to solve trivial things in proof mode *)

(* Useful for goals of the shape (⊢ ∀ (e : void), _), _.) which come up when
  reasoning about exceptional continuations *)
Global Hint Extern 0 (envs_entails _ (bi_forall (fun _ : void => _))) => iIntros (?)
; try done : core.

(* Apply general tactics *)
Global Hint Extern 0 (envs_entails _ (ewp_def _ (ret _) _ _)) => ewp: Ret : core.

Notation "OCAML⟦ x ⟧" := (eval.E.eval (deco x _)).

(* -------------------------------------------------------------------------- *)

(** *Fetching specifications of functions*)

(* Returns [spec] for the first occurrence of [(name, spec)] in [specs] *)
Ltac spec_of_name specs name :=
  match specs with
  | (name, ?spec) :: _ => constr:(spec)
  | _ :: ?l => spec_of_name l name
  end.

(* From [env_has_pspecs Λ η], add to Coq hypotheses [lookup_name η x = ret v]
   and the corresponding specification for [x] *)
Tactic Notation "get_spec" constr(name) "as" simple_intropattern(Hv) :=
  match goal with
    He : env_has_pspecs ?specs ?η |- _ =>
      let spec := spec_of_name specs name in
      edestruct (env_has_pspecs_find name spec He) as Hv;
      [ repeat first [ left; reflexivity | right ] (* solving List.In *)
      | ]
  end.

(** *Set postcondition *)

(* Force a postcondition, for example when the postcondition is an evar and one
   wants to perform an induction *)
Tactic Notation "set_postcondition" uconstr(φ) :=
  match goal with
  | |- envs_entails _ (ewp_def ?E ?m ?Ψ ?Φ) => assert (Φ = φ) as -> by reflexivity
  end.

(* -------------------------------------------------------------------------- *)

(** *Proving Handlers and Matches *)

(* Proving that a handler satisfies its specification involves proving
   the effectful case and the return/exceptional case. *)

Ltac prove_handler_spec := rewrite deep_handler_spec_unfold; iSplit.

(* Proving an [EMatch] expression boils down to proving a handler where
   the effectful case is trivial. *)

Ltac prove_match0_spec spec :=
  iApply ewp_EMatch;
  iApply (ewp_deep_handler _ _ spec);
  [ |
    prove_handler_spec;
    [
    | let Hf := iFresh in
      iIntros (??) Hf;
        by iPoseProof (upcl_bottom with Hf) as "?" ]
  ].

Ltac prove_match :=
  iApply ewp_EMatch;
  iApply ewp_deep_handler;
  [ |
    prove_handler_spec;
    [
    | let Hf := iFresh in
      iIntros (??) Hf;
        by iPoseProof (upcl_bottom with Hf) as "?" ]
  ].

Ltac prove_simple_match :=
  iApply ewp_EMatch;
  iApply (ewp_deep_handler _ _ (ieq ?[y]));
  [ |
    prove_handler_spec;
    [
    | let Hf := iFresh in
      iIntros (??) Hf;
        by iPoseProof (upcl_bottom with Hf) as "?" ];
    iIntros (?) "->"
  ].


Tactic Notation "prove_match" "with" constr(spec) := prove_match0_spec spec.


(* -------------------------------------------------------------------------- *)

(** *Entering and Skipping Handler Branches *)

(* Takes an iris environment and returns an ltac list containing the
   idents present in the environment. *)

Ltac2 rec to_ident_list (env : constr) (acc : constr list) :=
  lazy_match! env with
  | environments.Enil => acc
  | environments.Esnoc ?env ?h _ =>
      to_ident_list env (h :: acc)
  end.

Ltac2 all_intuitionistic_hyps () :=
  let env := iris_env () in
  lazy_match! env with
  | environments.Envs ?intuitionistic_env _ _ =>
      to_ident_list intuitionistic_env []
  end.

Ltac2 all_spatial_hyps () :=
  let env := iris_env () in
  lazy_match! env with
  | environments.Envs _ ?spatial_env _ =>
      to_ident_list spatial_env []
  end.

(* [conj_hyps] makes a single conjunction from list of iris hypotheses.
   The new conjunction has the name of the head of the original list. *)

Ltac2 rec conj_hyps (hyps : constr list) :=
  match hyps with
  | [] | [_] => ()
  | h1 :: (h2 :: hyps) =>
      ltac1:(h1 h2 |-
      let h := iFresh in
      iPoseProof (bi_sep_intro) as h;
      iSpecialize (h with h1);
      iSpecialize (h with h2);
      iRename h into h1) (Ltac1.of_constr h1) (Ltac1.of_constr h2);
      conj_hyps (h1 :: hyps)
  end.

(* Given a list of hypotheses that has been turned into a single
   conjuction, [unconj_hyps] reestablishes the original hypotheses. *)

Ltac2 rec unconj_hyps_aux (hyp_name : constr) (hyps : constr list) :=
  match hyps with
  | [] | [_] => ()
  | h1 :: t =>
      ltac1:(h1 hyp_name |-
      _iDestruct0 hyp_name
        (intro_patterns.IList [[intro_patterns.IIdent hyp_name;
                                intro_patterns.IIdent h1]]))
              (Ltac1.of_constr h1) (Ltac1.of_constr hyp_name);
      unconj_hyps_aux hyp_name t
  end.

Ltac2 unconj_hyps (hyps : constr list) :=
  match hyps with | [] => () | hyp_name :: _ =>
  let hyps := List.rev hyps in
  unconj_hyps_aux hyp_name hyps
  end.

(* [revert_intuitionistic] takes a list of persisent (intuitionistic)
   hypotheses and turns them into hypotheses of the form ["H" : □ P]. *)

Ltac2 rec revert_intuitionistic (hyps : constr list) :=
  match hyps with
  | [] => ()
  | h :: t =>
      iRevert $h; iIntros $h; revert_intuitionistic t
  end.

(* [unrevert_intuitionistic] takes a list of hypotheses of the form
   ["H" : □ P] and (re)introduces them into the intuitionistic
   environment. *)

Ltac2 rec unrevert_intuitionistic (hyps : constr list) :=
  match hyps with
  | [] => ()
  | h :: t =>
      iRevert $h;
      ltac1:(h |- _iIntros0 (intro_patterns.IIntuitionistic (intro_patterns.IIdent h)))
      (Ltac1.of_constr h);
      unrevert_intuitionistic t
  end.

(* Given a goal of the form [(□ H1 ∗ ⋯ ∗ □ Hn) ∗ (P1 ∗ ⋯ ∗ Pm) -∗ G],
   a list of the persistent hypotheses [H1, ⋯, Hn], and a list of the
   spatial hypotheses [P1, ⋯, Pm], introduce the hypotheses. *)

Ltac2 reintroduce_env (intuitionistic_hyps : constr list) (spatial_hyps : constr list) :=
  match intuitionistic_hyps with
  | h1 :: _ =>
      iIntros $h1;
      match spatial_hyps with
      | h2 :: _ => unconj_hyps [h1; h2]
      | _ => ()
      end
  | _ =>
      match spatial_hyps with
      | h2 :: _ =>
          iIntros $h2
      | _ => ()
      end
  end;
  unconj_hyps intuitionistic_hyps;
  unrevert_intuitionistic intuitionistic_hyps;
  unconj_hyps spatial_hyps.

Ltac2 do_iintros () :=
  try (iModIntro);
  let igoal := iris_goal () in
  lazy_match! igoal with
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
  let intuitionistic_hyps := all_intuitionistic_hyps () in
  let spatial_hyps := all_spatial_hyps () in
  conj_hyps spatial_hyps;
  revert_intuitionistic intuitionistic_hyps;
  conj_hyps intuitionistic_hyps;
  match intuitionistic_hyps with
  | h1 :: _ =>
      match spatial_hyps with
      | h2 :: _ => conj_hyps [h1; h2]
      | _ => ()
      end
  | _ => ()
  end;
  match intuitionistic_hyps with
  | h1 :: _ =>
      iApply (deep_handle_cons with $h1)
  | _ => match spatial_hyps with
        | h2 :: _ => iApply (deep_handle_cons with $h2)
        | _ => iApply deep_handle_cons_no_resources
        end
  end;
  Control.focus 1 1 (fun _ => iPureIntro;
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
  all (fun _ => reintroduce_env intuitionistic_hyps spatial_hyps);
  last (do_iintros).


Ltac2 Notation "next_branch" := apply_deep_handle_cons ().
Tactic Notation "next_branch" := ltac2:(next_branch).
