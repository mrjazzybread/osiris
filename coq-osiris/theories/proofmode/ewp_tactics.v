From iris.proofmode Require Import base proofmode classes environments.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import simp_tactics specifications.

(** *Utility *)

Create HintDb osiris.

(* Some hints used for resolving [repr] expressions *)
Global Hint Rewrite eq_repr_repr sub_repr_repr mul_repr_repr: osiris.
Global Hint Extern 1 (representable _) => representable : osiris.
Global Hint Unfold val_as_int : osiris.

(** *"WP" tactics

  These tactics operate on [WP] goals are Hoare-style;

  All tactics that are not "Hoare-style" are internal and should not be exposed
  to the user. *)

(** *General tactics *)
(* Start proof mode. *)
Ltac Start_proof := iStartProof.

(* Try to simplify the goal using the [simp] relation *)
Ltac Simp :=
  iApply ewp_simp; first try solve [simp].

(* Hoare-style rules that correspond to [rule] lemmas *)
Ltac Try := iApply ewp_try.

Ltac Ret := repeat iApply ewp_value.

Ltac Throw := iApply ewp_throw.

Ltac Par :=
  lazymatch goal with
  | |- envs_entails _ (ewp_def _ (Par (ret _) (ret _) _) _ _) =>
      iApply ewp_simp; first simp
  | |- envs_entails _ (ewp_def _ (Par _ (Ret _) _) _ _) =>
      iApply ewp_simp; first simp
  | |- envs_entails _ (ewp_def _ (Par (ret _) _ _) _ _) =>
      iApply ewp_simp; first simp
  | |- envs_entails _ (ewp_def _ (Par _ _ _) _ _) =>
      iApply ewp_Par
  | _ => fail "The goal must be a par to apply [ewp_par]."
  end; try done.

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
Ltac Bind := first [ iApply ewp_fmap | iApply ewp_bind ].

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

Notation "OCAML⟦ x ⟧" := (eval.eval (deco x _)).

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
