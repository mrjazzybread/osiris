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
From osiris.proofmode Require Import simp_tactics specifications pat expr_rules.

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


(* -------------------------------------------------------------------------- *)

(** *Calling AnonFuns *)

(* [ewp_call_anonfun] expects a goal of the form
          [ EWP call_anonfun η (λ args, body) (args ++ [x]) {{ Q }} ]
      and produces a goal of the form
          [ EWP call (VClo (args ++ η) body) x {{ Q }} ] *)
Ltac ewp_call_anonfun :=
  (* Unfold [call_anonfun], and get a tower of binds. *)
  rewrite /call_anonfun; simpl; rewrite ?bind_bind;
  (* Unfold [eval_anonfun]. *)
  rewrite /eval_anonfun;
  (* Simplify the tower of binds,
        this should elaborate a closure capturing all arguments.  *)
  repeat (iApply ewp_bind; Simp; Ret);
  simpl.

(* Non-recursive call. *)
Ltac Call :=
  match goal with
  | |- envs_entails _ (ewp_def _ (call_anonfun _ _ _) _ _) =>
      ewp_call_anonfun; iApply ewp_call_nonrec
  end.


(* -------------------------------------------------------------------------- *)

(** *Entering and Skipping Handler Branches *)

From Ltac2 Require Import Ltac2.

Ltac2 get_outcome_from_match (e : constr) : constr :=
  let o :=
    lazy_match! e with
    | (deep_eval_match _ _ ?o) => o
    | (shallow_eval_match _ _ _ ?o) => o
    | (eval_match _ _ ?o) => o
    | _ =>
        Control.throw
          (Tactic_failure
             (Some
                (Message.of_string "Expected a match")))
    end
  in
  (* We evaluate to get rid of coercions, such as [outcome2_inject]. *)
  Std.eval_hnf o.

Ltac2 trivial_post_instantiation (e : constr) : constr :=
  lazy_match! (get_outcome_from_match e) with
  | O3Ret _ => constr:(True)
  | O3Throw _ => constr:(True)
  | O3Perform _ _ => constr:(True \/ True)
  end.

Ltac2 skip_matching_branch (e : constr) :=
  let φ2 := trivial_post_instantiation e in
  ltac1:(φ2 |- iApply (deep_handle_cons _ _ _ _ _ _ _ _ (λ _, False) φ2);
         [ specify_cpattern; pattern_match
         | iIntros (? [])
         | iIntros (_) ]) (Ltac1.of_constr φ2).

Ltac2 skip_non_matching_branch () :=
  ltac1:(iApply deep_handle_cons_skip) > [ reflexivity | ].

Ltac2 get_expr_from_ewp () :=
  match! goal with
  | [ |- envs_entails _ ?e ] =>
      let rec strip_laters e :=
        lazy_match! e with
        | bi_later ?e => strip_laters e
        | _ => e
        end
      in
      lazy_match! strip_laters e with
      | ewp_def _ ?e _ _ => e
      end
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [EWP m @ E <|Ψ|> {{ Q}}]")))
  end.

Ltac2 skip_branch () :=
  let e := get_expr_from_ewp () in
  Control.plus
    (* Try to skip a branch that doesn't match the pattern type. *)
    (fun _ => skip_non_matching_branch ())
    (* Enter the branch and *)
    (fun _ => skip_matching_branch e).

Ltac2 iapply (lem : constr) (sel : constr option) :=
  match sel with
  | None => ltac1:(lem |- iApply lem) (Ltac1.of_constr lem)
  | Some sel =>
      ltac1:(lem sel |- iApply (lem with sel))
              (Ltac1.of_constr lem) (Ltac1.of_constr sel)
  end.

Ltac2 Notation "iApply" "(" lem(constr) "with" sel(constr) ")" := iapply lem (Some sel).
Ltac2 Notation "iApply" lem(constr) := iapply lem None.

Ltac2 enter_branch0 (intro_pat : constr option) :=
  match intro_pat with
  | None => iApply deep_handle_cons
  | Some intro_pat => iApply (deep_handle_cons with $intro_pat)
  end >
    [ ltac1:(specify_cpattern; pattern_match); try (apply eq_refl)
    | ltac1:(iIntros (? ->) || iIntros (? <-))
    | ltac1:(let F := fresh in iIntros (F); try tauto) ].

Ltac2 Notation "enter_branch" "with" intro_pat(constr) := enter_branch0 (Some intro_pat).
Ltac2 Notation "enter_branch" := enter_branch0 None.

(* Try to reduce a [match] expression by skipping all branches seen and then
     entering a branch on match. *)
Ltac red_match := repeat (ltac2:(skip_branch ()); [ idtac ]);
                  ltac2:(enter_branch with "[-]").
