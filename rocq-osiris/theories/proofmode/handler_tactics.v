From iris.proofmode Require Import proofmode environments ltac_tactics.

From osiris.lang Require Import lang.

From osiris.program_logic Require Import program_logic osiris_utils.
Require Import pure_tactics.

From osiris.utils Require Import tactics.

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

From Ltac2 Require Import Ltac2 Printf.


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
         When [Hη] is a concrete equality [λ η', η' = δ] (the no-guard case,
         e.g. built-in patterns), rewrite with it.  When [Hη] is still an evar
         (unreachable branch), close via [False].  Otherwise [Hη] is a guarded
         postcondition [λ η', ∃ …, c = … ∧ η' = δ] produced by [close_success]
         for a constructor pattern: leave the body goal for the user to
         introduce with their own pattern (e.g. [iIntros (η') "(%r & %Hc & ->)"]),
         so the matched-constructor equation is available in the branch body. *)
      Control.plus
        (fun _ => ltac1:(iIntros (? ->)))
        (fun _ => Control.plus
                    (* Genuine unreachable branch: [iIntros (? [])] closes it.
                       Gated by [complete] so it does *not* fire on a guarded
                       postcondition (where it would introduce without closing). *)
                    (fun _ => complete (fun _ => ltac1:(iIntros (? []))))
                    (fun _ => ()))
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

(* -------------------------------------------------------------------------- *)

(** *Closing a match-success postcondition while preserving the guard *)

(* When [apply_deep_handle_cons] drives the [cpattern]/[pattern] machinery on
   an Iris match, the per-branch success postcondition [Hη : env → Prop] is an
   evar threaded unchanged from [deep_handle_cons] down to the matching leaf,
   where it surfaces as a goal [?Hη δ] ([δ] the matched environment).

   The naive resolution [apply eq_refl] pins [?Hη := λ η', η' = δ].  That is
   correct only for patterns that introduce no information: for a constructor
   pattern (via a user [pattern_hook] such as [Root _ | Link _]), the matching
   leaves hypotheses in context — the bound variables and a guard equation
   [c = Ctor …] — and pinning [?Hη] to a bare environment equality *drops the
   guard*, leaving the branch body unconstrained by the matched case (and thus
   unsound to rely on).

   [close_success before] fixes this.  Given [before], the identifiers present
   *before* matching began, it collects the hypotheses introduced during
   matching ([delta]) and instantiates [?Hη] to the existential closure
     [λ η', ∃ <delta vars>, <delta guards> ∧ η' = δ],
   so the branch body goal becomes [∀ η', ⌜∃ …, c = Ctor … ∧ η' = δ⌝ -∗ imp …]
   and genuinely carries the matched-constructor equation.  When [delta] is
   empty (built-in patterns) this degenerates to [λ η', η' = δ], reproducing
   the old [apply eq_refl] behaviour exactly. *)

(* [subst_var id t c] replaces every occurrence of the local variable [id] in
   [c] by [t].  [t] is atomic (a variable), so no de Bruijn lifting is needed. *)
Ltac2 rec subst_var (id : ident) (t : constr) (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var v => if Ident.equal v id then t else c
  | _ => Constr.Unsafe.map (subst_var id t) c
  end.

Ltac2 is_prop (ty : constr) : bool := Constr.equal (Constr.type ty) constr:(Prop).

(* [occurs id c] holds when the local variable [id] appears in [c].  Tested by
   substituting [id] for a sentinel and checking whether [c] changed. *)
Ltac2 occurs (id : ident) (c : constr) : bool :=
  let sentinel := Constr.Unsafe.make (Constr.Unsafe.Var @osiris_occ_sentinel) in
  Bool.neg (Constr.equal c (subst_var id sentinel c)).

(* [build_closure delta seed] builds, in the current context, the body
   [∃ <delta vars>, <delta guards> ∧ seed], where [delta] is the outer-first
   list of [(ident, type)] introduced during matching: a [Prop]-typed entry
   becomes a conjunct, any other entry becomes an existential binder (its
   ambient occurrences in the remaining entries and in [seed] are abstracted
   into the fresh binder via [subst_var]). *)
Ltac2 rec build_closure (delta : (ident * constr) list) (seed : constr) : constr :=
  match delta with
  | [] => seed
  | p :: rest =>
      let (id, ty) := p in
      if is_prop ty then
        let rt := build_closure rest seed in constr:($ty /\ $rt)
      else
        let fid := Fresh.in_goal id in
        let fvar := Constr.Unsafe.make (Constr.Unsafe.Var fid) in
        let rest := List.map (fun q => let (i, t) := q in (i, subst_var id fvar t)) rest in
        let seed := subst_var id fvar seed in
        let lam := Constr.in_context fid ty
                     (fun () => let rt := build_closure rest seed in exact $rt) in
        constr:(@ex $ty $lam)
  end.

Ltac2 hyp_ids () : ident list :=
  List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()).

(* Drop later [Prop]-typed entries whose type already appears: [do_intros]
   runs [inversion] on the guard equation, which leaves a syntactic duplicate
   of the guard in context — we only want one copy of each guard as a conjunct. *)
Ltac2 rec dedup_props (seen : constr list) (delta : (ident * constr) list)
  : (ident * constr) list :=
  match delta with
  | [] => []
  | p :: rest =>
      let (id, ty) := p in
      if is_prop ty then
        if List.exist (fun t => Constr.equal t ty) seen
        then dedup_props seen rest
        else p :: dedup_props (ty :: seen) rest
      else p :: dedup_props seen rest
  end.

(* [relevant_delta delta d] selects, from the matching-introduced hypotheses
   [delta], exactly those that carry useful information about the matched value:
   - a [Prop] guard is kept iff it mentions a matching-introduced *variable*
     (this is what distinguishes a constructor guard [c = Root r] from a benign
     side condition like [1 = 1] that built-in patterns leave behind);
   - a variable is kept iff it is mentioned by the matched environment [d] or by
     a kept guard (so the resulting existential closure is well-scoped).
   When nothing is relevant (built-in patterns), the result is empty and the
   closure degenerates to [λ η', η' = d]. *)
Ltac2 relevant_delta (delta : (ident * constr) list) (d : constr)
  : (ident * constr) list :=
  let vars := List.map (fun q => let (i, _) := q in i)
                (List.filter (fun q => let (_, ty) := q in Bool.neg (is_prop ty)) delta) in
  let guard_mentions := fun ty => List.exist (fun v => occurs v ty) vars in
  let mguards := List.filter
                   (fun q => let (_, ty) := q in Bool.and (is_prop ty) (guard_mentions ty))
                   delta in
  let needed := fun v =>
    Bool.or (occurs v d)
            (List.exist (fun q => let (_, gty) := q in occurs v gty) mguards) in
  List.filter
    (fun q => let (id, ty) := q in
              if is_prop ty then guard_mentions ty
              else needed id)
    delta.

Ltac2 close_success (before : ident list) : unit :=
  let delta :=
    dedup_props []
      (List.map (fun h => let (id, _, ty) := h in (id, ty))
        (List.filter
           (fun h => let (id, _, _) := h in
                     Bool.neg (List.mem Ident.equal id before))
           (Control.hyps ()))) in
  lazy_match! goal with
  | [ |- ?h ?d ] =>
      if Constr.is_evar h then
        let delta := relevant_delta delta d in
        let efresh := Fresh.in_goal @η in
        let body := Constr.in_context efresh constr:(env)
          (fun () =>
             let ev := Constr.Unsafe.make (Constr.Unsafe.Var efresh) in
             let b := build_closure delta constr:($ev = $d) in
             exact $b) in
        unify $h $body;
        ltac1:(repeat eexists; repeat split; try eassumption; try reflexivity)
      else ()
  | [ |- _ ] => ()
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
       (* Snapshot the context *before* matching, so [close_success] can later
          tell which hypotheses (bound variables, guard equations) the matching
          introduced. *)
       let before := hyp_ids () in
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
                            matched environment.  [close_success] instantiates
                            [?Hη] to the existential closure of the hypotheses
                            introduced since [before], so the continuation's match
                            case becomes [∀ η', ⌜∃ …, c = Ctor … ∧ η' = δ⌝ -∗ imp …]
                            (degenerating to [λ η', η' = δ] when matching
                            introduced nothing).  If this fails it is skipped. *)
                         Control.plus
                           (fun _ => close_success before)
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

(* [imp_branches] processes all branches of an [imp (eval_branches η o bs)]
   goal, creating one Iris subgoal per branch — the analogue of [pure_match]
   for the Iris world.

   For each branch [Branch cp e] in [bs] it applies [next_branch], which:
     - resolves the [cpattern] and [iSplit]s into the match/no-match pair;
     - auto-closes no-match goals whose postcondition is provably [False];
     - leaves the branch body [imp (eval η' e) ...] as an open subgoal.

   Recursion terminates when [next_branch] fails (either the branch list is
   exhausted or the current goal is not an [eval_branches] goal). *)

Ltac2 rec imp_branches0 () :=
  Control.plus
    (fun _ =>
       apply_deep_handle_cons ();
       try (last (fun _ => imp_branches0 ())))
    (fun _ => ()).

Ltac2 Notation "imp_branches" := imp_branches0 ().
Tactic Notation "imp_branches" := ltac2:(imp_branches0 ()).

(* -------------------------------------------------------------------------- *)

(** *Match *)

(* [imp_match] applies the [imp_EMatch] rule to a goal of the form
   [imp eval η (EMatch e bs) ...].  It dispatches two subgoals:
     1. the scrutinee expression [imp eval η e {{ Φ' }}], which [imp_step]
        is tried on automatically;
     2. the eval_branches continuation, where [simple_intros] peels off the
        [∀ a, Φ' a -∗ ▷] prefix and then [imp_branches] automatically
        processes all pattern branches.
   Optionally, the intermediate type [A'] of the scrutinee can be given as
   an argument to fix the [Encode A'] instance.  If omitted, Rocq leaves it
   as an evar to be resolved from the scrutinee goal. *)

From osiris.proofmode Require Import imp_tactics.

Ltac2 imp_match_tac (a' : constr option) (selpat : constr option) :=
  let e := get_expr () in
  lazy_match! eval hnf in $e with
  | EMatch _ _ =>
      let specialized_match :=
        match a' with
        | Some a => open_constr:(imp_EMatch (A':=$a))
        | None => 'imp_EMatch
        end
      in
      (match selpat with
       | None => iApply $specialized_match
       | Some sel => iApply ($specialized_match with $sel)
       end) >
        [ try (imp_step0 None) | simple_intros (); try (imp_branches0 ()) ]
  | _ =>
      Control.zero (Tactic_failure
        (Some (fprintf "[imp_match] Expected EMatch expression, got %t" e)))
  end.

Ltac2 Notation "imp_match" a'(constr) := imp_match_tac (Some a') None.
Ltac2 Notation "imp_match" := imp_match_tac None None.
Ltac2 Notation "imp_match" a'(constr) "with" sel(constr) :=
  imp_match_tac (Some a') (Some sel).
Ltac2 Notation "imp_match" "with" sel(constr) :=
  imp_match_tac None (Some sel).

Tactic Notation "imp_match" constr(a') :=
  let tac := ltac2:(a' |- imp_match_tac (Ltac1.to_constr a') None) in
  tac a'.
Tactic Notation "imp_match" := ltac2:(imp_match_tac None None).
Tactic Notation "imp_match" constr(a') "with" constr(sel) :=
  let tac := ltac2:(a' sel |-
                      imp_match_tac (Ltac1.to_constr a') (Ltac1.to_constr sel)) in
  tac a' sel.
Tactic Notation "imp_match" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_match_tac None (Ltac1.to_constr sel)) in
  tac sel.
