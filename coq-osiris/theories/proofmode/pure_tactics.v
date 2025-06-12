From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.

Local Ltac pat_PTuple :=
  first [
      eapply pat_PTuple; first solve [ encode ]
    | rewrite 1 ?encode_encode'; simpl -[eval];
      eapply pat_PTuple_val ].

From Ltac2 Require Ltac2.
Import Ltac2.

(* -------------------------------------------------------------------------- *)

(* This file contains tactics intended for use during hoare-style proofs of pure
   programs. These range from symbolic execution to tactics designed to aid
   the application of single lemmas. *)

(* NOTE: The user-facing tactics are analogous to the user facing rules in
   [program_logic/pure/expr_rules].

   To avoid confusion, the [Local] tag controls the visibility of tactics. *)

(* -------------------------------------------------------------------------- *)

(* [specify_cpattern] takes a goal of the form [cpattern η cp o3 φ ψ]
   and turns it into [n] goals of the form [pattern η p v φ ψ],
   returning [n]. *)

Ltac2 rec specify_cpattern () : int :=
  lazy_match! goal with
  | [ |- cpattern _ _ ?cp ?o _ _ ] =>
      (* We simplify terms because of things like coercions. *)
      let cp := Std.eval_hnf cp in
      let o := Std.eval_hnf o in
      match Constr.Unsafe.kind o with
      | Constr.Unsafe.App _ _ =>
          (* If we know what kind of outcome [o] is. *)
          lazy_match! '($cp, $o) with
          | (CVal _, O3Ret _) =>
              apply cpat_CVal; 1
          | (CExc _, O3Throw _) =>
              apply cpat_CExc; 1
          | (CEff _ _, O3Perform _ _) =>
              apply cpat_CEff; 1
          | (COr _ _, _) =>
              eapply cpat_COr;
              let n := Control.focus 1 1 specify_cpattern in
              let m := Control.focus (Int.add n 1) (Int.add n 1)
                         (fun () =>
                            let match_hyp := Fresh.in_goal ident:(match_hyp) in
                            intros $match_hyp;
                            specify_cpattern ())
              in
              Int.add n m
          | _ =>
              eapply cpat_mismatch > [ cbn; reflexivity | ];
              if Constr.is_evar (Control.goal ()) then
                apply I; 0
              else
                1
          end
      | _ =>
          (* If [o] is not a concrete outcome. *)
          lazy_match! cp with
          | CVal _ => eapply cpat_CVal_abst; intros ??; 1
          | CExc _ => eapply cpat_CExc_abst; intros ??; 1
          | CEff _ _ => Control.plus
                         (fun _ => apply cpat_CEff_impossible; 0)
                         (fun _ => eapply cpat_CEff_abst; intros ???; 1)
          | COr _ _ =>
              eapply cpat_COr;
              let n := Control.focus 1 1 specify_cpattern in
              let m := Control.focus (Int.add n 1) (Int.add n 1) specify_cpattern in
              Int.add n m
          end

      end
  end.

Local Tactic Notation "specify_cpattern" := ltac2:(let _ := specify_cpattern () in ()).

(* -------------------------------------------------------------------------- *)

(* Custom tauto tactic. *)

Local Ltac2 tauto0 () := ltac1:(tauto).
Ltac2 Notation tauto := tauto0 ().

(* -------------------------------------------------------------------------- *)

(* Utility lemmas to help prune pattern no_match hypotheses. *)

Local Lemma false_or_r P :
  P \/ False <-> P.
Proof. tauto. Qed.

Local Lemma false_or_l P :
  False \/ P <-> P.
Proof. tauto. Qed.

Local Lemma true_or_r P :
  P \/ True <-> True.
Proof. tauto. Qed.

Local Lemma true_or_l P :
  True \/ P <-> True.
Proof. tauto. Qed.

Local Lemma false_and_r P :
  P /\ False <-> False.
Proof. tauto. Qed.

Local Lemma false_and_l P :
  False /\ P <-> False.
Proof. tauto. Qed.

Local Lemma true_and_r P :
  P /\ True <-> P.
Proof. tauto. Qed.

Local Lemma true_and_l P :
  True /\ P <-> P.
Proof. tauto. Qed.


(* In hypotheses [hyps], rewrite (left-to-right) using the equation defined in
   [rw].

    H1 : A
    H2 : B > A
    EQ : A = C
    ---------
    ...

   [rewrite_in_hyps EQ [H1; H2]] will result in:

    H1 : C
    H2 : B > C
    EQ : A = C
    ---------
    ...

    LATER: Factor this out as a general utility lemma. *)

Local Ltac2 rewrite_in_hyps (rw : constr) (hyps : ident list) :=
  let hyp_clauses :=
    List.map (fun id => (id, Std.AllOccurrences, Std.InHyp)) hyps
  in
  let clause :=
    { Std.on_hyps := Some hyp_clauses;
      Std.on_concl := Std.NoOccurrences }
  in
  let rw :=
    { Std.rew_orient := Some Std.LTR;
      Std.rew_repeat := Std.RepeatPlus;
      Std.rew_equatn := fun _ => (rw, Std.NoBindings) }
  in
  Std.rewrite false [rw] clause None.

(* Normalize (i.e. remove extraneous ⊥ and ⊤ appearances, or reduce to ⊥ or ⊤
   when possible) hypotheses in [hyps]. *)

Local Ltac2 normalize_hyps (hyps : ident list) :=
  let lemma_list :=
    [ 'false_or_r;
      'false_or_l;
      'true_or_r;
      'true_or_l;
      'false_and_r;
      'false_and_l;
      'true_and_r;
      'true_and_l ]
  in
  let thunk_list :=
    List.map (fun l _ => rewrite_in_hyps l hyps) lemma_list
  in
  repeat (first0 thunk_list).

(* Normalize hypothesis [h]. *)

Local Ltac2 normalize_hyp (h : ident) :=
  normalize_hyps [h].

(* [pattern_hook] is an extensible lemma that the users will add their custom
   patterns to.

   This is useful when a user defines their custom ADT with certain destruct
   patterns. (Used in [pure_match].) *)
Ltac pattern_hook := fail.

(* [pattern_match] expects a goal in the form of a [pattern] or [patterns] judgement.
   It tries to apply all know pattern matching rules. We use [pattern_hook] to
   make this tactic extensible (see its redefinition in examples/splay.v). *)

Ltac2 rec solve_lookup_name () :=
  lazy_match! goal with
  (* If a hypothesis matches the lookup we are trying to do, use it. *)
  | [ h_ident : lookup_name ?η ?c = _ |- lookup_name ?η ?c = _ ] =>
      let h := Control.hyp h_ident in
      rewrite -> $h
  (* Otherwise just try and compute the lookup. *)
  | [ |- lookup_name _ _ = _ ] =>
      progress (simpl -[eval])
  end;
  (* We now have two cases:
     - Using a hypothesis or simplification has produced a goal of
       the form [ret v = ret v].
     - Using a hypothesis has led us to a new lookup *)
  match! goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  end.

(* LATER: Move? *)

Local Lemma rewrite_bind {A B E} (m : micro A E) (f : A -> micro B E) a :
  m = ret a ->
  bind m f = f a.
Proof. intros ->; reflexivity. Qed.

Local Ltac2 rec solve_lookup_path () :=
  simpl;
  lazy_match! goal with
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  | [ |- bind (lookup_name ?η ?c) _ = _ ] =>
      erewrite -> (rewrite_bind (lookup_name $η $c)) >
        [ solve_lookup_name () | solve_lookup_path () ]
  | [ |- ret _ = ret _ ] => reflexivity
  end.

Local Ltac2 rec is_pattern (c : constr) :=
  lazy_match! c with
  | pattern _ _ _ _ _ _  => true
  | patterns _ _ _ _ _ _ => true
  | _ => false
  end.

Local Ltac2 constr_at_ident (h : ident) : constr :=
  let (_, _, x) :=
    List.find (fun (id, _, _) => Ident.equal h id) (Control.hyps ())
  in
  x.

Local Ltac2 destruct_as (h : ident) (p : Std.or_and_intro_pattern) :=
  let cl :=
        { Std.indcl_arg := Std.ElimOnIdent h;
          Std.indcl_eqn := None;
          Std.indcl_as := Some p;
          Std.indcl_in := None }
  in
  Std.destruct false [cl] None.

Local Ltac2 rec get_arity (c : constr) :=
  match! c with
  | ?a _ => (Int.add 1 (get_arity a))
  | _ => 0
  end.

Local Ltac2 rec get_constructor (c : constr) :=
  match! c with
  | ?a _ => get_constructor a
  | _ => match Constr.Unsafe.kind c with
        | Constr.Unsafe.Constructor _ _ => Some c
        | _ => None
        end
  end.

Local Ltac2 rec destruct_hyp (h : ident) : unit :=
  normalize_hyp h;
  let x := constr_at_ident h in
  lazy_match! x with
  | exists x, _ =>
      (* pat := [ ? h ] *)
      let pat :=
        Std.IntroAndPattern
          [Std.IntroNaming Std.IntroAnonymous;
           Std.IntroNaming (Std.IntroIdentifier h)]
      in
      destruct_as h pat;
      (* Recursive call in case [h] is a nested existential. *)
      destruct_hyp h
  | _ /\ _ =>
      let h2 := Fresh.in_goal h in
      (* pat := [ h h2 ] *)
      let pat :=
        Std.IntroAndPattern
          [ Std.IntroNaming (Std.IntroIdentifier h);
            Std.IntroNaming (Std.IntroIdentifier h2) ]
      in
      destruct_as h pat;
      destruct_hyp h;
      (* We need [Control.enter] in case [destruct_hyp h] solves the goal. *)
      Control.enter (fun _ => destruct_hyp h2)
  | False =>
      destruct_as h (Std.IntroOrPattern [])
  | _ \/ _ =>
      (* We only destruct an [or] pattern if we are able to solve one
         of the two generated subgoals. *)
      Control.plus
        (fun _ =>
           (* pat := [ h | h ] *)
           let pat :=
             Std.IntroOrPattern
               [ [ Std.IntroNaming (Std.IntroIdentifier h) ];
                 [ Std.IntroNaming (Std.IntroIdentifier h) ] ]
           in
           destruct_as h pat;
           (* Solve one of the two subgoals. *)
           Control.plus
             (fun _ => Control.focus 1 1 (fun _ => complete (fun _ => destruct_hyp h)))
             (fun _ => Control.focus 2 2 (fun _ => complete (fun _ => destruct_hyp h)));
           destruct_hyp h)
        (fun _ => ())
  | ?a = ?b =>
      (* If the hypothesis is a tautology, remove it. *)
      if Constr.equal a b then clear h else
        (* If the equality is of the form [c ... = ...] *)
      (if (Int.gt (get_arity a) 0) then
         let hyp := Control.hyp h in
         inversion $hyp
       else ());
      subst;
      try ltac1:(congruence)
  | ?a <> ?b =>
      (* An inequality between two terms with different constructors
         is trivial, so we clear such a hypothesis if we find one. *)
      match get_constructor a, get_constructor b with
      | Some c1, Some c2 =>
          if Bool.neg (Constr.equal c1 c2) then Std.clear [h] else ()
      | _, _ => ()
      end
  | _ => try ltac1:(congruence)
  end.

(* We build our own recursor instead of [List.iter] because we don't
   want to keep iterating after solving the goal. *)

Local Ltac2 destruct_hyps (hs : ident list) :=
  let rec iter :=
    fun f ls =>
      match ls with
      | [] => ()
      | h :: hs =>
          f h; (Control.enter (fun _ => iter f hs))
      end
  in
  iter destruct_hyp hs.

Local Tactic Notation "destruct_hyp" ident(hyp) :=
  let destr_hyp := ltac2:(hyp |-
                            let hyp := Option.get (Ltac1.to_ident hyp) in
                            destruct_hyp hyp)
  in
  destr_hyp hyp.

Local Tactic Notation "destruct_hyps" ident_list(hyps) :=
  let destr_hyps := ltac2:(hyps |-
                             let hyps := Option.get (Ltac1.to_list hyps) in
                             let hyps := List.map (fun hyp => Option.get (Ltac1.to_ident hyp)) hyps in
                             destruct_hyps hyps)
  in
  destr_hyps hyps.

(* -------------------------------------------------------------------------- *)

Local Ltac2 rec do_intros () :=
  lazy_match! goal with
  | [ |- ?h -> ?g ] =>
      (* If [h] is a proposition. *)
      (if Constr.equal (Constr.type h) constr:(Prop) then
         (* Give [h] a nice name. *)
         let match_hyp := Fresh.in_goal ident:(match_hyp) in
         intros $match_hyp;
         (* Try and use the information in [h]. *)
         destruct_hyp match_hyp
       (* If [h] is not a proposition then it is presumably a variable. *)
       else
         intros ?);
      Control.enter do_intros
  | [ |- forall x, _ ] =>
      intros ?; do_intros ()
  | [ |- _ ] => ()
  end.

Local Ltac2 set_postcondition_to_false () :=
  lazy_match! goal with
  | [ |- pattern _ _ _ _ _ (?ψ ?arg) ] =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        unify $ψ (fun (_ : $t) => False)
      else ()
  | [ |- pattern _ _ _ _ _ ?ψ ] =>
      if Constr.is_evar ψ then unify $ψ False else ()
  end.

Local Ltac2 set_postcondition_to_true () :=
  lazy_match! goal with
  | [ |- pattern _ _ _ _ _ (?ψ ?arg) ] =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        unify $ψ (fun (_ : $t) => True)
      else ()
  | [ |- pattern _ _ _ _ _ ?ψ ] =>
      if Constr.is_evar ψ then unify $ψ True else ()
  end.

Local Ltac2 massage_term (c : constr) :=
  lazy_match! c with
  | ?ψ ?arg  =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        let u := open_constr:(fun x => _) in
        unify $ψ $u
      else ()
  | _ => ()
  end.

(* [patterns] expects a goal of the form [patterns ...] and either
   - reduces to a [pattern ...] with [pats_PCons_unary],
   - solves the goal with [pats_PNil]. *)

Local Ltac2 patterns () :=
  lazy_match! goal with
  | [ |- patterns _ _ (_ :: _) _ _ ?ψ ] =>
      (* If [Ψ] is an evar, [pats_PCons_unary] instantiates it as
         [Ψ := ?Ψ1 ∨ ?Ψ2]. Currently (09/2024), the only other case
         is that [Ψ] is already instantiated to [False]. *)
      if (Constr.equal ψ constr:(False)) then
        eapply pats_PCons_unary_false
      else
        eapply pats_PCons_unary
  | [ |- patterns _ _ nil _ _ ?ψ ] =>
      (* If [Ψ] is an evar then we instantiate it to [False], otherwise we
         use [pats_consequence_psi] and the fact that [∀ P, ⊥ -> P]. *)
      if (Constr.is_evar ψ) then
        eapply pats_PNil
      else
        eapply patterns_exn_mono > [ eapply pats_PNil | intros [] ]
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [patterns η δ ps vs φ ψ]")))
  end.


(* [pattern_match_aux] expects a goal of the form [patterns ...] or
   [pattern ...] and progresses by matching the pattern(s) to the
   variable(s). This is done by applying the appropriate lemma for
   each pattern, for example [pat_PInt] if the pattern is a [PInt]. *)

(* If we don't match on any known pattern, we try to use an extensible
   Ltac1 tactic called [pattern_hook].
   This allows users to extend pattern matching to new data structures. *)

Local Ltac2 rec pattern_match_aux () :=
  (* [continue_matching] is used after solving one pattern. It
     introduces new information before deciding whether to continue
     pattern-matching or whether we are done. *)
  let continue_matching :=
    fun _ => do_intros ();
          (* Use [Control.enter] here because [do_intros] may solve the goal. *)
          Control.enter (fun _ =>
          if is_pattern (Control.goal ()) then pattern_match_aux () else ())
  in
  lazy_match! goal with
  | [ |- patterns _ _ _ _ _ _ ] => patterns (); continue_matching ()
  | [ |- pattern _ _ ?p _ _ ?ψ ] =>
      (* [massage_term] is black magic to help Rocq's unification engine. *)
      massage_term ψ;
      match! p with
      | PVar _ =>
          (* We assume that a [PVar] pattern never fails. *)
          set_postcondition_to_false ();
          (* It may be the case that [pat_PVar2] can entirely solve the goal. *)
          Control.plus
            (fun _ => eapply pat_PVar2)
            (fun _ => eapply pat_PVar;
                   continue_matching ())
      | PInt _ =>
          eapply pat_PInt;
          (* First solve the encoding to ensure that all values are instantiated. *)
          Control.focus 3 3 (fun _ => solve [ ltac1:(encode) ]);
          Control.extend [] (fun _ => ltac1:(representable)) [continue_matching]
      | pNil =>
          eapply pat_pNil > [ solve [ ltac1:(encode) ]
                            | continue_matching () ]
      | PConstant "[]" =>
          eapply pat_pNil > [ solve [ ltac1:(encode) ]
                            | continue_matching () ]
      | pCons _ _ =>
          eapply pat_pCons > [ solve [ ltac1:(encode) ]
                             | continue_matching () ]
      | PData "::" _ =>
          eapply pat_pCons > [ solve [ ltac1:(encode) ]
                             | continue_matching () ]
      | PXData _ _ =>
          Control.plus
            (fun _ => eapply pat_PXData_eq > [ solve_lookup_path () | pattern_match_aux () ])
            (fun _ => eapply pat_PXData_neq > [ solve_lookup_path () | auto ])
      | PConstant _ =>
          Control.plus
            (fun _ => eapply pat_PConst_eq; continue_matching ())
            (fun _ => eapply pat_PConst_neq > [ ltac1:(congruence) | try ltac1:(tauto) ])
      | POr _ _ =>
          apply pat_POr > [ pattern_match_aux () | pattern_match_aux () ]
      | PTuple _ =>
          ltac1:(pat_PTuple); continue_matching ()
      | PAlias _ _ =>
          apply pat_PAlias; pattern_match_aux ()
      | PAny =>
          apply pat_PAny; continue_matching ()
      (* If we haven't matched any known pattern, try and use the hook. *)
      | _ =>
          ltac1:(pattern_hook); continue_matching ()
      end
  end.

(* Assuming a goal of the form [⊢ pattern(s) η δ p v ?φ ?ψ], the
   [pattern_match] tactic tries to reduce the goal to [⊢ φ] while
   elaborating the failure postcondition [Ψ]. *)

Ltac2 pattern_match0 () :=
  Control.enter (fun _ =>
  lazy_match! goal with
  | [ |- pattern _ _ ?p (#?x) _ ?ψ ] =>
      rewrite 1 ?encode_encode'; pattern_match_aux ()
  | [ |- pattern _ _ ?p _ _ ?ψ ] => pattern_match_aux ()
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pattern η δ p v φ ψ]")))
  end).

Ltac2 Notation "pattern_match" := pattern_match0 ().
Tactic Notation "pattern_match" := ltac2:(pattern_match).

(* -------------------------------------------------------------------------- *)

(* [resolve_no_match] attempts to prove by contradiction that
   not matching on any branch of a pattern match is impossible.e Its
   tactics implicitly target the "no_match" hypotheses that are
   generated by [pure_match_branches] and instantiated by [pattern_match]. *)

Local Ltac strip_disjunction :=
  match goal with
  | H : _ \/ _ |- _ =>
      destruct H as [ H | H ]; try contradiction
  end.
Local Ltac remove_tauto :=
  lazymatch goal with
  | H : ?x = ?x |- _ => clear H
  | _ => idtac
  end.
Local Ltac subst_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ => subst x
  | _ => idtac
  end.
Local Ltac inject_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ =>
      (injection H; repeat (intros ->) || clear dependent x)
  | _ => idtac
  end.
Local Ltac elim_exists :=
  lazymatch goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  end.
Local Ltac elim_conj :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac resolve_no_match :=
  repeat first
    [ strip_disjunction
    | elim_exists
    | elim_conj
    | congruence
    | remove_tauto
    | subst_eq
    | inject_eq ].

Ltac2 first tac := Control.extend [tac] (fun _ => ()) [].
Ltac2 last tac := Control.extend [] (fun _ => ()) [tac].

(* -------------------------------------------------------------------------- *)

(* [pure_match_branches] expects a goal of the form
   [pure_match _ _ bs _] where [bs] is a list of n branches. It
   successively applies [pure_match_cons], creating n subgoals of the
   form [pattern _ _ _ _ (λ n', pure (eval η' _) ##_ ⊥) _] and one subgoal of
   the form [False]. *)


Ltac2 rec pure_match_branches0 (hyps : ident list) :=
  lazy_match! goal with
  | [ |- branches _ ?o ?bs _ _ ] =>
      (* Match on [bs] to decide whether to apply [pure_match_cons]
         or [pure_match_nil]. *)
      lazy_match! (Std.eval_hnf bs) with
      | _ :: _ =>
          (* [pure_match_cons] produces two subgoals :
             - one of the form [cpattern ...]
             - one of the form [Ψ -> pure_match ...] *)
          eapply branches_cons;
          (* In the first subgoal, apply the [specify_cpattern] tactic
             followed by the [pattern_match] tactic. *)
          Control.focus 1 1
            (fun _ =>
               (* [specify_cpattern ()] introduces m subgoals. *)
               let m := specify_cpattern () in
               if (Int.gt m 0) then
                 Control.focus 1 m pattern_match0
               else ());
          (* In the second subgoal, introduce the new hypothesis [ψ]
             and recursively apply [pure_match_branches0]. *)
          last
            (fun _ =>
               let no_match := Fresh.in_goal @no_match in
               intros $no_match;
               (* Simplify the hypotheses we've generated so far. *)
               destruct_hyps (no_match :: hyps);
               (* Filter to only keep the hypotheses which still exist
                  after simplification. *)
               let remaining_hyps :=
                 List.filter (fun id => Control.plus
                                       (fun _ => let _ := Control.hyp id in true)
                                       (fun _ => false)) (no_match :: hyps)
               in
               (* We use [Control.enter] so the tactic doesn't fail in
                  the case where the goal was solved by the hypothesis
                  simplification. *)
               Control.enter (fun _ => pure_match_branches0 (remaining_hyps)))
      | [] =>
          (* We have to show that every pattern match is exhaustive. *)
          lazy_match! (Std.eval_hnf o) with
          | O3Ret _ =>
              (* If we reach this point, then we can assume that an early
                 use of [destruct_hyps] was not powerful enough to solve
                 this goal. We thus use the more brute-force
                 [resolve_no_match] tactic. *)
              eapply branches_val_nil; ltac1:(resolve_no_match)
          | O3Throw _ =>
              (* If we didn't catch an exception, we propagate it. *)
              eapply branches_exn_nil
          | _ =>
              (* [o] could be abstract, in which case we try to say we have been exhaustive. *)
              ltac1:(resolve_no_match)
          end
      end
  | [ |- ?g ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [branches η o bs φ Ψ]")))
  end.

Ltac2 pure_match0 () := pure_match_branches0 [].

Ltac2 Notation "pure_match" := pure_match0 ().
Tactic Notation "pure_match" := ltac2:(pure_match).

(* Tactics. *)

(* TODO reduce just beta-redexes in the goal (possibly under ∀ and →) *)
Ltac2 beta () := cbn beta.

Goal (forall l : list nat,
         l = [] ->
         (λ (x : bool), negb x = ((λ (x : bool), x) false)) true).
Proof.
  beta (). reflexivity.
Qed.

(* [remove_deco] is used by subsequent tactics when we want to match on an
   expression under a decoration in a goal. *)

Ltac2 notation remove_deco := unfold deco.

(* Remove any local environment definitions. *)

Ltac2 clear_abstracted_env () :=
  (* Iterate over the hypotheses. *)
  List.iter
    (* Take [η] the name of the hyp-name and [ty] its type. *)
    (fun (η, _, ty) =>
       (* Use [Std.eval_vm] in case [ty] is folded as [env]. *)
       match! (Std.eval_vm None ty) with
       (* If [η] is an environment, try substitute it. *)
       | list (string * val) => subst $η
       | _ => ()
       end)
    (Control.hyps ()).

Ltac2 Notation "clear_abstracted_env" := clear_abstracted_env ().
Tactic Notation "clear_abstracted_env" := ltac2:(clear_abstracted_env).

(* [get_env] returns the current environment under which an expression
   is currently being evaluated in [pure] mode. *)

Ltac2 get_env () :=
  lazy_match! goal with
  | [ |- pure (eval ?η _) _ _ ]  => η
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pure (eval η e) φ ψ]")))
  end.

(* [abstract_env] expects a goal of the form [pure (eval η e) ##φ ⊥]. It creates a
   local definition for the environment [η]. *)

Ltac2 abstract_env () :=
  Control.enter
    (fun _ =>
       (* Collapse any previous environment abstraction. *)
       clear_abstracted_env;
       (* Fetch the full environment as a constr [η]. *)
       let η := get_env () in
                   (* Generate a fresh name and use [set] to abstract [η]. *)
       let η0 := Fresh.in_goal @η in
       set ($η) as η0).

Ltac2 Notation "abstract_env" := abstract_env ().
Tactic Notation "abstract_env" := ltac2:(abstract_env).

(* -------------------------------------------------------------------------- *)

 Ltac2 solve_encoding () : unit :=
   Control.plus
     (fun _ =>
        Control.plus
          (fun _ => complete (fun _ => ltac1:(encode)))
          (fun _ => rewrite <- solve_encode_val; reflexivity))
     (fun _ =>
        Control.throw
          (Tactic_failure
             (Some
                (Message.of_string
                   "Was not able to solve encoding")))).

Ltac2 decompose_pure () : (constr * constr) :=
  match! goal with
  | [ |- pure ?m ?φ _ ] => (m, φ)
  | [ |- total ?m ?φ ] => (m, φ)
  end.

Ltac2 get_expr_from_eval (m : constr) :=
  lazy_match! m with
  | eval _ ?e => eval hnf in $e
  | unseal eval.E.eval_aux _ ?e => eval hnf in $e
  | _ =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string
                 "Expected term of the form [eval η e]")))
  end.

(* TODO: Move; utility. Definition by Michael Soegtrop *)

Definition type_of {T : Type} (x : T) := T.

Ltac2 solve_returns () :=
  match! goal with
    | [ |- returns _ _ ] =>
        ltac1:(
          first [ solve [ eauto with pure ] |
          eexists _; split; eauto with pure ])
  end.

Ltac2 match_type (x:constr) (t:constr) :=
  let tx:=eval cbv in (type_of $x) in
  Constr.equal tx t.

(* [pure_ret] expects a goal of the form [pure (ret v) ##φ ⊥]. It applies
   the lemma [pure_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac2 pure_ret0 () :=
  match! goal with
  | [ |- pure_wp (ret ?v) _ _ ] =>
      if match_type v constr:(val) then
        first
          [ eapply pure_ret_eq_val; eauto with encode |
            eapply pure_ret; eauto with encode ]
      else
        eapply pure_ret; eauto with encode
  | [ |- pure (ret ?v) _ _ ] =>
      if match_type v constr:(val) then
        first
          [ eapply pure_ret_eq_val; eauto with encode |
            eapply pure_ret; eauto with encode ]
      else
        eapply pure_ret; eauto with encode
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
            (Some
              (Message.of_string
                  "Was not able to solve encoding")))
  end.

Ltac2 Notation "pure_ret" := Control.enter pure_ret0.
Tactic Notation "pure_ret" := ltac2:(pure_ret).

(* [pure_path] expects a goal of the form [pure (eval η (EPath x)) ##φ ⊥]. It applies
   the lemma [pure_eval_path], asks Coq to compute the lookup in the environment,
   and, assuming that the lookup succeeds, calls pure_ret on the result. *)

Ltac2 pure_path0 () : unit :=
  let (m, φ) := decompose_pure () in
  let e := get_expr_from_eval m in
  match! e with
  | (EPath _) =>
      (* [pure_eval_path : *)
(*           pure (lookup_path η π) ##ψ ⊥ -> pure (eval η (EPath π)) ##ψ ⊥] *)
      eapply pure_eval_path;
      simpl lookup_path;
      lazy_match! goal with
      (* If the lookup has not reduced to a result, try and use a hypothesis. *)
      | [ h_ident : lookup_name ?η ?π = ret _
          |- pure (lookup_name ?η ?π) _ _ ] =>
          let h := Control.hyp h_ident in
          rewrite [$h]; pure_ret
      (* If the lookup has reduced to a result, use [pure_ret]. *)
      | [ |- _] => pure_ret
      end
  end.

Ltac2 Notation "pure_path" := Control.enter pure_path0.
Tactic Notation "pure_path" := ltac2:(pure_path; try reflexivity).

(* [pure_const] expects a goal of the form [pure (eval η (EConstant x)) ##φ ⊥].
   It applies the lemma [pure_eval_const], solves the subgoal [VConstant c = #x],
   and leaves the subgoal [φ x]. *)

Ltac2 pure_const0 () :=
  let (m, φ) := decompose_pure () in
  let e := get_expr_from_eval m in
  match! e with
  | EConstant _ =>
      (* [pure_eval_const : *)
(*           VConstant c = #x -> ψ x -> pure (eval η (EConstant c)) ##ψ ⊥] *)
      eapply pure_eval_const;
      let solve_encoding : unit -> unit :=
        fun _ =>
          match! Constr.type φ with
          | val -> Prop => rewrite <- solve_encode_val; reflexivity
          | _ => solve [ ltac1:(encode) ]
          end
      in
      Control.focus 1 1 solve_encoding
  end.

Ltac2 Notation "pure_const" := Control.enter pure_const0.
Tactic Notation "pure_const" := ltac2:(pure_const).

(* -------------------------------------------------------------------------- *)

Ltac2 get_ref (t : constr) : Std.reference :=
 match Constr.Unsafe.kind t with
 | Constr.Unsafe.Var id => Std.VarRef id
 | Constr.Unsafe.Constant c _ => Std.ConstRef c
 | _ => Control.zero Match_failure
 end.

Ltac2 rec unfold_item (item : constr) : constr :=
  Control.plus
    (fun _ =>
       let ref :=
         match! item with
         | ILet ?bs => get_ref bs
         | ILetRec ?rbs => get_ref rbs
         | IModule ?m ?me => Control.zero Match_failure
         | IOpen ?i => get_ref i
         | IInclude ?me => get_ref me
         | IExtend ?ns => get_ref ns
         end
       in
       Std.eval_unfold [(ref, Std.AllOccurrences)] item)
    (fun _ =>
       item).

Ltac2 init_item (item : constr) (spec : constr option) () :=
  let item := unfold_item item in
  lazy_match! item with
  | IOpen _ => eapply struct_open
  | IInclude _ =>
      match spec with
      | None => eapply struct_include
      | Some spec => eapply struct_include with (module_spec := $spec)
      end
  | ILet [Binding (PVar _) _] =>
      match spec with
      | None => eapply struct_let_single
      | Some spec => eapply struct_let_single with (spec := $spec)
      end
  | ILet [Binding _ _] => eapply struct_let_pat
  | ILet _ => eapply struct_let
  | ILetRec [RecBinding _ _] =>
      match spec with
      | None => eapply struct_letrec_single
      | Some spec => eapply struct_letrec_single with (spec := $spec)
      end
  | ILetRec _ => eapply struct_letrec
  | IModule _ _ => eapply struct_module
  end.

Ltac2 next_item0 (spec : constr option) () :=
  lazy_match! goal with
  | [ |- struct_items _ (?item :: ?items) _ ] =>
      eapply structs_cons;
      Control.focus 1 1 (init_item item spec)
  end.

Ltac2 Notation "next_item" spec(opt(constr)) := Control.enter (next_item0 spec).
Tactic Notation "next_item" := ltac2:(next_item).
Tactic Notation "next_item" "with" constr(spec) :=
  let f := ltac2:(spec |-
    let spec := Option.get (Ltac1.to_constr spec) in
    Control.enter (next_item0 (Init.Some spec)))
  in
  f spec.

Ltac2 finished_struct0 () := apply structs_nil.

Ltac2 Notation "finished_struct" := finished_struct0 ().
Tactic Notation "finished_struct" := ltac2:(finished_struct).

(* -------------------------------------------------------------------------- *)

Local Open Scope nat.

Ltac2 rec unfold_Forall2 () :=
  match! goal with
  | [ |- Forall2 _ (?x :: ?xs) _ ] =>
      apply List.Forall2_cons > [ | unfold_Forall2 () ]
  | [ |- Forall2 _ [] _ ] =>
      apply List.Forall2_nil
  end.

Ltac2 solve_or_silent tac :=
 try (complete tac).

Ltac2 solve_by_simp () := solve_or_silent (fun _ => ltac1:(simp)).

Ltac2 solve_encode () := solve_or_silent (fun _ => ltac1:(encode)).

Ltac2 etuple_args (e : constr) : constr list :=
  match! e with
  | ETuple ?l =>
      let rec aux l :=
        match! l with
        | cons ?e ?t => e :: (aux t)
        | nil => []
        end
      in
      aux l
  end.

Ltac2 simp_to_value η e :=
  let res := Fresh.in_goal @t in
  let h := Fresh.in_goal @H in
  epose _ as $res;
  let ev := Control.hyp res in
  (* Fixme: surely there's an easier way to create the evar [ev]? *)
  assert (simp (eval $η $e) (ret $ev)) as $h; subst $res;
  Control.focus 1 1 (fun _ => complete (fun _ => ltac1:(simp)));
  h.

Ltac2 simp_tuple_args () :=
  let (m, _) := decompose_pure () in
  lazy_match! m with
  | (eval ?η ?e) =>
      let args := etuple_args e in
      List.map (fun e => simp_to_value η e) args
  end.

Ltac2 pure_tuple0 clear_hyps () :=
  (* Simplify all elements of the tuple to a value using [simp]. *)
  let hs := simp_tuple_args () in
  eapply pure_eval_tuple >
    [ (* Use the assumption generated by [simp_tuple_args]. *)
      unfold_Forall2 (); ltac1:(eassumption)
    | Control.enter solve_encode
    | ];
  if clear_hyps then Std.clear hs else ().

Ltac2 Notation "pure_tuple" := Control.enter (pure_tuple0 true).
Tactic Notation "pure_tuple" := ltac2:(pure_tuple).

(* -------------------------------------------------------------------------- *)

(* Given a tuple type of the form [ty := (t1 * t2 * ... * tn)],
   [evar_tuple ty] returns an evar of that type.

   Use: [let ev := evar_tuple &ty in epose $ev as t]. *)

Ltac2 rec evar_tuple (ty: constr) : constr :=
  (* Allows you to pass [ty] instead of something like [(nat * (bool * nat))%type]. *)
  let ty := eval hnf in $ty in
  lazy_match! ty with
  | prod ?a ?b =>
      let evar_a := evar_tuple a in
      let evar_b := evar_tuple b in
      (* typing constraints on the evars are enforced here;
         note that this will give you an evar with evar type,
         rather than a typed evar, if you pass it a type that is not a prod. *)
      constr:(@pair $a $b $evar_a $evar_b)
  | ?a =>
      (* This uses base name "t". *)
      let arg_i := Fresh.in_goal @t in
      (* [_] gives a new evar, use ['_] or [open_constr:(_)] in other contexts. *)
      epose _ as $arg_i;
      Control.hyp arg_i
  end.


(* -------------------------------------------------------------------------- *)

Ltac2 rec pure_data () :=
  (* Simplify all elements of the tuple to a value using [simp]. *)
  eapply pure_eval_data_val >
    [ (* Use the assumption generated by [simp_tuple_args]. *)
      eapply pure_wp_mono_ret;
      first (fun _ => eapply pure_evals_eq;
                      unfold_Forall2 ();
                      try0 (fun _ => Control.plus
                                       (fun _ => pure_path)
                                       (fun _ => pure_data ())));
    ltac1:(rewrite /singleton; intros ? ->; encode)
    | ]; ltac1:(try encode).

Ltac2 Notation "pure_data" := Control.enter (fun _ => repeat0 pure_data).
Tactic Notation "pure_data" := ltac2:(pure_data).

(* -------------------------------------------------------------------------- *)

(* [pure_simp] expects a goal of the form [pure m φ ψ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [pure m' φ ψ]. *)

Ltac2 pure_simp () :=
  eapply pure_wp_simp > [ ltac1:(simp_really) | ];
  (* Why does it always go to [ret]? *)
  Control.enter pure_ret0.

Ltac2 Notation "pure_simp" := pure_simp ().
Tactic Notation "pure_simp" := ltac2:(pure_simp).

Ltac2 pure_enter () :=
  first [
      eapply pure_enter_call_VClo
    | eapply pure_enter_call_VCloRec
    ];
  apply pure_stop_eval; try (rewrite ?try2_ret_right).

Ltac2 Notation "pure_enter" := Control.enter pure_enter.
Tactic Notation "pure_enter" := ltac2:(pure_enter).

Ltac2 pure_enter_anonfun () :=
  eapply pure_eval_anonfun; pure_enter.

Ltac2 Notation "pure_enter_anonfun" := pure_enter_anonfun ().
Tactic Notation "pure_enter_anonfun" := ltac2:(pure_enter_anonfun).

(* It is debatable in which order the two premises of the lemma [pure_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [pure (call v1 #x) ##φ ⊥]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [pure (call v1 #x) ##φ ⊥], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb pure_specs.


(* -------------------------------------------------------------------------- *)

(* Dummy proposition with one constructor *)
Inductive BLOCK := block.

(* Tranform a goal of the form [H1 -> H2 -> ... -> BLOCK -> G] into
   [H1 /\ H2 /\ ... -> G] *)
Ltac conj_until_BLOCK b :=
  lazymatch goal with
  | |- BLOCK -> _ =>
      intros _; let H := fresh in
               pose proof (H := I); revert H
  | |- _ -> BLOCK -> _ =>
      let H1 := fresh in
      intros H1 _; revert H1
  | |- ?A -> ?B -> _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      intros H1 H2; pose proof (H3 := conj H2 H1);
      revert H3;
      match b with
      | true => clear H1; conj_until_BLOCK true
      | false => conj_until_BLOCK true
      end
  end.

(* Given a tuple (or single term), move all hypotheses depending on elements
   of the tuple (or single term) into the goal *)
Ltac generalize_tuple t :=
  match t with
  | pair ?x ?y =>
      generalize dependent y; intro;
      generalize_tuple x
  | _ => generalize dependent t; intro
  end.

(* Given a term (or tuple of terms), move all hypotheses depending on this term
   (or tuple of terms) into the goal as a single conjunction *)
Ltac capture_hypotheses_aux arg :=
  generalize (block);
  generalize_tuple arg;
  conj_until_BLOCK false.

Tactic Notation "capture_hypotheses" constr(arg1) :=
  capture_hypotheses_aux arg1.

Tactic Notation "capture_hypotheses" constr(arg1) "as" simple_intropattern(x) :=
  capture_hypotheses_aux arg1; intros x.

Tactic Notation "capture_hypotheses" constr(arg1) constr(arg2) :=
  capture_hypotheses_aux (arg1, arg2).

Tactic Notation "capture_hypotheses" constr(arg1) constr(arg2) "as" simple_intropattern(x) :=
  capture_hypotheses_aux (arg1, arg2); intros x.

Ltac2 eta_expand (arg : constr) (f : constr) : constr :=
  Std.eval_pattern [(arg, Std.AllOccurrences)] f.

Ltac2 pure_rec_subgoals hwf pre () := ().

Ltac2 pure_rec0 arg pre hwf :=
  let expanded_post :=
    lazy_match! goal with
    | [ |- pure (call _ _) ##?φ ⊥ ] =>
        Std.eval_pattern [(arg, Std.AllOccurrences)] φ
    (* TODO: Standardize error messages. *)
    | [ |- _ ] =>
        Control.throw
          (Tactic_failure
             (Some
                (Message.of_string
                   "[pure_rec] expects a goal of the form [pure (call f x) ##φ ⊥]")))
    end
  in
  match! pre with
  | None =>
      eapply pure_rec_call_no_pre with (v := $arg)
  | Some ?pre =>
      eapply pure_rec_call with (v := $arg) (P := $pre)
  end;
  Control.focus 1 1 (fun _ => apply $hwf).

(* Automatically apply [pure_rec_call] on a goal of the form [pure m ##φ ⊥] *)
Ltac pure_rec_tac arg pre Hwf :=
  (* Eta-expand the postcondition *)
  match goal with
  | |- pure _ ##?H ⊥ =>
      let post := fresh in
      set (post := H); pattern arg in post; cbv delta [post]; clear post
  end;
  (* Apply [pure_rec_call], possibly with an explicit precondition *)
  match pre with
  | None =>
      eapply pure_rec_call with (v:=arg)
  | Some ?pre =>
      eapply pure_rec_call with (v:=arg) (P:=pre)
  end;
  (* Try and solve subgoals generated by [pure_rec_call] *)
  [ apply Hwf
  | lazymatch pre with
    | None =>
        capture_hypotheses arg;
        let HPre := fresh in intros HPre;
        pattern arg in HPre;
        exact HPre
    | Some _ =>
        subst; auto; fail
    end
  | ];
  clear dependent arg; (* [pure_rec_call] deprecates the original argument *)
  let HP := fresh "HP" in
  let IH := fresh "IH" in
  simpl; intros vf arg HP IH.

Tactic Notation "pure_rec" constr(arg) constr(Hwf) :=
  pure_rec_tac arg constr:(@None False) Hwf.

Tactic Notation "pure_rec" constr(arg) constr(pre) constr(Hwf) :=
  pure_rec_tac arg constr:(Some pre) Hwf.


Definition lift_rel {X Y} (R : (X * Y) -> (X * Y) -> Prop) (y : Y) : X -> X -> Prop :=
  fun x1 x2 => R (x1, y) (x2, y).


(* Automatically apply [pure_nested_call] on a goal of the form [pure m ##φ ⊥] *)
Ltac pure_nested_tac arg1 arg2 pre Hwf :=
  match goal with
  | |- pure _ ##(fun c => pure _ ##?H ⊥) ⊥ =>
      let post := fresh in
      set (post := H); pattern arg1, arg2 in post; cbv delta [post]; clear post;
      lazymatch pre with
      | None =>
          eapply pure_rec_call2 with (v1:=arg1) (v2:=arg2)
      | Some ?pre =>
          eapply pure_rec_call2 with (v1:=arg1) (v2:=arg2) (P:=pre)
      end;
      [ reflexivity
      | simpl_eval; reflexivity
      | apply Hwf
      | lazymatch pre with
          None =>
            capture_hypotheses arg1 arg2;
            let HPre := fresh in intros HPre;
                                 pattern arg1, arg2 in HPre;
                                 exact HPre
        | Some _ =>
            auto
        end
      | ];
      let HP := fresh "HP" in
      let IH := fresh "IH" in
      clear dependent arg1 arg2;
      simpl; intros vf arg1 arg2 HP IH
  end.

Tactic Notation "pure_nested" constr(arg1) constr(arg2) constr(Hwf) :=
  pure_nested_tac arg1 arg2 constr:(@None False) Hwf.

Tactic Notation "pure_nested" constr(arg1) constr(arg2)
  constr(pre) constr(Hwf) :=
  pure_nested_tac arg1 arg2 constr:(Some pre) Hwf.

(* -------------------------------------------------------------------------- *)

Module Tac.
  Import Ltac2.

  Ltac2 eta_post' (arg : constr list) :=
    lazy_match! goal with
    | [ |- pure _ ##?φ ⊥ ] =>
        let post := Fresh.in_goal @post in
        set ($post := $φ);
        Std.pattern (List.map (fun x => (x, Std.AllOccurrences)) arg)
          { Std.on_hyps := Some [(post, Std.AllOccurrences, Std.InHyp)];
                           Std.on_concl := Std.NoOccurrences };
        cbv delta [&post];
        clear $post
    end.

  Import Constr.Unsafe.

  Ltac2 eta_post'' (arg : Ltac1.t) :=
    let arg := Option.get (Ltac1.to_list arg) in
    let arg := List.map (fun x => Option.get (Ltac1.to_constr x)) arg in
    eta_post' arg.

  Ltac eta_post arg :=
    let f := ltac2:(arg |- eta_post'' arg) in
    f arg.

  Tactic Notation "eta_post" constr_list(arg) :=
    let f := ltac2:(arg |- eta_post'' arg) in
    f arg.

  Ltac2 eta_tuple_aux t :=
    let rec aux t :=
      lazy_match! t with
      | pair ?x ?y =>
          let l := aux x in
          List.append l [y]
      | ?single => [single]
      end
    in
    let arg_list := aux t in
    eta_post' arg_list.

  Ltac2 eta_tuple_aux_interface (arg : Ltac1.t) :=
    let arg := Option.get (Ltac1.to_constr arg) in
    eta_tuple_aux arg.

  Tactic Notation "eta_tuple" constr(arg) :=
    let f := ltac2:(arg |- eta_tuple_aux_interface arg) in
    f arg.

End Tac.
