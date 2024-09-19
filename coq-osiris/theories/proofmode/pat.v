From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic.pure Require Import pure.

Implicit Type φ : env -> Prop.
Implicit Type ψ : Prop.

(* -------------------------------------------------------------------------- *)

(* [pats_unary] expects a goal of the form [patterns η ps vs φ ψ]. It is
   used during pattern matching because the [patterns] judgement can be
   introduced by applying [pat_PTuple]. *)

(* We use the unary version in automation tactics to avoid creating
   evars accross different subgoals and scopes. *)

Ltac pats_unary :=
  first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons_unary; [ eauto ]
    ].

(* The binary variant is more natural to use in interactive proofs. *)


Local Ltac pat_PInt :=
  eapply pat_PInt; [ | | solve [ encode ] | ]; [ representable | representable | ]; intros.


(* -------------------------------------------------------------------------- *)

From Ltac2 Require Import Ltac2.

(* [specify_cpattern] takes a goal of the form [cpattern η cp o3 φ ψ]
   and turns it into [n] goals of the form [pattern η p v φ ψ],
   returning [n]. *)

Ltac2 rec specify_cpattern () : int :=
  lazy_match! goal with
  | [ |- cpattern_wp _ ?cp ?o _ _ ] =>
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
              let m := Control.focus (Int.add n 1) (Int.add n 1) specify_cpattern in
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

Tactic Notation "specify_cpattern" := ltac2:(let _ := specify_cpattern () in ()).

(* -------------------------------------------------------------------------- *)

Ltac2 tauto0 () := ltac1:(tauto).
Ltac2 Notation tauto := tauto0 ().

(* Lemmas to help prune pattern no_match hypotheses. *)

Lemma false_or_r P :
  P ∨ False <-> P.
Proof. tauto. Qed.

Lemma false_or_l P :
  False ∨ P <-> P.
Proof. tauto. Qed.

Lemma true_or_r P :
  P ∨ True <-> True.
Proof. tauto. Qed.

Lemma true_or_l P :
  True ∨ P <-> True.
Proof. tauto. Qed.

Lemma false_and_r P :
  P ∧ False <-> False.
Proof. tauto. Qed.

Lemma false_and_l P :
  False ∧ P <-> False.
Proof. tauto. Qed.

Lemma true_and_r P :
  P ∧ True <-> P.
Proof. tauto. Qed.

Lemma true_and_l P :
  True ∧ P <-> P.
Proof. tauto. Qed.

Ltac2 rewrite_in_hyps (rw : constr) (hyps : ident list) :=
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

Ltac2 normalize_hyps (hyps : ident list) :=
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
    List.map (fun l => (fun () => rewrite_in_hyps l hyps)) lemma_list
  in
  repeat (first0 thunk_list).

Ltac2 normalize_hyp (h : ident) :=
  normalize_hyps [h].

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
      progress simpl
  end;
  (* We now have two cases:
     - Using a hypothesis or simplification has produced a goal of
       the form [ret v = ret v].
     - Using a hypothesis has led us to a new lookup *)
  match! goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  end.

Lemma rewrite_bind {A B E} (m : micro A E) (f : A -> micro B E) a :
  m = ret a ->
  bind m f = f a.
Proof. intros ->; reflexivity. Qed.

Ltac2 rec solve_lookup_path () :=
  simpl;
  lazy_match! goal with
  | [ |- lookup_name _ _ = _ ] => solve_lookup_name ()
  | [ |- bind (lookup_name ?η ?c) _ = _ ] =>
      erewrite -> (rewrite_bind (lookup_name $η $c)) >
        [ solve_lookup_name () | solve_lookup_path () ]
  | [ |- ret _ = ret _ ] => reflexivity
  end.

Ltac2 rec is_pattern (c : constr) :=
  lazy_match! c with
  | pattern _ _ _ _ _  => true
  | patterns _ _ _ _ _ => true
  | _ => false
  end.


Ltac2 constr_at_ident (h : ident) : constr :=
  let (_, _, x) :=
    List.find (fun (id, _, _) => Ident.equal h id) (Control.hyps ())
  in
  x.

Ltac2 destruct_as (h : ident) (p : Std.or_and_intro_pattern) :=
  let cl :=
        { Std.indcl_arg := Std.ElimOnIdent h;
          Std.indcl_eqn := None;
          Std.indcl_as := Some p;
          Std.indcl_in := None }
  in
  Std.destruct false [cl] None.

Ltac2 rec get_arity (c : constr) :=
  match! c with
  | ?a _ => (Int.add 1 (get_arity a))
  | _ => 0
  end.

Ltac2 rec get_constructor (c : constr) :=
  match! c with
  | ?a _ => get_constructor a
  | _ => match Constr.Unsafe.kind c with
        | Constr.Unsafe.Constructor _ _ => Some c
        | _ => None
        end
  end.

Ltac2 rec destruct_hyp (h : ident) : unit :=
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
  | _ ∧ _ =>
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
  | _ ∨ _ =>
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

Ltac2 destruct_hyps (hs : ident list) :=
  let rec iter :=
    fun f ls =>
      match ls with
      | [] => ()
      | h :: hs =>
          f h; (Control.enter (fun _ => iter f hs))
      end
  in
  iter destruct_hyp hs.

Tactic Notation "destruct_hyp" ident(hyp) :=
  let destr_hyp := ltac2:(hyp |-
                            let hyp := Option.get (Ltac1.to_ident hyp) in
                            destruct_hyp hyp)
  in
  destr_hyp hyp.

Tactic Notation "destruct_hyps" ident_list(hyps) :=
  let destr_hyps := ltac2:(hyps |-
                             let hyps := Option.get (Ltac1.to_list hyps) in
                             let hyps := List.map (fun hyp => Option.get (Ltac1.to_ident hyp)) hyps in
                             destruct_hyps hyps)
  in
  destr_hyps hyps.

(* -------------------------------------------------------------------------- *)

Ltac2 rec do_intros () :=
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

Ltac2 set_postcondition_to_false () :=
  lazy_match! goal with
  | [ |- pattern _ _ _ _ (?ψ ?arg) ] =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        unify $ψ (fun (_ : $t) => False)
      else ()
  | [ |- pattern _ _ _ _ ?ψ ] =>
      if Constr.is_evar ψ then unify $ψ False else ()
  end.

Ltac2 massage_term (c : constr) :=
  lazy_match! c with
  | ?ψ ?arg  =>
      if Constr.is_evar ψ then
        let t := Constr.type arg in
        let u := open_constr:(fun x => _) in
        unify $ψ $u
      else ()
  | _ => ()
  end.

(* (* [patterns] expects a goal of the form [patterns ...] and either *)
(*    - reduces to a [pattern ...] with [pats_PCons_unary], *)
(*    - solves the goal with [pats_PNil]. *) *)

(* Ltac2 patterns () := *)
(*   lazy_match! goal with *)
(*   | [ |- patterns _ (_ :: _) _ _ ?ψ ] => *)
(*       (* If [Ψ] is an evar, [pats_PCons_unary] instantiates it as *)
(*          [Ψ := ?Ψ1 ∨ ?Ψ2]. Currently (09/2024), the only other case *)
(*          is that [Ψ] is already instantiated to [False]. *) *)
(*       if (Constr.equal ψ constr:(False)) then *)
(*         eapply pats_PCons_unary_false *)
(*       else *)
(*         eapply pats_PCons_unary *)
(*   | [ |- patterns _ [] _ _ ?ψ ] => *)
(*       (* If [Ψ] is an evar then we instantiate it to [False], otherwise we *)
(*          use [pats_consequence_psi] and the fact that [∀ P, ⊥ -> P]. *) *)
(*       if (Constr.is_evar ψ) then *)
(*         eapply pats_PNil *)
(*       else *)
(*         eapply pats_consequence_psi > [ eapply pats_PNil | intros [] ] *)
(*   | [ |- _ ] => *)
(*       Control.throw *)
(*         (Tactic_failure *)
(*            (Some *)
(*               (Message.of_string "Expected goal of the form [patterns η ps vs φ ψ]"))) *)
(*   end. *)

(* [pattern_match_aux] expects a goal of the form [patterns ...] or
   [pattern ...] and progresses by matching the pattern(s) to the
   variable(s). This is done by applying the appropriate lemma for
   each pattern, for example [pat_PInt] if the pattern is a [PInt]. *)

(* If we don't match on any known pattern, we try to use an extensible
   Ltac1 tactic called [pattern_hook].
   This allows users to extend pattern matching to new data structures. *)

(* Ltac2 rec pattern_match_aux () := *)
(*   (* [continue_matching] is used after solving one pattern. It *)
(*      introduces new information before deciding whether to continue *)
(*      pattern-matching or whether we are done. *) *)
(*   let continue_matching := *)
(*     fun _ => do_intros (); *)
(*           (* Use [Control.enter] here because [do_intros] may solve the goal. *) *)
(*           Control.enter (fun _ => *)
(*           if is_pattern (Control.goal ()) then pattern_match_aux () else ()) *)
(*   in *)
(*   lazy_match! goal with *)
(*   | [ |- patterns _ _ _ _ _ ] => patterns (); continue_matching () *)
(*   | [ |- pattern _ ?p _ _ ?ψ ] => *)
(*       (* [massage_term] is black magic to help Rocq's unification engine. *) *)
(*       massage_term ψ; *)
(*       match! p with *)
(*       | PVar _ => *)
(*           (* We assume that a [PVar] pattern never fails. *) *)
(*           set_postcondition_to_false (); *)
(*           (* It may be the case that [pat_PVar2] can entirely solve the goal. *) *)
(*           Control.plus *)
(*             (fun _ => eapply pat_PVar2) *)
(*             (fun _ => eapply pat_PVar; *)
(*                    continue_matching ()) *)
(*       | PInt _ => *)
(*           eapply pat_PInt; *)
(*           (* First solve the encoding to ensure that all values are instantiated. *) *)
(*           Control.focus 3 3 (fun _ => solve [ ltac1:(encode) ]); *)
(*           Control.extend [] (fun _ => ltac1:(representable)) [continue_matching] *)
(*       | pNil => *)
(*           eapply pat_pNil > [ solve [ ltac1:(encode) ] *)
(*                             | continue_matching () ] *)
(*       | PConstant "[]" => *)
(*           eapply pat_pNil > [ solve [ ltac1:(encode) ] *)
(*                             | continue_matching () ] *)
(*       | pCons _ _ => *)
(*           eapply pat_pCons > [ solve [ ltac1:(encode) ] *)
(*                              | continue_matching () ] *)
(*       | PData "::" _ => *)
(*           eapply pat_pCons > [ solve [ ltac1:(encode) ] *)
(*                              | continue_matching () ] *)
(*       | PXData _ _ => *)
(*           Control.plus *)
(*             (fun _ => eapply pat_PXData_eq > [ solve_lookup_path () | pattern_match_aux () ]) *)
(*             (fun _ => eapply pat_PXData_neq > [ solve_lookup_path () | auto ]) *)
(*       | PConstant _ => *)
(*           Control.plus *)
(*             (fun _ => eapply pat_PConst_eq; continue_matching ()) *)
(*             (fun _ => eapply pat_PConst_neq > [ ltac1:(congruence) | try ltac1:(tauto) ]) *)
(*       | POr _ _ => *)
(*           apply pat_POr > [ pattern_match_aux () | pattern_match_aux () ] *)
(*       | PTuple _ => *)
(*           ltac1:(pat_PTuple); continue_matching () *)
(*       | PAlias _ _ => *)
(*           apply pat_PAlias; pattern_match_aux () *)
(*       | PAny => *)
(*           apply pat_PAny; continue_matching () *)
(*       (* If we haven't matched any known pattern, try and use the hook. *) *)
(*       | _ => *)
(*           ltac1:(pattern_hook); continue_matching () *)
(*       end *)
(*   end. *)

(* Assuming a goal of the form [⊢ pattern(s) η p v ?φ ?ψ], the
   [pattern_match] tactic tries to reduce the goal to [⊢ φ] while
   elaborating the failure postcondition [Ψ]. *)

(* Ltac2 pattern_match0 () := *)
(*   Control.enter (fun _ => *)
(*   lazy_match! goal with *)
(*   | [ |- pattern _ ?p _ _ ?ψ ] => pattern_match_aux () *)
(*   | [ |- _ ] => *)
(*       Control.throw *)
(*         (Tactic_failure *)
(*            (Some *)
(*               (Message.of_string "Expected goal of the form [pattern η p v φ ψ]"))) *)
(*   end). *)

Ltac2 pattern_match0 () := repeat constructor.
(* pattern_match0 (). *)
Tactic Notation "pattern_match" := repeat constructor.
  (* ltac2:(pattern_match). *)

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
   form [pattern _ _ _ (λ n', pure (eval η' _) ##_ ⊥) _] and one subgoal of
   the form [False]. *)

Ltac2 rec pure_match_branches0 (hyps : ident list) :=
  lazy_match! goal with
  | [ |- pure_match _ ?bs _ _ _ ] =>
      (* Match on [bs] to decide whether to apply [pure_match_cons]
         or [pure_match_nil]. *)
      lazy_match! (Std.eval_hnf bs) with
      | _ :: _ =>
          (* [pure_match_cons] produces two subgoals :
             - one of the form [cpattern ...]
             - one of the form [Ψ -> pure_match ...] *)
          eapply pure_match_cons;
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
          (* We have to show that every pattern match is exhaustive.
             If we reach this point, then we can assume that an early
             use of [destruct_hyps] was not powerful enough to solve
             this goal. We thus use the more brute-force
             [resolve_no_match] tactic. *)
          ltac1:(exfalso;resolve_no_match)
      end
  | [ |- ?g ] =>
      let () := Message.print (Message.of_constr g) in
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pure_match η bs o φ]")))
  end.

Ltac2 pure_match0 () := pure_match_branches0 [].

Ltac2 Notation "pure_match" := pure_match0 ().
Tactic Notation "pure_match" := ltac2:(pure_match).
