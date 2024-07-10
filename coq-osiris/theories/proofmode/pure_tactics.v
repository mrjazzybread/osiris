From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp_tactics pure_hoare simp_eval.
From Ltac2 Require Ltac2.

(* This file contains tactics intended for use during hoare-style proofs of pure
   programs. These range from symbolic execution to tactics designed to aid
   the application of single lemmas. *)

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* TODO reduce just beta-redexes in the goal (possibly under ∀ and →) *)
Import Ltac2.

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
       | list (string * val) => subst η
       | _ => ()
       end)
    (Control.hyps ()).

Ltac2 Notation "clear_abstracted_env" := clear_abstracted_env ().

(* [get_env] returns the current environment under which an expression
   is currently being evaluated in [pure] mode. *)

Ltac2 get_env () :=
  lazy_match! goal with
  | [ |- pure (eval ?η _) _ ]  => η
  | [ |- _ ] =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Expected goal of the form [pure (eval η e) φ]")))
  end.

(* [abstract_env] expects a goal of the form [pure (eval η e) φ]. It creates a
   local definition for the environment [η]. *)

Ltac2 abstract_env () :=
  (* Collapse any previous environment abstraction. *)
  clear_abstracted_env;
  (* Fetch the full environment as a constr [η]. *)
  let η := get_env () in
  (* Generate a fresh name and use [set] to abstract [η]. *)
  let η0 := Fresh.in_goal @η in
  set ($η) as η0.

Ltac2 Notation "abstract_env" := abstract_env ().

(* -------------------------------------------------------------------------- *)

Ltac2 decompose_pure () : (constr * constr) :=
  match! goal with
  | [ |- pure ?m ?φ ] => (m, φ)
  end.

Ltac2 get_expr_from_eval (m : constr) :=
  lazy_match! m with
  | eval _ ?e => eval hnf in $e
  | unseal eval.eval_aux _ ?e => eval hnf in $e
  | _ =>
      Control.throw
        (Tactic_failure
           (Some
              (Message.of_string
                 "Expected term of the form [eval η e]")))
  end.

(* [pure_ret] expects a goal of the form [pure (ret v) φ]. It applies
   the lemma [pure_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac2 pure_ret0 () :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | ret ?v =>
      (* [pure_ret : v = #a → φ a → pure (ret v) φ] *)
      eapply pure_ret;
      (* We solve [v = #a] differently depending on the type of [a]. *)
      let solve_encoding : unit -> unit :=
        fun _ =>
          match! Constr.type φ with
          | val -> Prop => rewrite <- solve_encode_val; reflexivity
          | _ => complete (fun _ => ltac1:(encode))
          | _ =>
              Control.throw
                (Tactic_failure
                   (Some
                      (Message.of_string
                         "Was not able to solve encoding")))
          end
      in
      Control.dispatch [ solve_encoding ; beta ]
  end.

Ltac2 Notation "pure_ret" := Control.enter pure_ret0.

(* [pure_path] expects a goal of the form [pure (eval η (EPath x)) φ]. It applies
   the lemma [pure_eval_path], asks Coq to compute the lookup in the environment,
   and, assuming that the lookup succeeds, calls pure_ret on the result. *)

Ltac2 pure_path0 () : unit :=
  let (m, φ) := decompose_pure () in
  let e := get_expr_from_eval m in
  match! e with
  | (EPath _) =>
      (* [pure_eval_path :
          pure (lookup_path η π) ψ -> pure (eval η (EPath π)) ψ] *)
      eapply pure_eval_path;
      simpl lookup_path;
      lazy_match! goal with
      (* If the lookup has not reduced to a result, try and use a hypothesis. *)
      | [ h_ident : lookup_name ?η ?π = ret _
          |- pure (lookup_name ?η ?π) _ ] =>
          let h := Control.hyp h_ident in
          rewrite [$h]; pure_ret
      (* If the lookup has reduced to a result, use [pure_ret]. *)
      | [ |- pure (ret _) _ ] => pure_ret
      end
  end.

Ltac2 Notation "pure_path" := Control.enter pure_path0.

(* [pure_const] expects a goal of the form [pure (eval η (EConstant x)) φ].
   It applies the lemma [pure_eval_const], solves the subgoal [VConstant c = #x],
   and leaves the subgoal [φ x]. *)

Ltac2 pure_const0 () :=
  let (m, φ) := decompose_pure () in
  let e := get_expr_from_eval m in
  match! e with
  | EConstant _ =>
      (* [pure_eval_const :
          VConstant c = #x -> ψ x -> pure (eval η (EConstant c)) ψ] *)
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

Local Open Scope nat.

Lemma prove_evals η es vs :
  Forall2 (fun e v => simp (eval η e) (ret v)) es vs ->
  simp (evals η es) (ret vs).
Proof.
  generalize vs. induction es; intros.
  - apply Forall2_nil_inv_l in H; rewrite H.
    ltac1:(by simpl_evals).
  - apply Forall2_cons_inv_l in H.
    destruct H as (v & vs' & Heval & H & ->).
    ltac1:(simpl_evals).
    eapply simp_par. apply Heval.
    apply IHes. apply H.
    unfold continue; apply SimpReflexive.
Qed.

Lemma pure_eval_tuple `{Encode A} η es a vs (ψ : A -> Prop)  :
  Forall2 (fun e v => simp (eval η e) (ret v)) es vs ->
  VTuple vs = #a ->
  ψ a ->
  pure (eval η (ETuple es)) ψ.
Proof.
  intros Hevals Henc Hψ.
  ltac1:(simpl_eval).
  eapply pure_simp.
  eapply prove_simp_bind.
  - apply prove_evals. apply Hevals.
  - apply SimpReflexive.
  - pure_ret. assumption.
Qed.

Lemma simp_pure {E} `{Encode A} (m : micro val E) (φ : A -> Prop) :
  pure m φ ->
  exists v, simp m (ret v).
Proof.
  intros (a & ? & ?). exists #a. assumption.
Qed.

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
  match! m with
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

Ltac2 pure_data0 clear_hyps () :=
  eapply pure_eval_data > [ pure_tuple0 clear_hyps (); Control.enter solve_encode | ].

Ltac2 Notation "pure_data" := Control.enter (pure_data0 true).
Ltac2 Notation "pure_data_v" := Control.enter (pure_data0 false).

Goal pure (eval [] (ETuple [EConstant "true"; EConstant "false"])) (fun v => v = (true, false)).
  pure_tuple. reflexivity.
Qed.

Goal
  pure (eval []
          (EData "::"
             (ETuple [EConstant "true";
                      EConstant "[]"])))
    (fun v => v = [true]).
  pure_data_v. reflexivity.
Qed.


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

Ltac2 pure_call_VClo () :=
  apply pure_enter_call_VClo; simpl; apply pure_EvalRetThrow.

(* [pure_simp] expects a goal of the form [pure m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [pure m' φ]. *)

Ltac2 pure_simp () :=
  eapply pure_simp > [ ltac1:(simp_really) | try (pure_ret) ].

Ltac2 pure_enter () :=
  first [
      eapply pure_enter_call_VClo
    | eapply pure_enter_call_VCloRec
    ];
  apply pure_stop_eval; try (rewrite ?try2_ret_right).

Ltac2 Notation "pure_enter" := Control.enter pure_enter.

(* It is debatable in which order the two premises of the lemma [pure_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [pure (call v1 #x) φ]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [pure (call v1 #x) φ], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb pure_specs.

(* TODO may be unused *)
Ltac pure_call :=
  first [
    simple eapply pure_call; [ solve [encode] | solve [eauto with pure_specs] ]
  | simple eapply pure_consequence; [
      simple eapply pure_call; [ solve [encode] | eauto with pure_specs ]
    | cbn ]
  ].

(* -------------------------------------------------------------------------- *)

(* Evaluate an [eval] by repeatedly applying all of the simplifications. *)
Ltac2 simpl_evaluate () :=
  repeat
    (first
       [ ltac1:(simpl_eval)
       | ltac1:(simpl_evals)
       | ltac1:(simpl_evalfs)
       | ltac1:(simpl_deep_eval_match_aux)
       | ltac1:(simpl_eval_match)
       | ltac1:(simpl_eval_bindings)
       | ltac1:(simpl_eval_sitem)
       | ltac1:(simpl_eval_sitems)
       | ltac1:(simpl_eval_mexpr)
       | ltac1:(simpl_extends)
       | ltac1:(simpl_extend)
    ]).

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
    | [ |- pure (call _ _) ?φ ] =>
        Std.eval_pattern [(arg, Std.AllOccurrences)] φ
    (* TODO: Standardize error messages. *)
    | [ |- _ ] =>
        Control.throw
          (Tactic_failure
             (Some
                (Message.of_string
                   "[pure_rec] expects a goal of the form [pure (call f x) φ]")))
    end
  in
  match! pre with
  | None =>
      eapply pure_rec_call_no_pre with (v := $arg)
  | Some ?pre =>
      eapply pure_rec_call with (v := $arg) (P := $pre)
  end;
  Control.focus 1 1 (fun _ => apply $hwf).


(* Automatically apply [pure_rec_call] on a goal of the form [pure m φ] *)
Ltac pure_rec_tac arg pre Hwf :=
  (* Eta-expand the postcondition *)
  match goal with
  | |- pure _ ?H =>
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


(* Automatically apply [pure_nested_call] on a goal of the form [pure m φ] *)
Ltac pure_nested_tac arg1 arg2 pre Hwf :=
  match goal with
  | |- pure _ (fun c => pure _ ?H) =>
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
    | [ |- pure _ ?φ ] =>
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
