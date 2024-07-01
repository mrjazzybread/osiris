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

Ltac2 Notation "beta" := cbn beta.

Goal (forall l : list nat,
         l = [] ->
         (λ (x : bool), negb x = ((λ (x : bool), x) false)) true).
Proof.
  beta. reflexivity.
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
       | list (var * val) => subst η
       end)
    (Control.hyps ()).

Ltac2 Notation "clear_abstracted_env" := clear_abstracted_env ().

(* [get_env] returns the current environment under which an expression
   is currently being evaluated in [pure] mode. *)

Ltac2 get_env () :=
  lazy_match! goal with
  | [ |- pure (eval ?η _) _ ]  => η
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


(* -------------------------------------------------------------------------- *)

Ltac2 decompose_pure () : (constr * constr) :=
  match! goal with
  | [ |- pure ?m ?φ ] => (m, φ)
  end.

(* [pure_ret] expects a goal of the form [pure (ret v) φ]. It applies
   the lemma [pure_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac2 pure_ret () :=
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
          | _ => solve [ ltac1:(encode) ]
          end
      in
      Control.focus 1 1 solve_encoding;
      Control.enter beta
  end.

(* [pure_path] expects a goal of the form [pure (eval η (EPath x)) φ]. It applies
   the lemma [pure_eval_path], asks Coq to compute the lookup in the environment,
   and, assuming that the lookup succeeds, calls pure_ret on the result. *)

Ltac2 pure_path () : unit :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | eval _ (EPath _) =>
      (* [pure_eval_path :
          pure (lookup_path η π) ψ -> pure (eval η (EPath π)) ψ] *)
      eapply pure_eval_path;
      simpl lookup_path;
      lazy_match! goal with
      | [ h_ident : lookup_name ?η ?π = ret _
          |- pure (lookup_name ?η ?π) _ ] =>
          let h := Control.hyp h_ident in
          rewrite [$h]; pure_ret ()
      | [ |- pure (ret _) _ ] => pure_ret ()
      end
  end.

(* [pure_const] expects a goal of the form [pure (eval η (EConstant x)) φ].
   It applies the lemma [pure_eval_const], solves the subgoal [VConstant c = #x],
   and leaves the subgoal [φ x]. *)

Ltac2 pure_const () :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | eval _ (EConstant _) =>
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

Local Open Scope nat.

Ltac2 rec pure_ADT () : unit :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | eval _ (EData ?c (ETuple ?args)) =>
      1. Evaluate all args to encoded values.
      2. Solve [VData c (VTuple encoded_args) = #v]
      3. Reduce goal to [φ v]

Ltac2 rec pure_data () : unit :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | eval _ (EData _ (ETuple ?args)) =>
      lazy_match! eval cbn in (List.length $args) with
      | 0 => pure_const ()
      | 1 => eapply pure_eval_data1
      | 2 => eapply pure_eval_data2; eapply pure_eval_pair
      | 3 => eapply pure_eval_data3; eapply pure_eval_triple
      | 4 => eapply pure_eval_data4
      (* TODO: make a higher-order version of pure_eval_pair *)
      | _ =>
          Control.throw
            (Tactic_failure (Some
               (Message.of_string "Not implemented for this arity")))
      end
  end;
  repeat first [ pure_path (); pure_const (); pure_data () ];
  try (split; Control.focus 1 1 (fun _ => (solve [ encode ]))).

Ltac pure_call_VClo :=
  apply pure_enter_call_VClo; simpl; apply pure_EvalRetThrow.

(* [pure_simp] expects a goal of the form [pure m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [pure m' φ]. *)

Ltac pure_simp :=
  eapply pure_simp; [ simp_really |].

(* -------------------------------------------------------------------------- *)

(* pure0 leaves zero subgoal. *)
(* pure1 leaves one subgoal, which may have an arbitrary shape. *)

Ltac pure0 :=
  try pure_simp;
  first [

    pure_ret; [
      (* goal: [φ x] *)
      pure_close
    ]

  | simple eapply pure_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* goal: [pure (call #x) φ] *)
      pure_close
    ]

  | simple eapply pure_call_consequence; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [pure (call #x) φ] *)
    | solve [eauto with pure_specs]
      (* goal: [∀ x, φ x → φ' x] *)
    | pure_close
    ]

  | simple eapply pure_bind_as_bool; [ pure0 | beta; intros; pure0 ]
  | simple eapply pure_bind_as_int ; [ pure0 | beta; intros; pure0 ]
  | simple eapply pure_bind        ; [ pure0 | beta; intros; pure0 ]
  | simple eapply pure_try         ; [ pure0 | beta; intros; pure0 ]

  | pure_close

  ]

with pure1 :=
  try pure_simp;
  first [

    pure_ret (* residual goal: [φ x] *)

  | simple eapply pure_call_consequence; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [pure (call #x) φ] *)
    | solve [eauto with pure_specs]
      (* residual goal: [∀ x, φ x → φ' x] *)
    | beta
    ]

  | simple eapply pure_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* residual goal: [pure (call #x) φ] *)
      idtac
    ]

  | simple eapply pure_bind_as_bool; [ pure0 | (* residual goal *) beta ]
  | simple eapply pure_bind_as_int ; [ pure0 | (* residual goal *) beta ]
  | simple eapply pure_bind        ; [ pure0 | (* residual goal *) beta ]
  | simple eapply pure_try         ; [ pure0 | (* residual goal *) beta ]

  | idtac (* residual goal *)

  ]

with pure_close :=
  solve [ eauto with pure_specs representable ].

Ltac pure1_call_step :=
  first [
    eapply pure_enter_call_VClo
  | eapply pure_enter_call_VCloRec
  ].

Ltac pure_enter :=
  pure1_call_step;
  pure1.

Ltac pure_specify x φ :=
  lazymatch goal with
  | |- pure (bind (ret (?δ ++ _, ?δ ++ _)) _) _ =>
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

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

Ltac pure_enter_and_abstract :=
  lazymatch goal with |- pure (call ?v _) _ =>
    (* First, expand [call] away. *)
    pure1_call_step;
    normalize;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.

(* -------------------------------------------------------------------------- *)

(* Evaluate an [eval] by repeatedly applying all of the simplifications. *)
Ltac simpl_evaluate :=
  repeat first [ simpl_eval
               | simpl_evals
               | simpl_evalfs
               | simpl_deep_eval_match_aux
               | simpl_eval_match
               | simpl_eval_bindings
               | simpl_eval_sitem
               | simpl_eval_sitems
               | simpl_eval_mexpr
               | simpl_extends
               | simpl_extend
    ].

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

(* Automatically apply [pure_nested_call] on a goal of the form [pure m φ] *)
Ltac pure_nested_tac arg1 arg2 pre Hwf :=
  match goal with
  | |- pure _ (fun c => pure _ ?H) =>
      let post := fresh in
      set (post := H); pattern arg1, arg2 in post; cbv delta [post]; clear post;
      lazymatch pre with
      | None =>
          eapply pure_nested_call with (v1:=arg1) (v2:=arg2)
      | Some ?pre =>
          eapply pure_nested_call with (v1:=arg1) (v2:=arg2) (P:=pre)
      end;
      [ reflexivity
      | simpl_evaluate; reflexivity
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
