From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.

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

Ltac2 decompose_pure () : (constr * constr) :=
  match! goal with
  | [ |- pure ?m ##?φ _ ] => (m, φ)
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

(* [pure_ret] expects a goal of the form [pure (ret v) ##φ ⊥]. It applies
   the lemma [pure_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac2 pure_ret0 () :=
  let (m, φ) := decompose_pure () in
  match! (Std.eval_vm None m) with
  | ret ?v =>
      (* [pure_ret : v = #a → φ a → pure (ret v) ##φ ⊥] *)
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
Tactic Notation "pure_ret" := ltac2:(pure_ret).

(* [pure_path] expects a goal of the form [pure (eval η (EPath x)) ##φ ⊥]. It applies
   the lemma [pure_eval_path], asks Coq to compute the lookup in the environment,
   and, assuming that the lookup succeeds, calls pure_ret on the result. *)

(* Ltac2 pure_path0 () : unit := *)
(*   let (m, φ) := decompose_pure () in *)
(*   let e := get_expr_from_eval m in *)
(*   match! e with *)
(*   | (EPath _) => *)
(*       (* [pure_eval_path : *)
(*           pure (lookup_path η π) ##ψ ⊥ -> pure (eval η (EPath π)) ##ψ ⊥] *) *)
(*       eapply pure_eval_path; *)
(*       simpl lookup_path; *)
(*       lazy_match! goal with *)
(*       (* If the lookup has not reduced to a result, try and use a hypothesis. *) *)
(*       | [ h_ident : lookup_name ?η ?π = ret _ *)
(*           |- pure (lookup_name ?η ?π) _ _ ] => *)
(*           let h := Control.hyp h_ident in *)
(*           rewrite [$h]; pure_ret *)
(*       (* If the lookup has reduced to a result, use [pure_ret]. *) *)
(*       | [ |- pure (ret _) _ _ ] => pure_ret *)
(*       end *)
(*   end. *)

(* Ltac2 Notation "pure_path" := Control.enter pure_path0. *)
(* Tactic Notation "pure_path" := ltac2:(pure_path). *)

(* [pure_const] expects a goal of the form [pure (eval η (EConstant x)) ##φ ⊥].
   It applies the lemma [pure_eval_const], solves the subgoal [VConstant c = #x],
   and leaves the subgoal [φ x]. *)

(* Ltac2 pure_const0 () := *)
(*   let (m, φ) := decompose_pure () in *)
(*   let e := get_expr_from_eval m in *)
(*   match! e with *)
(*   | EConstant _ => *)
(*       (* [pure_eval_const : *)
(*           VConstant c = #x -> ψ x -> pure (eval η (EConstant c)) ##ψ ⊥] *) *)
(*       eapply pure_eval_const; *)
(*       let solve_encoding : unit -> unit := *)
(*         fun _ => *)
(*           match! Constr.type φ with *)
(*           | val -> Prop => rewrite <- solve_encode_val; reflexivity *)
(*           | _ => solve [ ltac1:(encode) ] *)
(*           end *)
(*       in *)
(*       Control.focus 1 1 solve_encoding *)
(*   end. *)

(* Ltac2 Notation "pure_const" := Control.enter pure_const0. *)
(* Tactic Notation "pure_const" := ltac2:(pure_const). *)

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

(* Ltac2 pure_data0 clear_hyps () := *)
(*   eapply pure_eval_data > [ pure_tuple0 clear_hyps (); Control.enter solve_encode | ]. *)

(* Ltac2 Notation "pure_data" := Control.enter (pure_data0 true). *)
(* Ltac2 Notation "pure_data_v" := Control.enter (pure_data0 false). *)

(* Tactic Notation "pure_data" := ltac2:(pure_data). *)
(* Tactic Notation "pure_data_v" := ltac2:(pure_data_v). *)

Goal pure (eval [] (ETuple [EConstant "true"; EConstant "false"])) (fun v => v = (true, false)) ⊥.
  (* pure_tuple. reflexivity. *)
Abort.

(* Goal *)
(*   pure (eval [] *)
(*           (EData "::" *)
(*              (ETuple [EConstant "true"; *)
(*                       EConstant "[]"]))) *)
(*     ##(fun v => v = [true]) ⊥. *)
(*   pure_data_v. reflexivity. *)
(* Qed. *)


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

(* [pure_simp] expects a goal of the form [pure m φ ψ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [pure m' φ ψ]. *)

(* Local Lemma pure_simp `{Encode A} {X} m m' (φ : A → Prop) : *)
(*   simp m m' → pure (E := X) m' ##φ ⊥ → pure (E := X) m ##φ ⊥. *)
(* Proof. apply pure_simp. Qed. *)

(* Ltac2 pure_simp () := *)
(*   eapply pure_simp > [ ltac1:(simp_really) | try (pure_ret) ]. *)

(* Ltac2 Notation "pure_simp" := pure_simp (). *)
(* Tactic Notation "pure_simp" := ltac2:(pure_simp). *)

(* Ltac2 pure_enter () := *)
(*   first [ *)
(*       eapply pure_enter_call_VClo *)
(*     | eapply pure_enter_call_VCloRec *)
(*     ]; *)
(*   apply pure_stop_eval; try (rewrite ?try2_ret_right). *)

(* Ltac2 Notation "pure_enter" := Control.enter pure_enter. *)
(* Tactic Notation "pure_enter" := ltac2:(pure_enter). *)

(* (* It is debatable in which order the two premises of the lemma [pure_call] *)
(*    should be attacked. The premise [v'2 = #x] may seem easy to solve (this *)
(*    is the job of the tactic [encode]) so one may wish to solve it first. *)
(*    This offers the advantage of instantiating [x] immediately, so [x] is *)
(*    known when we try to prove that the call is permitted -- which may *)
(*    involve proving that a precondition holds. *)

(*    However, solving [v'2 = #x] can involve guessing some types (e.g., the *)
(*    type of an empty list), and we have used [Hint Mode] in encode.v to *)
(*    forbid this. So, it can also be preferable to first solve the premise *)
(*    [pure (call v1 #x) ##φ ⊥]. Doing so can allow us to instantiate these types *)
(*    in a correct way. *)

(*    One might wish to try both approaches in sequence, but waiting until *)
(*    [encode] fails is very slow (several seconds). *)

(*    One might also wish to do a bit of both: that is, first apply some lemma *)
(*    [L] to the subgoal [pure (call v1 #x) ##φ ⊥], then solve [v'2 = #x], then *)
(*    attack the proof obligations created by applying the lemma [L]. *) *)

(* Create HintDb pure_specs. *)

(* (* TODO may be unused *) *)
(* Ltac pure_call := *)
(*   first [ *)
(*     simple eapply pure_call; [ solve [encode] | solve [eauto with pure_specs] ] *)
(*   | simple eapply pure_consequence; [ *)
(*       simple eapply pure_call; [ solve [encode] | eauto with pure_specs ] *)
(*     | cbn ] *)
(*   ]. *)

