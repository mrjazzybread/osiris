From osiris Require Import base.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp capital_SIMP.
From Ltac2 Require Ltac2.

(* This file contains tactics intended for use during hoare-style proofs of pure
   programs. These range from symbolic execution to tactics designed to aid
   the application of single lemmas.

   Very Work-In-Progress and subject to change (10/12/2023) *)

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* TODO reduce just beta-redexes in the goal (possibly under ∀ and →) *)

Ltac beta :=
  cbn beta.

Goal (λ (x : bool), negb x = ((λ (x : bool), x) false)) true.
Proof.
  beta. reflexivity.
Qed.

(* [SIMP_ret] expects a goal of the form [SIMP (ret v) φ]. It applies
   the lemma [SIMP_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac SIMP_ret :=
  simple eapply SIMP_ret; [ solve [ encode ] | beta ].

(* [SIMP_simp] expects a goal of the form [SIMP m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [SIMP m' φ]. *)

Ltac SIMP_simp :=
  simple eapply SIMP_simp; [ simp_really |].

(* SIMP0 leaves zero subgoal. *)
(* SIMP1 leaves one subgoal, which may have an arbitrary shape. *)

Ltac SIMP0 :=
  try SIMP_simp;
  first [

    SIMP_ret; [
      (* goal: [φ x] *)
      SIMP_close
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* goal: [SIMP (call #x) φ] *)
      SIMP_close
    ]

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* goal: [∀ x, φ x → φ' x] *)
    | SIMP_close
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind        ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_try         ; [ SIMP0 | beta; intros; SIMP0 ]

  | SIMP_close

  ]

with SIMP1 :=
  try SIMP_simp;
  first [

    SIMP_ret (* residual goal: [φ x] *)

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* residual goal: [∀ x, φ x → φ' x] *)
    | beta
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* residual goal: [SIMP (call #x) φ] *)
      idtac
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind        ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_try         ; [ SIMP0 | (* residual goal *) beta ]

  | idtac (* residual goal *)

  ]

with SIMP_close :=
  solve [ eauto with SIMP_specs representable ].

Ltac SIMP1_call_step :=
  first [
    eapply SIMP_enter_call_VClo
  | eapply SIMP_enter_call_VCloRec
  ].

Ltac SIMP_enter :=
  SIMP1_call_step;
  SIMP1.

Ltac SIMP_continue :=
  lazymatch goal with
  | |- SIMP ?m _ =>
      unfold_breakpoint m;
      SIMP1
  | _ =>
      fail "[SIMP_continue] expects a goal of the form [SIMP _ _]"
  end.

Ltac SIMP_specify x φ :=
  lazymatch goal with
  | |- SIMP (bind (ret_dconcat ?δ _) _) _ =>
      (* is this reduction too strong? *)
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* It is debatable in which order the two premises of the lemma [SIMP_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [SIMP (call v1 #x) φ]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [SIMP (call v1 #x) φ], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb SIMP_specs.

(* TODO may be unused *)
Ltac SIMP_call :=
  first [
    simple eapply SIMP_call; [ solve [encode] | solve [eauto with SIMP_specs] ]
  | simple eapply SIMP_covariant; [
      simple eapply SIMP_call; [ solve [encode] | eauto with SIMP_specs ]
    | cbn ]
  ].

Ltac SIMP_enter_and_abstract :=
  lazymatch goal with |- SIMP (call ?v _) _ =>
    (* First, expand [call] away. *)
    SIMP1_call_step;
    normalize;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.

(* -------------------------------------------------------------------------- *)

(* Evaluate an [eval] by repeatedly changing [eval] into [eval'] *)
Ltac simp_evaluate :=
  simpl; repeat (rewrite eval_eval'; simpl).

(* On a goal of the form [SIMP (Stop CEval x k ko) φ], evaluate the call by:
   stepping through the [Stop] with the appropriate advance_SimpEval lemma,
   using [simp_evaluate] under the resulting SIMP *)
Ltac SIMP_evaluate :=
  (lazymatch goal with
   | |- SIMP (Stop CEval _ ret (λ _ : (), Next)) _ =>
       eapply SIMP_simp; [apply advance_SimpEvalRetNext | apply SimpReflexive]
   | |- SIMP (Stop CEval _ _ (λ _ : (), Next)) _ =>
       eapply SIMP_simp; [apply advance_SimpEvalNext | apply SimpReflexive]
   | |- SIMP (Stop CEval _ _ _) _ =>
       eapply SIMP_simp; [apply advance_SimpEval | apply SimpReflexive]
   | _ => idtac
   end);
  eapply SIMP_simp; [simp_evaluate; apply SimpReflexive|].

Ltac SimpParRet :=
  lazymatch goal with
  | |- simp (Par (ret _) (ret _) _ _) _ =>
      apply SimpParRetRet
  | |- simp (Par (ret _) _ _ (λ _ : (), Next)) _ =>
      apply SimpParRetLeftNext
  | |- simp (Par _ (ret _) _ (λ _ : (), Next)) _ =>
      apply SimpParRetRightNext
  | |- simp (Par (ret _) _ _ _) _ =>
      apply SimpParRetLeft
  | |- simp (Par _ (ret _) _ _) _ =>
      apply SimpParRetRight
  end.

Ltac SIMPParRet :=
  eapply SIMP_simp; first SimpParRet; simpl.

Ltac SIMP_execute :=
  repeat (simpl; (SIMP_evaluate || SIMP_continue)); repeat SIMPParRet.

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

(* Automatically apply [SIMP_rec_call] on a goal of the form [SIMP m φ] *)
Ltac SIMP_rec_tac arg pre Hwf :=
  (* Eta-expand the postcondition *)
  match goal with
  | |- SIMP _ ?H =>
      let post := fresh in
      set (post := H); pattern arg in post; cbv delta [post]; clear post
  end;
  (* Apply [SIMP_rec_call], possibly with an explicit precondition *)
  match pre with
  | None =>
      eapply SIMP_rec_call with (v:=arg)
  | Some ?pre =>
      eapply SIMP_rec_call with (v:=arg) (P:=pre)
  end;
  (* Try and solve subgoals generated by [SIMP_rec_call] *)
  [ apply Hwf
  | lazymatch pre with
    | None =>
        capture_hypotheses arg;
        let HPre := fresh in intros HPre;
        pattern arg in HPre;
        exact HPre
    | Some _ =>
        auto
    end
  | ];
  clear dependent arg; (* [SIMP_rec_call] deprecates the original argument *)
  let HP := fresh "HP" in
  let IH := fresh "IH" in
  simpl; intros vf arg HP IH.

Tactic Notation "SIMP_rec" constr(arg) constr(Hwf) :=
  SIMP_rec_tac arg constr:(@None False) Hwf.

Tactic Notation "SIMP_rec" constr(arg) constr(pre) constr(Hwf) :=
  SIMP_rec_tac arg constr:(Some pre) Hwf.

(* Automatically apply [SIMP_nested_call] on a goal of the form [SIMP m φ] *)
Ltac SIMP_nested_tac arg1 arg2 pre Hwf :=
  match goal with
  | |- SIMP _ (fun c => SIMP _ ?H) =>
      let post := fresh in
      set (post := H); pattern arg1, arg2 in post; cbv delta [post]; clear post;
      lazymatch pre with
      | None =>
          eapply SIMP_nested_call with (v1:=arg1) (v2:=arg2)
      | Some ?pre =>
          eapply SIMP_nested_call with (v1:=arg1) (v2:=arg2) (P:=pre)
      end;
      [ reflexivity
      | simpl; rewrite eval_eval'; reflexivity
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

Tactic Notation "SIMP_nested" constr(arg1) constr(arg2) constr(Hwf) :=
  SIMP_nested_tac arg1 arg2 constr:(@None False) Hwf.

Tactic Notation "SIMP_nested" constr(arg1) constr(arg2)
  constr(pre) constr(Hwf) :=
  SIMP_nested_tac arg1 arg2 constr:(Some pre) Hwf.

(* -------------------------------------------------------------------------- *)

Module Tac.
  Import Ltac2.
  
  Ltac2 eta_post' (arg : constr list) :=
    lazy_match! goal with
    | [ |- SIMP _ ?φ ] =>
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

