From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import weakestpre.
From osiris.proofmode Require Import simp.

(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

Lemma tac_change_goal {Σ: gFunctors} Δ (P Q : iProp Σ) :
  (P ⊢ Q) →
  environments.envs_entails Δ P →
  environments.envs_entails Δ Q.
Proof.
  intros H Henv.
  eapply coq_tactics.tac_eval; last done.
  intros Q''; subst Q''. assumption.
Qed.

(* [lem] must be of the form (P -∗ Q). Thanks to the tactic notation it can be
   lemma whose forall quantifiers have been instantiated with [_]. *)
Ltac tac_change_goal lem :=
  simple notypeclasses refine (tac_change_goal _ _ _ lem _).
Tactic Notation "tac_change_goal" uconstr(lem) := (tac_change_goal lem).

(* -------------------------------------------------------------------------- *)

(* Tactics to move forward in the proof. *)

(* NOTE:
 * - The performance of the calls to [cbn] made by the functions below
 *   crucially depends on adequate unfolding settings being set for terms
 *   that can appear in the goal, using the [Arguments] command.
 *   (Such as [eval] and definition it uses transitively or combinators
 *   of the monad.)
 *
 * TODO:
-* - we still reduce too much:
 *   + we reduce under continuations;
 *   + because we reduce the whole Coq context, we reduce all the Iris
       hypotheses!
 * TODO: just apply [wp_simp] and reduce in the subgoal [simp m ?m'].

 * TODO: letting [simp] reduce [Stop CEval _ _] is not satisfactory,
         as it deprives us from the opportunity of applying the lemma
         [wp_eval] and eliminating a [later] modality. So, the lemma
         [wp_eval] should be applied first, when applicable.

 * TODO: blindly applying [wp_bind] is dangerous, as it will duplicate
         the continuation (therefore the entire rest of the proof!)
         if the left-hand side of the sequence involves a conditional
         construct. A more cautious approach is to use
         [wp_bind_binary] and silently apply this lemma
         only if we are able to silently solve its first premise. *)

Ltac wp_simp :=
  iApply wp_simp; first by simp_really.

(* [wp_bind] can be applied when the goal is of the form [WP bind m m' {{ _ }}].
   It bahaves differently depending on the term [m]:
   - if [m] can be simplified into [ret v], then [bind] can reduce: do it;
   - otherwise, apply the lemma [wp_bind]. *)
Ltac wp_bind :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      first [
          (* [wp_simp] will reduce the bind if it can. *)
          progress wp_simp; try once wp_bind
        | tac_change_goal (wp_bind _ _ _ _ _) ]
  | _ => fail "[wp_bind] should only be applied to goals of the form [WP bind _ _ {{ _ }}]."
  end.

Ltac wp_step :=
  (* The lazymatch stills misses a few cases and should be completed. *)
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ret _) _) =>
      tac_change_goal (wp_ret _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (try _ _ _) _) =>
      tac_change_goal (wp_try _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) (ret _) _ _) _) =>
      tac_change_goal (wp_par_ret_ret _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par _ (ret _) ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_right _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_left _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (stop CEval _) _) =>
      first [ tac_change_goal (wp_eval_ret _ _ _ _ _ _)
            | tac_change_goal (wp_eval _ _ _ _ _ _ _) ]
  | |- environments.envs_entails _ (wp _ _ (Stop CFlip _ _ _) _) =>
      tac_change_goal (wp_flip _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      fail "[bind] is no longer simplified by [wp_step]."
  | _ =>
      fail "The goal must be a wp to apply [wp_step]."
  end.

Ltac wp_cbn_term m :=
  lazymatch m with
  | Par ?m1 ?m2 ?k ?ko =>
      let m'1 := wp_cbn_term m1 in
      let m'2 := wp_cbn_term m2 in
      uconstr:(Par m'1 m'2 k ko)
  | Stop ?c ?x ?k ?ko =>
      let x' := eval cbn in x in uconstr:(Stop c x' k ko)
  | _ => let m' := eval cbn -[encode] in m in uconstr:(m')
  end.

Ltac wp_cbn :=
  lazymatch goal with
  | |- environments.envs_entails _ $ wp _ _ ?m _ =>
      let m' := wp_cbn_term m in
      first [
          progress change m with m'
        | fail "[wp_cbn] No progress to be made." ]
  | _ => fail "[wp_cbn] WP goal expected."
  end.

Local Ltac wp_progress :=
  first [
      lazymatch goal with
      | |- environments.envs_entails _ $ wp _ _ (eval _ _) _ =>
          rewrite eval_eval'; try progress wp_cbn
      end
    | wp_cbn (* TODO: better control the reduction strategy. *)
    | progress wp_simp
    | cbn beta
    ].

Ltac wp_concat :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ ?m _) =>
      unfold_breakpoint m
  | _ => fail "There is no concatenation here."
  end.

Local Ltac wp_startproof :=
  iStartProof.

Ltac wp :=
  wp_startproof;
  try progress wp_progress;
  repeat
    (first [
          (* 1. Try to eliminate a later or take a step. *)
          lazymatch goal with
          | |- environments.envs_entails _ (bi_later _) => iNext
          | _ => wp_step
          end
        | (* 2. Try to simplify the proof goal using [wp_progress].*)
          wp_progress
        | (* Otherwise, do nothing ([repeat] will stop). *)
          idtac
    ]).
    (* TODO [wp] should produce a normalized residual goal *)
    (* TODO clarify where normalized goals are expected/produced *)

(* -------------------------------------------------------------------------- *)

(* We want symbolic execution to stop at breakpoints, that is, when the
   environment is extended with new bindings. This gives the user a chance
   to prove specifications about these bindings using [wp_specify]. *)

(* The tactic [wp_continue] moves past a breakpoint and invokes [wp]
   to continue simplifying the goal. *)

(* The tactic [simp] applies [rewrite ?bind_bind], which ensures that
   the breakpoint of interest cannot be buried under several [bind]s. *)

Ltac wp_continue :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ ?m _) =>
      unfold_breakpoint m
  end;
  wp.

(* -------------------------------------------------------------------------- *)

Ltac wp_par :=
  iApply wp_par; [wp | wp | ].

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ].

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  | iApply (wp_covariant with H)
  ];
  cbn.

Ltac wp_enter :=
  iApply wp_simp; [
    simp_enter; [ normalize; eapply SimpReflexive ]
  | (* residual goal *)
  ].

Ltac wp_enter_and_abstract :=
  lazymatch goal with |- environments.envs_entails _ (wp _ _ (call ?v _) _) =>
    (* First, expand [call] away. *)
    iApply wp_simp; [
      simp_enter; eapply SimpReflexive
    | normalize
    ];
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.

(* TODO: not great *)
Ltac wp_set_postcondition :=
    by
    lazymatch goal with
    | |- environments.envs_entails ?Δ (?φ ?v) =>
        is_evar φ;
        let hyps :=
          eval cbn in (
                     environments.env_to_list $
                     environments.env_spatial Δ
                   ) in
          let H := eval cbn in (
                              match hyps with
                              | [] => λ res, ⌜ res = v ⌝%I
                              | _ => (λ res, ⌜ res = v ⌝ ∗ [∗ list] p ∈ hyps, p)%I
                              end)%I in
            instantiate (1 := H)
    end.

(* -------------------------------------------------------------------------- *)

(* Store-related tactics. *)

Ltac wp_alloc l H:=
  iApply wp_alloc; iNext; iIntros (l) H; wp.
Ltac wp_load H :=
  iApply (wp_load with H); iNext; iIntros H; wp.
Ltac wp_store H :=
  iApply (wp_store with H); iNext; iIntros H; wp.

(* -------------------------------------------------------------------------- *)
(* Tactics used to prove the specification of a module expression. *)


Ltac wp_module_spec :=
  lazymatch goal with
  | |- environments.envs_entails _  (?φ (VStruct ?η)) =>
      iExists _; iSplit ; first  (iPureIntro; reflexivity);
      repeat first
             [ (iApply big_sepL_cons; iSplitL;
                first (iExists _; iSplit; [ done | iAssumption || done ])
               )
             | iApply big_sepL_nil; iPureIntro; exact I
             | idtac
                 "I cannot prove the required spec; please go back and prove the required specifications."
             ]
  end.

(* -------------------------------------------------------------------------- *)

(* [Ltac] helpers to deal with value abstraction. *)

Tactic Notation "oAbstract" constr(s1) ident(i1):=
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  | |- context [EnvCons s1 (VClo ?η ?e) _] =>
      generalize (VClo η e); intro i1
  end.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2) :=
  oAbstract s1 i1;
  oAbstract s2 i2.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2)
       constr(s3) ident(i3) :=
  oAbstract s1 i1;
  oAbstract s2 i2
            s3 i3.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2)
       constr(s3) ident(i3)
       constr(s4) ident(i4):=
  oAbstract s1 i1
            s2 i2;
  oAbstract s3 i3
            s4 i4.

(* -------------------------------------------------------------------------- *)

(* [oCall] behaves in the same way that wp_call does, except that it abstracts
   the required closures.
   It is defined as a notation so that it is easy to ask for more idents (Ltac
   cannot take a list of idents as argument for a tactic). *)
Tactic Notation "oCall" constr(s1) ident(i1):=
  (* TODO if possible, use [wp_enter] instead of [unfold call] *)
  with_strategy transparent [call] unfold call; simpl (bind _ _);
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end;
  wp.
Tactic Notation "oCall" constr(s1) ident(i1) constr(s2) ident(i2) :=
  with_strategy transparent [call] unfold call; wp;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s2] =>
      generalize (VCloRec η bds s2); intro i2
  end.

(* -------------------------------------------------------------------------- *)

(* Below are defined local tactics which are used to define [oSpecify]. *)

(* [oSpecify] is used to provide the user the possibility to provide
   specifications for variables which are about to be added to the environment
   through [ret_dconcat].
   The tactic notation only works for two arguments, as it is what is required
   here. If it works, it should be moved to [proofmode/specifications.v].
   Note: [ret_dconcat] only takes two arguments now (the continuation is
         always ret). *)
Local Ltac oSpecify_intros lnames :=
  let hyps := eval cbn in (foldr String.append "" lnames) in
  iIntros hyps.

Local Ltac oSpecify_assume lspecs lnames lhyps δ :=
  let specs :=
    eval cbn in (
               foldr
                 (λ '(spec, name) (res: list (iProp _)),
                   let value :=
                     match lookup_name δ name with
                     | Ret v => v
                     | _ => VUnit
                     end in
                   spec value :: res)
                 [] (combine lspecs lnames)
             )
    in
    iApply (assumming_list specs);
      first (by eauto using intuitionistically_persistent);
      (try iModIntro);
      oSpecify_intros lhyps.

Tactic Notation "oSpecify_abstract" constr(δ) constr(n1) ident(i1) :=
  let value :=
    eval cbn in (match lookup_name δ n1 with
                           | Ret v => v
                           | _ => VUnit
                           end) in
    generalize value; intros i1.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2) :=
  oSpecify_abstract δ n1 i1;
  oSpecify_abstract δ n2 i2.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2)
       constr(n3) ident(i3) :=
  oSpecify_abstract δ n1 i1 n2 i2;
  oSpecify_abstract δ n3 i3.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2)
       constr(n3) ident(i3)
       constr(n4) ident(i4) :=
  oSpecify_abstract δ n1 i1 n2 i2;
  oSpecify_abstract δ n3 i3 n4 i4.

(* -------------------------------------------------------------------------- *)

(* Definition of [oSpecify], used to specify and abstract away values when the
   evaluation stops on en environment concatenation. *)

Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume [spec1] [n1] [H1] δ;
      last ( oSpecify_abstract δ n1 i1 ;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1] [n1] [H1] δ;
      last ( oSpecify_abstract δ n1 i1 ;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2]
                      [n1; n2]
                      [H1; H2]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 ;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume [spec1; spec2]
                      [n1; n2]
                      [H1; H2]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 ;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3] [n1; n2; n3] [H1; H2; H3] δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3] [n1; n2; n3] [H1; H2; H3] δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3)
       constr(n4) constr(spec4) ident(i4) constr(H4) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3; spec4]
                      [n1; n2; n3; n4]
                      [H1; H2; H3; H4]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3 n4 i4;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3; spec4]
                      [n1; n2; n3; n4]
                      [H1; H2; H3; H4]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3 n4 i4;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.

(* -------------------------------------------------------------------------- *)

(* Wrapers around the above [Tactic Notation]s to autoname idents.
   For some (unknown) reason, it is not possible to overload [oSpecify] with
   four new notations, even if the arities differ from the previous notations.
 *)

From iris.proofmode Require Import string_ident.

Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1) :=
  string_to_ident_cps n1 ltac:(fun i1 =>
  let i1 := fresh i1 in
  oSpecify n1 spec1 i1 H1).
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2) :=
  string_to_ident_cps
    n1
    ltac:(fun i1 =>
            let i1 := fresh i1 in
            string_to_ident_cps
              n2
              ltac:(fun i2 =>
                      let i2 := fresh i2 in
                      oSpecify n1 spec1 i1 H1
                               n2 spec2 i2 H2)).
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2)
       constr(n3) constr(spec3) constr(H3) :=
  string_to_ident_cps
    n1
    ltac:(fun i1 =>
            let i1 := fresh i1 in
            string_to_ident_cps
              n2
              ltac:(fun i2 =>
                      let i2 := fresh i2 in
                      string_to_ident_cps
                        n3
                        ltac:(fun i3 =>
                                let i3:= fresh i3 in
                                oSpecify n1 spec1 i1 H1
                                         n2 spec2 i2 H2
                                         n3 spec3 i3 H3))).
