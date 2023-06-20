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

Ltac wp_bind :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      tac_change_goal (wp_bind _ _ _ _ _)
  | _ => fail "[wp_bind]"
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

Ltac wp_simp :=
  iApply wp_simp; first by simp_really.

Local Ltac wp_progress :=
  progress (
      cbn (* TODO: better control the reduction strategy. *)
    ).

Ltac wp :=
  iStartProof;
  (try wp_progress);
  repeat
    (first [
          lazymatch goal with
          | |- environments.envs_entails _ (bi_later _) => iNext
          | _ => wp_step; try progress cbn
          end
        | apply tc_change_goal
        | try progress wp_simp
        | idtac "Nothing to do."
    ]).

Ltac wp_par :=
  iApply wp_par; [wp | wp | ].

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ].

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  ];
  cbn.

Ltac wp_call :=
  with_strategy transparent [call] unfold call; wp.


(* TODO not great *)
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


Ltac wp_alloc l H:=
  iApply wp_alloc; iNext; iIntros (l) H; wp.
Ltac wp_load H :=
  iApply (wp_load with H); iNext; iIntros H; wp.
Ltac wp_store H :=
  iApply (wp_store with H); iNext; iIntros H; wp.

(* -------------------------------------------------------------------------- *)

(* We want symbolic execution to stop at [ret_concat], that is, when the
   environment is extended with new bindings. This gives the user a chance
   to prove specifications about these bindings using [wp_specify]. *)

(* The tactic [wp_continue] expands away [ret_concat] and invokes [wp]
   to continue simplifying the goal. *)

(* One should avoid [context] in the following tactic, as it might match an
   occurrence that is in the postcondition. *)
(* TODO [ret_concat] is usually under a [bind], not at the root *)
(* TODO unless [wp_bind] has been automatically applied,
        which is undesirable, as noted elsewhere! *)
(* TODO [rewrite ?bind_bind] to make sure it is not buried under
        several binds *)
Ltac wp_continue :=
  lazymatch goal with
  | |- environments.envs_entails
         _ $
         wp _ _ (ret_concat ?δ _) _ =>
      with_strategy transparent [ret_concat] unfold ret_concat at 1
        (* We wish to unfold just the root occurrence. *)
  | |- environments.envs_entails
         _ $
         wp _ _ (bind (ret_concat ?δ _) _) _ =>
      with_strategy transparent [ret_concat] unfold ret_concat at 1
        (* We wish to unfold just the root occurrence. *)
  | |- environments.envs_entails
         _ $
         wp _ _ (ret_dconcat ?δ _) _ =>
      with_strategy transparent [ret_dconcat] unfold ret_dconcat at 1
        (* We wish to unfold just the root occurrence. *)
  end; wp.

Ltac wp_autocontinue :=
  repeat (wp || wp_continue).


(* The tactic [wp_specify x φ H] should be used when the goal begins with
   [bind (ret_concat δ η) _], that is, when the environment is about to
   be extended with the environment fragment [δ].

   The tactic looks up the variable [x] in the environment fragment [δ]
   so as to find the value [v] of this variable. Then, it produces two
   subgoals:
   - the subgoal [φ v],
     letting the user prove that [v] satisfies the specification [φ];
   - the original goal,
     generalized under the form [∀ v, φ v → ...],
     which means that [v] becomes an opaque value
     about which nothing is known except that [φ v] holds. *)

(* One should avoid [context] in the following tactic, as it might match an
   occurence that is in the postcondition. *)
Ltac wp_specify x φ :=
  lazymatch goal with
  | |- environments.envs_entails
         _ $
         wp _ _ (ret_concat ?δ _) _ => (* TODO missing [bind] *)
      let o := eval cbn in (lookup_name δ x) in
        match o with
        | ret ?v => let H := iFresh in
                    iAssert (φ v) as H; [  | iRevert H; generalize v ]
        end
  | |- environments.envs_entails
         _ $
         wp _ _ (ret_dconcat ?δ _) _ => (* TODO missing [bind] *)
      let o := eval cbn in (lookup_name δ x) in
        match o with
        | ret ?v => let H := iFresh in
                    iAssert (φ v) as H; [  | iRevert H; generalize v ]
        end
  end.

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
  let i1 := string_to_ident n1 in
  let i1 := fresh i1 in
  oSpecify n1 spec1 i1 H1.
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2) :=
  let i1 := string_to_ident n1 in let i1 := fresh i1 in
  let i2 := string_to_ident n2 in let i2 := fresh i2 in
  oSpecify n1 spec1 i1 H1
           n2 spec2 i2 H2.
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2)
       constr(n3) constr(spec3) constr(H3) :=
  let i1 := string_to_ident n1 in let i1 := fresh i1 in
  let i2 := string_to_ident n2 in let i2 := fresh i2 in
  let i3 := string_to_ident n3 in let i3 := fresh i3 in
  oSpecify n1 spec1 i1 H1 n2 spec2 i2 H2 n3 spec3 i3 H3.
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2)
       constr(n3) constr(spec3) constr(H3)
       constr(n4) constr(spec4) constr(H4) :=
  let i1 := string_to_ident n1 in let i1 := fresh i1 in
  let i2 := string_to_ident n2 in let i2 := fresh i2 in
  let i3 := string_to_ident n3 in let i3 := fresh i3 in
  let i4 := string_to_ident n4 in let i4 := fresh i4 in
  oSpecify n1 spec1 i1 H1 n2 spec2 i2 H2 n3 spec3 i3 H3 n4 spec4 i4 H4.
