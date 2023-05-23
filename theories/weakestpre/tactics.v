From iris.proofmode Require Import classes proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics specifications.


(* -------------------------------------------------------------------------- *)

(* Simplification tactics. *)

(* TODO in all of the tactics below, avoid using repeated underscores
        _ _ _ _
   This style is fragile and will silently break when a constructor or
   lemma receives one more argument. *)

(* [simp] proves a goal of the form [simp _ _]. *)
Ltac simp :=
  lazymatch goal with
  | |- simp ?m _ =>
      lazymatch m with
      (* [Par]-related cases. *)
      | Par ?m1 ?m2 ?k ?ko =>
          (* Choose the simplification lemma depending on the presence of
             [Ret]s in the branches of [Par]. *)
          lazymatch m1 with
          | Ret ?v1 =>
              match m2 with
              | Ret ?v2 =>
                  exact (simp_par_ret_ret v1 v2 k)
              | _ =>
                  simple notypeclasses refine
                         (SimpTransitive (Par (Ret v1) m2 k ko) _ _ _ _) ;
                  [ (* ?m2 *) | (* ?m3 *)
                  | (* [simp m1 m2] *) exact (SimpParRetLeft v1 m2 k)
                  | (* [simp m2 m3] *)
                    cbn; (* Simplify the bind. *)
                    by simp (* Try to simplify the result. *) ]
              end
          | _ =>
              lazymatch m2 with
              | Ret ?v2 =>
                  simple notypeclasses refine
                         (SimpTransitive (Par m1 (Ret v2) k ko) _ _ _ _) ;
                  [ (* ?m2 *) | (* ?m3 *)
                  | (* [simp m1 m2] *) exact (SimpParRetLeft m1 v2 k)
                  | (* [simp m2 m3] *)
                    cbn; (* Simplify the bind. *)
                    by simp (* Try to simplify the result. *) ]
              | _ =>
                  (* [simp (Par m1 m2 k ko) (Par m1' m2' k ko)]
                     The simplification of a [Par] cannot go any further using
                     the transitivity of [simp], as one cannot check for
                     progress. *)
                  by simple notypeclasses refine (SimpPar m1 _ m2 _ k ko _ _) ;
                  [ (* m1' *) | (* m2' *)
                  | (* [simp m1 m1'] *) by simp
                  | (* [simp m2 m2'] *) by simp ]
              end
          end

      (* [Stop]-related cases. *)
      | Stop CFlip ?x ?k =>
          (* Either : apply [SimpFlip] works and ends the proof search,
               or stop simplifying the term. *)
          first [ simple notypeclasses refine (SimpFlip x k _ _ _);
                  [ (* [m'] *)
                  | (* [simp (k true) m'] *) by simp
                  | (* [simp (k false) m'] *) by simp ]
                | exact (SimpReflexive m) ]
      | Stop CEval (pair ?η ?e) ?k =>
          simple notypeclasses refine (SimpEval η e k);
          cbn; (* Simplify the bind. *)
          simp (* Try to simplify the result. *)

      | Stop CLoop (pair (pair (pair (pair ?η ?x) ?i1) ?i2) ?e) ?k =>
          simple notypeclasses refine (SimpLoop η x i1 i2 e k)

      | _ => exact (SimpReflexive m)
      end
  | |- _ => fail "The goal is not of the form [simp _ _]"
  end.



(* [wp_simp] simplifies [m] in a goal of the form [WP m @ _; _ {{ _ }}]. *)
Ltac wp_simp :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp ?s ?E ?m ?φ) =>
      tac_change_goal (wp_simp m _ s E φ _);
      [ | simp | ]
  end.



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
 *)

Ltac wp_step :=
  (* The lazymatch stills misses a few cases and should be completed. *)
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ret _) _) =>
      tac_change_goal (wp_ret _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      tac_change_goal (wp_bind _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) (ret _) _ _) _) =>
      tac_change_goal (wp_par_ret_ret _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par _ (ret _) ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_right _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) _ ?k ?ko) _) =>
      tac_change_goal (wp_par_ret_left _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (stop CEval _) _) =>
      first [ tac_change_goal (wp_eval_ret _ _ _ _ _)
            | tac_change_goal (wp_eval _ _ _ _ _ _) ]
  | |- environments.envs_entails _ (wp _ _ (Stop CFlip _ _) _) =>
      tac_change_goal (wp_flip _ _ _ _ _)
  end; repeat wp_simp.

Ltac wp :=
  iStartProof;
  cbn; (* TODO: better control the reduction strategy. *)
  (repeat
     (lazymatch goal with
        | |- environments.envs_entails _ (bi_later _) => iNext
        | _ => wp_step; try progress cbn
        end || apply tc_change_goal)).

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

Global Opaque call.
Ltac wp_call :=
  with_strategy transparent [call] unfold call; wp.


(* TODO not great *)
Ltac wp_set_postcondition :=
  match goal with
    |- @environments.envs_entails _ _
        (?φ ?v) =>
      is_evar φ;
      instantiate (1 := (λ w, ⌜w = v⌝)%I)
  end.


Ltac wp_alloc l H:=
  iApply wp_alloc; iNext; iIntros (l) H; wp.
Ltac wp_load H :=
  iApply (wp_load with H); iNext; iIntros H; wp.
Ltac wp_store H :=
  iApply (wp_store with H); iNext; iIntros H; wp.



(* -------------------------------------------------------------------------- *)

(* Do not allow [concatenating] to be unfolded. We want symbolic execution
   to stop at [concatenating], that is, when the environment is extended
   with new bindings. This gives the user a chance to prove specifications
   about these bindings using [wp_specify]. *)

Global Opaque concatenating.
Global Opaque dconcatenating.

(* The tactic [wp_continue] expands away [concatenating] and invokes [wp]
   to continue simplifying the goal. *)

Lemma concatenating_def eval η e δ :
  concatenating eval η e δ =
  let η := concat δ η in eval η e.
Proof.
  reflexivity.
Qed.

Lemma dconcatenating_def {A} δ ηδ (k: envs → A) :
  dconcatenating δ ηδ k =
  k (dconcat δ ηδ).
Proof.
  reflexivity.
Qed.

(* One should avoid [context] in the following tactic, as it might match an
   occurence that is in the postcondition. *)
Ltac wp_continue :=
  lazymatch goal with
  | |- environments.envs_entails
         _ $
         wp _ _ (concatenating eval _ _ ?δ) _ => rewrite concatenating_def
  | |- environments.envs_entails
         _ $
         wp _ _ (dconcatenating ?δ _ _) _ => rewrite dconcatenating_def
  end; wp.

Ltac wp_autocontinue :=
  repeat (wp || wp_continue).


(* The tactic [wp_specify x φ H] should be used when the goal begins with
   [concatenating eval η e δ], that is, when the environment is about to
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
         wp _ _ (concatenating eval _ _ ?δ) _ =>
      let o := eval cbn in (lookup_name δ x) in
        match o with
        | ret ?v => let H := iFresh in
                    iAssert (φ v) as H; [  | iRevert H; generalize v ]
        end
  | |- environments.envs_entails
         _ $
         wp _ _ (dconcatenating ?δ _ _) _ =>
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
