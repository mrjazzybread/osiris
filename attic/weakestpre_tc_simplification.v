From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics specifications.



(* -------------------------------------------------------------------------- *)

(* This Section defines classes to simplify the goal. *)

Section TypeclassesDefinitions.
  Context `{!osirisGS_gen hlc Σ}.

  (* [TC_change_goal] can either be used to simplify the goal
     (Cf. [inst_TCsimp_change_goal]) or to help with automation (Cf. the section
     [Specifications]. *)
  Class TC_change_goal (P Q: iProp Σ) Δ :=
    tc_change_goal : environments.envs_entails Δ P →
                     environments.envs_entails Δ Q.

End TypeclassesDefinitions.
