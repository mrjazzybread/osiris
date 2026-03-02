From Ltac2 Require Import Ltac2 Printf.

(* [all] takes a tactic and applies it to all subgoals. *)

Ltac2 all (tac : unit -> unit) :=
  Control.extend [] tac [].

(* [last] applies a tactic to the last subgoal. *)

Ltac2 last tac := Control.extend [] (fun _ => ()) [tac].

(* [first] applies a tactic to the first subgoal. *)

Ltac2 first tac := Control.extend [tac] (fun _ => ()) [].

(* [try_complete] takes a tactic and either
   solves the goal by running it or does nothing. *)

Ltac2 try_complete (tac : unit -> unit) :=
  Control.plus (fun _ => complete tac) (fun _ => ()).

From iris Require Import base environments.
From stdpp Require Import stringmap.

(* [get_iris_goal] returns the current iris goal. *)

Ltac2 get_iris_goal () :=
  lazy_match! goal with
  | [ |- envs_entails ?_envs ?goal ] => goal
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "Expected an iris goal")))
  end.

(* [get_iris_hyps] returns a tuple of iris environments [(Δi, Δs)], where
   [Δi] is the intuitionistic environment, and
   [Δs] is the spatial environment. *)

Ltac2 get_iris_hyps () :=
  lazy_match! goal with
  | [ |- envs_entails ?envs ?_goal ] =>
      match! envs with
      | (Envs ?Δi ?Δs _) => (Δi, Δs)
      end
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "Expected an iris goal")))
  end.

(* [idents_to_strings Δ] takes a list of iris hypothesis identifiers, and returns
   the list of names of those hypotheses. *)

Fixpoint idents_to_strings (Δ : list ident) : list string :=
  match Δ with
  | [] => []
  | (IAnon _ :: Δ) => idents_to_strings Δ
  | (INamed s :: Δ) => s :: idents_to_strings Δ
  end.

(* Takes a Rocq string as a base, returns a Rocq string that does not
   clash with any name of a current iris hypothesis. *)

Ltac2 iFresh' (h : constr) :=
  lazy_match! goal with
  | [ |- envs_entails ?Δ _ ] =>
      let hs := eval cbv in (idents_to_strings (envs_dom $Δ)) in
        eval vm_compute in (fresh_string_of_set $h (list_to_set $hs))
  end.

Ltac2 Notation "iFresh" := iFresh' '"~".
Ltac2 Notation "iFresh" h(constr) := iFresh' h.

(* Given a constr of the form [▷^n c] (where [n] might equal 0),
   [strip_laters] returns [c]. *)

Ltac2 rec strip_laters (g : constr) :=
  lazy_match! g with
  | bi_later ?c => strip_laters c
  | _ => g
  end.

(* Check if the spatial environment is empty. *)

Ltac2 empty_spatial_env () :=
  let (_, Δs) := get_iris_hyps () in
  match! Δs with
  | Enil => true
  | _ => false
  end.
