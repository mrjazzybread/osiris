From Ltac2 Require Import Ltac2 Printf.

(* [all] takes a tactic and applies it to all subgoals. *)

Ltac2 all (tac : unit -> unit) :=
  Control.extend [] tac [].

(* [lastn] applies a list of tactics to the last subgoals (one tactic per subgoal). *)

Ltac2 lastn tacs := Control.extend [] (fun _ => ()) tacs.

(* [last] applies a tactic to the last subgoal. *)

Ltac2 last tac := lastn [tac].

(* [firstn] applies a list of tactics to the first subgoals (one tactic per subgoal). *)

Ltac2 firstn tacs := Control.extend tacs (fun _ => ()) [].

(* [first] applies a tactic to the first subgoal. *)

Ltac2 first tac := firstn [tac].

(* [try_complete] takes a tactic and either
   solves the goal by running it or does nothing. *)

Ltac2 try_complete (tac : unit -> unit) :=
  Control.plus (fun _ => complete tac) (fun _ => ()).

(* [class_solutions limit mk] enumerates the instantiations of [?A] for
   which the class goal [mk ?A] is inhabited. Enumeration stops after
   [limit] distinct solutions. *)

Ltac2 rec collect_successes (limit : int) (acc : constr list Ref.ref) (t : constr)
                            (tac : unit -> unit) : unit :=
  match Control.case tac with
  | Val (_, k) =>
      let sol := (eval cbv in $t) in
      (if List.exist (fun s => Constr.equal s sol) (Ref.get acc) then ()
       else Ref.set acc (sol :: Ref.get acc));
      if Int.le limit (List.length (Ref.get acc)) then ()
      else collect_successes limit acc t (fun () => k (Tactic_failure None))
  | Err _ => ()
  end.

Ltac2 class_solutions (limit : int) (mk : constr -> constr) : constr list :=
  let acc := Ref.ref [] in
  (* Instance resolution only backtracks when it is run as a *tactic*
     (term elaboration commits to the first solution), so we open a
     throwaway goal and collect the successes of [typeclasses eauto] on
     it. The results escape through a [Ref] cell, which backtracking does
     not roll back. *)
  Control.plus
    (fun () =>
       (* Open a goal of the form [mk ?t]. *)
       let t := open_constr:(_ : Type) in
       Std.assert (Std.AssertType None (mk t) None);
       (* Collect the successes of [typeclasses_eauto] on that goal. *)
       Control.focus 1 1 (fun () =>
         collect_successes limit acc t (fun () => typeclasses_eauto));
       Control.zero (Tactic_failure None))
    (fun _ => ());
  List.rev (Ref.get acc).
