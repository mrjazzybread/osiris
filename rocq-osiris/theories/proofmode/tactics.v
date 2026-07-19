From osiris.utils Require Import tactics.
From osiris.lang Require Import encode type_nel constructors.
From osiris.program_logic Require Import program_logic.

From stdpp Require Import strings.
From Ltac2 Require Import Ltac2 Printf.

Ltac2 determine_Constant_instance (c : constr) (b : constr) : constr :=
  if Constr.equal b 'val then '(Constant_val $c) else
  if Bool.neg (Constr.is_evar b) then constr:((_ : Constant $c $b)) else
  match class_solutions 2 (fun t => open_constr:(Constant $c $t)) with
  | [] =>
        Control.zero
          (Tactic_failure
             (Some (fprintf
                "No [Constant %t _] instance could be inferred; provide the type explicitly" c)))
  | [a] => constr:((_ : Constant $c $a))
  | sols =>
        let msg :=
          List.fold_left
            (fun msg s => Message.concat msg (fprintf " %t" s))
            (fprintf "Several types have a [Constant %t _] instance; provide the type explicitly. Candidates include:" c)
            sols
        in
        Control.zero (Tactic_failure (Some msg))
  end.
