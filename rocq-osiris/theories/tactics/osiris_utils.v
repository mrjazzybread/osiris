From Ltac2 Require Import Ltac2 Printf.
From osiris.tactics Require Export utils iris_bindings.
From osiris.program_logic Require Import program_logic.
From stdpp Require Import strings.

Ltac2 get_expr () :=
  let g := get_iris_goal () in
  lazy_match! g with
  | impure _ (eval _ ?e) ?_Ψ ?_ζ ?_Φ => e
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected goal of the form [imp (eval η e) _]")))
  end.

Ltac2 simple_intros () :=
  cbv beta;
  let g := get_iris_goal () in
  let rec go g :=
    lazy_match! g with
    | bi_later ?prop =>
        iIntros "!>";
        go prop
    | bi_forall ?prop =>
        match Constr.Unsafe.kind prop with
        | Constr.Unsafe.Lambda _ prop =>
            iIntros "%";
            go prop
        | _ => Control.zero (Tactic_failure None)
        end
    | bi_wand (bi_pure (_ = _)) ?prop =>
        iIntros "->";
        go prop
    | bi_wand _ ?prop =>
        let h := iFresh in
        iIntros $h; go prop; iRevert $h
    | _ => ()
    end
  in
  go g.
Tactic Notation "simple_intros" := ltac2:(simple_intros ()).
