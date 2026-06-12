From Ltac2 Require Import Ltac2 Printf.
From osiris.utils Require Export tactics.
Require Import ewp.
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

(** *Set postcondition *)

(* Force a postcondition, for example when the postcondition is an evar and one
   wants to perform an induction *)
Ltac2 set_postcondition_tac (φ : constr) : unit :=
  lazy_match! strip_laters (get_iris_goal ()) with
  | impure ?_e ?_m ?_Ψ ?_ζ ?Φ =>
      Std.unify Φ φ
  | _ => Control.zero
           (Tactic_failure (Some (Message.of_string "Expected goal of the form [imp m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}]")))
  end.
Ltac2 Notation "set_postcondition" φ(open_constr) := set_postcondition_tac φ.
Tactic Notation "set_postcondition" open_constr(φ) :=
  let tac := ltac2:(φ |- set_postcondition_tac (Option.get (Ltac1.to_constr φ))) in
  tac φ.
