(* The empty type and its elimination form. *)

Definition void : Type := Empty_set.

Definition elim_void {A} (v : void) : A :=
  match v with end.

Ltac elim_void e :=
  exfalso; exact (elim_void e).
