Require Import monads lang free eval spec handle.

(* Instantiate the generic [handle] with the [spec] monad. *)

Definition wp η e φ :=
  run η e ∋ φ.

Ltac wp :=
  (* Expose [handle (eval η e)] in the goal. *)
  unfold wp, run;
  (* Unfold the outer iteration in the loop. *)
  rewrite handle_fixed_point;
  (* Let Coq compute! *)
  cbv.
