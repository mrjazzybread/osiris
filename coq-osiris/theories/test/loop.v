From osiris Require Import osiris.

(* #[global] Hint Extern 0 (VClo _ _ _ = # _) => eapply solve_encode_val :  encode. *)


Goal ∃ (X : Type) (H : Encode X) (y : X),
    VTuple [ #0; #0] = #y.
  
  eexists _, _, _; eauto using eq_refl with encode nocore.
Admitted.

Global Remove Hints f_equal_nat Logic.eq : core.
Goal ∃ (X : Type) (H : Encode X) (y : X),
    VTuple [VClo [] (Anon ("y" => EPath ["y"])); #0] = #y.
(* Goal ∃ (X : Type) (H : Encode X) (y : X), VTuple [ #0; #0] = #y. *)
  (* Typeclasses eauto := 2. *)
  (* Typeclasses eauto := debug. *)
  (* Print Instances Encode. *)
  eexists _, _, _.
  (* Print HintDb core. *)
  (* eapply solve_encode_tuple2. all : eauto with encode. *)
  eauto with encode nocore.
  (* Timeout 10 debug eauto with encode. *)
  (* Print Hint *. *)

  (* For Logic.eq we have too many hints  *)
Admitted.
Goal ∃ (X : Type) (H : Encode X) (y : X),
    VTuple [ #0; #0] = #y.
  eexists _, _, _.
  eauto with encode core.
  Print HintDb encode.
  (* eapply solve_encode_tuple2; auto. *)
  (* eauto with encode. *)

  (* simple eapply solve_encode_val; auto. *)

  (* (* Set Typeclasses Debug. *) *)
  (* (* Set Typeclasses Debug Verbosity 2. *) *)
  (* (* (* typeclasses eauto bfs. *) *) *)
  (* (* Set Typeclasses Iterative Deepening. *) *)
  (* (* Unshelve. *) *)
  (* (* Typeclasses eauto := debug (dfs) 3. *) *)
  (* eauto 20 with encode. *)
(* Qed. *)
Admitted.
