Require Import monads lang free eval spec handle.

(* Instantiate the generic [handle] with the [spec] monad. *)

Definition wp η e φ :=
  run η e ∋ φ.
