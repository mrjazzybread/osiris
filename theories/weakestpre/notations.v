From iris.bi Require Import weakestpre.
From osiris.semantics Require Import free eval.


(* -------------------------------------------------------------------------- *)
(* Notations used to handle n-ary calls. *)
Notation "'WP'  'call' f v1 v2 .. vn @ s ; E {{ ϕ }}" :=
  (wp s E (call f v1) (fun v => wp s E (call v v2) (.. (fun v =>  wp s E (call v vn) ϕ ) ..)))
    (only printing).



(* -------------------------------------------------------------------------- *)
(* Notations to hide some continuations. *)
Notation "'WP' Par m m' '...' @ s ; E {{ ϕ }}" :=
  (wp s E (Par m m' _ _) ϕ)
    (only printing).
