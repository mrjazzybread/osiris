From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.
From osiris.semantics Require Import semantics.
From osiris.lang Require Import lang.

(* ------------------------------------------------------------------------ *)

(* Store-related notations. *)

Notation "l ↦ v" :=
  (mapsto l (DfracOwn 1) v) (at level 20).

(* -------------------------------------------------------------------------- *)
(* Notations used to handle n-ary calls. *)
Notation "'WP'  'calln' f v1 v2 .. vn @ s ; E {{ φ }}" :=
  (wp s E (call f v1)
      (fun v => wp s E (call v v2)
                   (.. (fun v =>  wp s E (call v vn) φ ) ..)))
  (only printing).



(* -------------------------------------------------------------------------- *)
(* Notations to hide some continuations. *)
Notation "'WP' Par m m' '...' @ s ; E {{ φ }}" :=
  (wp s E (Par m m' _ _) φ)
  (only printing).

Notation "'The'  'following'  'environment'  (  η  )  'is'  'about'  'to'  'be'  'added.'" :=
  (wp _ _ (dconcatenating η _) _)
  (only printing).

  Notation "'The'  'following'  (  δ  ':='  v  )
'is'  'about'  'to'  'be'  'added'  'to'  'the'  'environment.'" :=
    (wp _ _ (concatenating _ _ δ v) _)
    (only printing).

  Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
    (EnvCons x _ (.. (EnvCons z _ EnvNil) ..))
    (only printing).
