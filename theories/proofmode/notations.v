From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.
From osiris.semantics Require Import semantics.
From osiris.lang Require Import lang.
From osiris.proofmode Require Import specifications.

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
Notation "'WP'  'Par' m m' '...' @ s ; E {{ φ }}" :=
  (wp s E (Par m m' _ _) φ)
    (only printing).

Notation "'WP'  'focus'  m  {{ φ }}" :=
  (wp _ _ (bind m _) φ)
  (only printing).

Notation "'The'  'following'  'environment'  (
 * x ;
 * .. ;
 * z )  'is'  'about'  'to'  'be'  'added.'" :=
  (wp _ _ (ret_concat (EnvCons x _ (.. (EnvCons z _ EnvNil) ..)) _) _)
  (only printing).

Notation "'The'  'following'  '(d)environment'   (
 * x ;
 * .. ;
 * z )  'is'  'about'  'to'  'be'  'added.'" :=
  (wp _ _ (ret_dconcat (EnvCons x _ (.. (EnvCons z _ EnvNil) ..)) _) _)
  (only printing).

(* -------------------------------------------------------------------------- *)

(* Notations for ad-hoc lists: they are all printed as normal lists. *)

(* Notation "'[ x : v ; .. ; z : w ]" :=
  (EnvCons x v (.. (EnvCons z w EnvNil) ..))
    (only printing). *)

Notation "[
 * x ;
 * .. ;
 * z ]" :=
  (RecBiCons x (.. (RecBiCons z RecBiNil) ..))
  (only printing).

Notation "[
 * x ;
 * .. ;
 * z ]" :=
  (BiCons x (.. (BiCons z BiNil) ..))
  (only printing).

Notation "[
 * x ;
 * .. ;
 * z ]" :=
  (ICons x (.. (ICons z INil) ..))
  (only printing).

Notation "[
 * x ;
 * .. ;
 * z ]" :=
  (BrCons x (.. (BrCons z BrNil) ..))
  (only printing).

Notation "'<v' v1 ; .. ; vn 'v>'" :=
  (VTuple (VCons v1 (.. (VCons vn VNil) ..))).

(* -------------------------------------------------------------------------- *)

(* Notation for iterated unary constructors. *)

(* Unfortunately, adding parentheses does not work. *)
Notation "'data:(' C1  $  ..  $  Cn  $  i ')'" :=
  (VData C1 <v .. (VData Cn (<v VConstant i v>)) .. v>).

(* With the above notation,
     [VData "S" (VTuple1 (VData "S" (VTuple1 (VData "S" (VTuple1 (
      VData "S" (VTuple1 (VConstant "O"))))))))]
   can simply be written [data:( "S" $ "S" $ "S" $ "S" $ "O")]. *)

(* -------------------------------------------------------------------------- *)

(* On modules. *)

(* [val_as_struct_total] is introduced by Osiris tactics when the evaluation
   function wants to extract the underlying environment of a value which we know
   define a module. Thus, it can be saftely hidden. *)
Notation "v" :=
  (val_as_struct_total _ v)
  (only printing, at level 101).

(* The following notation represents paths: [M :$: f] is the osiris equivalent
   to the OCaml [M.f] *)
Notation "v  ':$:'  n" :=
  (lookup_name_total (val_as_struct_total v) n)
  (only printing, at level 100).
