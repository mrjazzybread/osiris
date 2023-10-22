From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.
From osiris Require Import base.
From osiris.semantics Require Import semantics.
From osiris.lang Require Import lang.
From osiris.proofmode Require Import specifications.

(* Cf.
   https://coq.inria.fr/doc/V8.10.2/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations
   for information on notation formatting. *)


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
(* Specific cases of the weakest precondition assertions. *)

(* [WP Par m1 m2 k ko @s; E {{ φ }}] is printed as follows (if breaking lines is
   required):
   [ WP Par
         ( m1 )
         ( m2 )
         ...continuations @ s; E
         {{ φ }} ] *)
Notation "'WP' 'Par' '(' m1 ')' '(' m2 ')' '...continuations' '@' s ';' E '{{' φ '}}'" :=
  (wp s E (Par m1 m2 _ _) φ)
    (only printing, format
    "'[v    ' 'WP'  'Par' '/' '(' m1 ')' '/' '(' m2 ')' '/'  '...continuations'  '@' s ';'  E '/'  '{{'  φ  '}}' ']'").


(* [WP (bind m k) @s; E {{ φ }}] is printed as follows (if breaking lines is
   required):
   [ WP focus
         m1
         ...continuation
         {{ φ }} ]
  Note that [s] and [E] should not be required before the evaluation of
  [bind]. This explains why they are hidden. *)
Notation "'WP' 'focus' m '...continuation' {{ φ }}" :=
  (wp _ _ (bind m _) φ)
    (only printing,
       format "'WP'  '[v  ' 'focus'  m  '//' '...continuation'  '//' {{  '[v ' φ ']'  }} ']'").

Notation "'WP' e {{ v , ... } }" :=
  (wp NotStuck ⊤ e%E (λ v, wp _ _ _ _))
    (at level 20, e at level 200,
       only printing,
       format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' '...'  ']' } } ']'") : bi_scope.


(* -------------------------------------------------------------------------- *)
(* Environment-related rules. *)

(* Environments are associative lists.
   They are written as:
   - [name1 ~> value1 ;
      ... ;
      namen ~> valuen] if line-breaking is necessary,
   - [name1 ~> value1; ...; namen ~> valuen] otherwise. *)

Notation "n1 ~> v1 ; η" :=
  (EnvCons n1 v1 η) (at level 80, right associativity, format "n1  ~>  v1 ;  '/' η").

(* Recursive bindings are not exactly printed as environments. Thay are a
   list. Hints are provided to break lines between two elements. *)
Notation "[ x ; .. ; z ]" :=
  (RecBiCons x (.. (RecBiCons z RecBiNil) ..))
    (only printing,
       format "[  '[v' x ;  '/' .. ;  '/' z ']' ]").

Notation "x  '≈>'  f" :=
  (RecBinding x f)
    (only printing, at level 100, no associativity).

Notation "'An' 'environment' 'containing' n1 , .. , nn 'will' 'be' 'added' 'to' 'the' 'current' 'environment.'" :=
  (ret_dconcat
     (n1 ~> _ ; (.. (nn ~> _ ; EnvNil) ..))
     (_, _))
    (only printing, format
"'[v    ' 'An'  'environment'  'containing'  '/' n1 ,  '/' .. ,  '/' nn  '/' 'will'  'be'  'added'  'to'  'the'  'current'  'environment.' ']'").

Infix ":::" := (concat).

(* -------------------------------------------------------------------------- *)
(* Closures. *)

(* Closures capture an environment. We rely on the above pretty-printing rules
   for environments. Closures are delimitted by [closure:( ... )].
   [VClo η f] is written
   [closure:(
        {: η :}
        f )]. *)
Notation "'closure:(' {: η :} f ')'" :=
  (VClo η f)
  (format "'[v    ' 'closure:(' '/' '[v   ' '{:'  η  ':}' ']'  '/' f  ')' ']'").


Notation "'rec-closure:(' {: η :} rbds x ')'" :=
  (VCloRec η rbds x)
    (format
       "'[v    ' 'rec-closure:(' '/' '[v   ' {:  η  :} ']' '/' rbds '/'  x  ')' ']'").

Notation "'λ:(' x , e )" :=
  (AnonFun x e)
    (format "'λ:(' x ',' '//'    '[v' e ']' ')'").

Notation "'λ:(' '()' , e )" :=
  (AnonFun "__osiris_anonymous_arg" e)
    (format "'λ:('  '()'  ',' '//'    '[v' e ']' ')'").

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* OCaml Expressions. *)



Notation "'begin' 'if' econd 'then' ethen 'else' eelse 'end' " :=
  (EIfThenElse econd ethen eelse)
    (format "'[v' '[v  ' 'begin' '//' '[v' 'if'  '[v  ' econd ']'  '/' 'then'  '[v  ' ethen ']' '/' 'else'  '[v  ' eelse ']' ']' ']' '/' 'end' ']'",
       only printing).

Notation "( e1 e2 )" := (EApp e1 e2) (only printing).



(* Pattern matching. *)

Notation "'match:(' x 'with' pats )" :=
  (EMatch x pats)
    (only printing,
       no associativity,
         format "'[v' 'match:('  x  'with' '//' pats ']' ')'").

Notation "'|' pat '=>' e others" :=
  (BrCons (Branch pat e) others)
    (at level 80,
       others at level 81,
         only printing,
           format "'[hv' '|'  '[v  ' pat  '=>' '//' e ']' '//' others ']'").

Notation "'end'" := (BrNil) (only printing).


(* Paths. *)
Notation "'path:(' x1 ')'" := (PathBase x1).
Notation "'path:(' x1 '.' .. '.' xn '.' xm ')'" :=
  (PathDot (.. (PathDot (PathBase xm) xn) ..) x1)
    (x1, xn, xm at level 200,
       format "'path:(' x1 '/' '.' .. '/' '.' xn '.' '/' xm )").

Notation "'epath:(' x1 '.' .. '.' xn '.' xm ')'" :=
  (EPath (PathDot (.. (PathDot (PathBase xm) xn) ..) x1))
    (format "'epath:(' x1 '/' '.' .. '/' '.' xn '/' '.' xm ')'").
Notation "'epath:(' x1 ')'" := (EPath (PathBase x1)).

(* ADTs. *)
Notation "'emktpl:(' e1 ',' .. ',' en ')'" :=
  (EMkTuple (cons e1 (.. (cons en nil) .. )))
    (format "'emktpl:(' e1 ','  '/' .. ','  '/' en ')'").

Notation "'edata:(' n '(...)' ')'" :=
  (EData n _)
    (only printing).

(* -------------------------------------------------------------------------- *)

(* Values often contain lists. *)

(* Only the name of the symbols are important in module-values.
Notation "struct:( i1 ; .. ; im )" :=
  (VStruct (EnvCons i1 _ ( .. ( EnvCons im _ EnvNil ) .. ) ))
  (only printing, format
   "'[v     ' 'struct:(' i1 ';' '/' .. ';' '/' im ')' ']'"). *)
(* Tuples. *)
Notation "'<v' v1 ; .. ; vn 'v>'" :=
  (VTuple (VCons v1 (.. (VCons vn VNil) ..))).

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* Notation for iterated unary constructors. *)

(* Unfortunately, adding parentheses does not work. *)
Notation "'data:(' C1  $  ..  $  Cn  $  i ')'" :=
  (VData C1 <v .. (VData Cn (<v VConstant i v>)) .. v>).

(* With the above notation,
     [VData "S" (VTuple1 (VData "S" (VTuple1 (VData "S" (VTuple1 (
      VData "S" (VTuple1 (VConstant "O"))))))))]
   can simply be written [data:( "S" $ "S" $ "S" $ "S" $ "O")]. *)

(* ------------------------------------------------------------------------- *)

(* On modules. *)

(* [val_as_struct_total] is introduced by Osiris tactics when the evaluation
   function wants to extract the underlying environment of a value which we know
   define a module. Thus, it can be saftely hidden. *)
Notation "« v »" :=
  (val_as_struct_total _ v)
  (only printing, at level 101).

(* The following notation represents paths: [M :$: f] is the osiris equivalent
   to the OCaml [M.f] *)
Notation "v  ':$:'  n" :=
  (lookup_name_total (val_as_struct_total v) n)
  (only printing, at level 100).

(* ------------------------------------------------------------------------- *)

(* On loops *)
