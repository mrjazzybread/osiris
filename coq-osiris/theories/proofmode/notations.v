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

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.

Notation "- e" := (EIntNeg e) : expr_scope.
Infix "+" := EIntAdd : expr_scope.
Infix "-" := EIntSub : expr_scope.
Infix "*" := EIntMul : expr_scope.
Infix "&&" := EBoolConj : expr_scope.
Infix "||" := EBoolDisj : expr_scope.

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

(* [WP Par m1 m2 k z @s; E {{ φ }}] is printed as follows (if breaking lines is
   required):
   [ WP Par
         ( m1 )
         ( m2 )
         ...continuations @ s; E
         {{ φ }} ] *)
Notation "'WP' 'Par' '(' m1 ')' '(' m2 ')' '...continuations' '@' s ';' E '{{' φ '}}'" :=
  (wp s E (Par m1 m2 _ _) φ)
    (only printing, format
    "'[hv    ' 'WP'  'Par' '/' '(' m1 ')' '/' '(' m2 ')' '/'  '...continuations'  '@' s ';'  E '/'  '{{'  φ  '}}' ']'").


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
       format "[  '[hv' x ;  '/' .. ;  '/' z ']' ]").

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
(* Paths, tuples and ADTs. *)


Notation "'Path' x1" :=
  (PathBase x1)
    (at level 90,
      format "'Path'  x1").

Notation "'Path' x1 '.' .. '.' xn '.' xm" :=
  (PathDot (.. (PathDot (PathBase xm) xn) ..) x1)
    (at level 200,
       format "'Path'  x1 '/' '.' .. '/' '.' xn '.' '/' xm").

Notation "'EPath' x1" :=
  (EPath (PathBase x1))
    (at level 90,
      only printing,
        format "'EPath'  x1").

Notation "'EPath' x1 '.' .. '.' xn '.' xm ')'" :=
  (EPath (PathDot (.. (PathDot (PathBase xm) xn) ..) x1))
    (x1, xn, xm at level 200,
      only printing,
        format "'EPath'  x1 '/' '.' .. '/' '.' xn '/' '.' xm ')'").

Notation "'<e' e1 , .. , en 'e>'" :=
  (ETuple (ECons e1 .. (ECons en ENil) ..))
    (format "'<e'  e1 ,  '/' .. ,  '/' en  'e>'").

Notation "'<v' v1 , .. , vn 'v>'" :=
  (VTuple (VCons v1 .. (VCons vn VNil) ..))
    (format "'<v'  v1 ,  '/' .. ,  '/' vn  'v>'").

Notation "'<p' p1 , .. , pn 'p>'" :=
  (PTuple (PCons p1 .. (PCons pn PNil) ..))
    (format "'<p'  p1 ,  '/' .. ,  '/' pn  'p>'").


Notation "'edata:(' C1 $ .. $ Cn $ argn ')'" :=
  (EData C1 <e .. (EData  Cn <e argn e>) .. e>).
Notation "C ( e1 , .. , en )" :=
  (EData C (ETuple (ECons e1 (.. (ECons en ENil) ..))))
    (only printing, at level 20).

Notation "'vdata:(' C1 $ .. $ Cn $ argn ')'" :=
  (VData C1 <v .. (VData  Cn <v argn v>) .. v>).
Notation "C ( v1 , .. , vn )" :=
  (VData C (VTuple (VCons v1 (.. (VCons vn VNil) ..))))
    (only printing, at level 20).

Notation "'pdata:(' C1 $ .. $ Cn $ argn ')'" :=
  (PData C1 <p .. (PData  Cn <p argn p>) .. p>).
Notation "C ( p1 , .. , pn )" :=
  (PData C (PTuple (PCons p1 (.. (PCons pn PNil) ..))))
    (only printing, at level 20).

(* -------------------------------------------------------------------------- *)
(* Closures. *)

(* Closures capture an environment. We rely on the above pretty-printing rules
   for environments. Closures are delimitted by [closure:( ... )].
   [VClo η f] is written
   [closure:(
        {: η :}
        f )]. *)
Notation "'closure:(' η f ')'" :=
  (VClo η f)
  (format "'[v    ' 'closure:(' '/' '[hv   '  η  ']'  '/' f  ')' ']'").


Notation "'rec-closure:(' η rbds x ')'" :=
  (VCloRec η rbds x)
    (format
       "'[v    ' 'rec-closure:(' '/' '[hv'     η   ']' '/' rbds '/'  x  ')' ']'").

Notation "'λ:(' x , e )" :=
  (AnonFun x e)
    (format "'λ:(' x ',' '/'    '[hv' e ']' ')'").

Notation "'λ:(' '_' , e )" :=
  (AnonFun "__osiris_anonymous_arg" e)
    (format "'λ:('  '_'  ',' '/'    '[hv' e ']' ')'").

Notation "'eλ:(' x , e )" :=
  (EAnonFun (AnonFun x e))
    (format "'eλ:(' x ',' '/'    '[hv' e ']' ')'").

Notation "'eλ:(' '_' , e )" :=
  (EAnonFun (AnonFun "__osiris_anonymous_arg" e))
    (format "'eλ:('  '_'  ',' '/'    '[hv' e ']' ')'").

Notation "'_'" := (EPath "__osiris_anonymous_arg") (only printing).

Notation "( e1 )  ( e2 )" := (EApp e1 e2) (only printing).

(* -------------------------------------------------------------------------- *)
(* Loops and conditionals. *)

Notation "'begin' 'if' econd 'then' ethen 'else' eelse 'end' " :=
  (EIfThenElse econd ethen eelse)
    (format "'[v' '[v  ' 'begin' '//' '[v' 'if'  '[hv  ' econd ']'  '/' 'then'  '[hv  ' ethen ']' '/' 'else'  '[v  ' eelse ']' ']' ']' '/' 'end' ']'",
       only printing).



Notation "'for' i '=' lo 'to' hi 'with' {: η :} 'do' e 'done;' '...'" :=
  (Stop CLoop (η, i, lo, hi, e) _ _)
     (only printing,
        format "'[v' 'for'  i  '='  lo  'to'  hi '//' 'with'  '[hv   ' {:  η  :} ']' '//' 'do' '[hv' '//' e ']' '//' 'done;'  '...' ']'").

Notation "e1 ; e2" :=
  (ESeq e1 e2)
    (only printing, format "e1 ;  '/' e2", at level 20, e1, e2 at level 200).

(* Check (Stop CLoop (("n" ~> #0; "k" ~> VData "S" <v VConstant "O" v> ; ε),
                      "x", repr 1, repr 50,
                      ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x"))
                        (EApp (EVar "f") (EVar "x"))) ret next).
   =>
for "x" = repr 1 to repr 50
with {: "n" ~> #0;
        "k" ~> "S" (VConstant "O");
        ε :}
do
  (EVar "f") (EVar "x"); (EVar "f") (EVar "x"); (EVar "f") (EVar "x"); (EVar "f") (EVar "x")
done; ...
     : micro val *)
(* Check (Stop CLoop (("n" ~> #0; "k" ~> VData "S" <v VConstant "O" v> ; ε),
                      "x", repr 1, repr 50,
                      ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x")) $ ESeq
                        (EApp (EVar "f") (EVar "x"))
                        (EApp (EVar "f") (EVar "x"))) ret next).
   =>
for "x" = repr 1 to repr 50
with {: "n" ~> #0;
        "k" ~> "S" (VConstant "O");
        ε :}
do
  (EVar "f") (EVar "x");
  (EVar "f") (EVar "x");
  (EVar "f") (EVar "x");
  (EVar "f") (EVar "x");
  (EVar "f") (EVar "x");
  (EVar "f") (EVar "x")
done; ...
  : micro val *)

(* -------------------------------------------------------------------------- *)
(* Pattern matching. *)

Notation "'EMatch' x 'with' pats " :=
  (EMatch x pats)
    (at level 90,
      only printing,
        no associativity,
          format "'[v' 'EMatch'  x  'with' '//' pats ']'").

Notation "'|' pat '=>' e others" :=
  (BrCons (Branch pat e) others)
    (at level 80,
       others at level 81,
         only printing,
           format "'[hv' '|'  '[v  ' pat  '=>' '//' e ']' '//' others ']'").

Notation "'end'" := (BrNil) (only printing).

(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* [Stop]-related notations. *)

Notation "'ref' v ';' '...continuations'" := (Stop CAlloc v _ _) (only printing).
Notation "'!' v ';' '...continuations'" := (Stop CLoad v _ _) (only printing).
Notation "ℓ ':=' v ';' '...continuations'" := (Stop CStore (ℓ, v) _ _) (at level 70, only printing).

(* -------------------------------------------------------------------------- *)
(* Records *)

Notation "'(' n1 := v1 ')'" :=
  (FECons n1 v1 FENil)
    (only printing,
     at level 80,
     right associativity,
     format "'(' n1  ':='   v1 ')'").

Notation "'(' n1 := v1 ')' ; tail" :=
  (FECons n1 v1 tail)
    (only printing,
     at level 80,
     right associativity,
     format "'(' n1  ':='   v1 ')' ;  '/' tail").

Notation "{ fds }" :=
  (ERecord fds)
    (only printing,
     format "{  '[hv' fds ']'  }").

Notation "r . f" :=
  (ERecordAccess r f)
    (only printing,
     at level 80, format "r . f").

Notation "{ r 'with' fds }" :=
  (ERecordUpdate r fds)
    (only printing,
       format "{  r  'with'  fds  }").
