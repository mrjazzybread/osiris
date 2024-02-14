From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.
From osiris Require Import base.
From osiris.semantics Require Import semantics.
From osiris.lang Require Import lang.
From osiris.proofmode Require Import specifications.

(* Cf.
   https://coq.inria.fr/doc/V8.10.2/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations
   for information on notation formatting. *)

(* TODO Most of the notation in this file should go away.
   The rest should be cleaned up and documented. *)

(* ------------------------------------------------------------------------ *)

(* We use [Goal (trivial e)] to avoid printing notation the notation of [e]
   to stdout when compiling *)

Local Definition trivial {A : Type} := (λ (_ : A), True).

(* ------------------------------------------------------------------------ *)

(* When a decoration is present, the underlying AST is not shown. *)

Notation "'ocaml' decoration" := (deco decoration _)
  (at level 8, only printing).

(* ------------------------------------------------------------------------ *)

(* A notation scope for [expr], includes arithmetic and booleans *)

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.

Notation "- e" := (EIntNeg e) : expr_scope.
Infix "+" := EIntAdd : expr_scope.
Infix "-" := EIntSub : expr_scope.
Infix "*" := EIntMul : expr_scope.
Infix "&&" := EBoolConj : expr_scope.
Infix "||" := EBoolDisj : expr_scope.
Infix "==" := EOpPhysEq (at level 90) : expr_scope.
Infix "=" := EOpEq : expr_scope.
Infix "<>" := EOpNe : expr_scope.
Infix "<" := EOpLt : expr_scope.
Infix "<=" := EOpLe : expr_scope.
Infix ">" := EOpGt : expr_scope.
Infix ">=" := EOpGe : expr_scope.

Definition EInt_of_Z Z := EInt Z.

Definition Z_of_EInt e :=
  match e with
  | EInt z => Some z
  | _ => None
  end.

Number Notation expr EInt_of_Z Z_of_EInt : expr_scope.

Open Scope expr.

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
  ((n1, v1) :: η) (at level 80, right associativity, format "n1  ~>  v1 ;  '/' η").

Notation "x  '≈>'  f" :=
  (RecBinding x f)
    (only printing, at level 100, no associativity).

Notation "'An' 'environment' 'containing' n1 , .. , nn 'will' 'be' 'added' 'to' 'the' 'current' 'environment.'" :=
  (ret
     (n1 ~> _ ; (.. (nn ~> _ ; []) ..)) ++ _, (n1 ~> _ ; (.. (nn ~> _ ; []) ..)) ++ _)
    (only printing, format
"'[v    ' 'An'  'environment'  'containing'  '/' n1 ,  '/' .. ,  '/' nn  '/' 'will'  'be'  'added'  'to'  'the'  'current'  'environment.' ']'").

Infix ":::" := (concat).

(* -------------------------------------------------------------------------- *)
(* Paths, tuples and ADTs. *)

Notation "'Path' x1" :=
  (PathBase x1)
    (at level 90,
      format "'Path'  x1").

Goal (trivial (PathBase "base")). Abort.

Notation "'Path' x1 '.' .. '.' xn '.' xm" :=
  (PathDot (.. (PathDot (PathBase xm) xn) ..) x1)
    (at level 200,
       format "'Path'  x1 '/' '.' .. '/' '.' xn '.' '/' xm").

Goal (trivial
        (PathDot (PathDot (PathDot (PathBase "base") "1") "2") "3")).
Abort.

Notation "'EPath' x1" :=
  (EPath (PathBase x1))
    (at level 90,
      only printing,
      format "'EPath'  x1").

Goal (trivial (EPath (PathBase "base"))). Abort.

Notation "'EPath' x1 '.' .. '.' xn '.' xm " :=
  (EPath (PathDot (.. (PathDot (PathBase xm) xn) ..) x1))
    (at level 200,
      only printing,
      format "'EPath'  x1 '/' '.' .. '/' '.' xn '/' '.' xm").

Goal (trivial
        (EPath (PathDot (PathDot (PathDot (PathBase "base") "1") "2") "3"))).
Abort.

(* -------------------------------------------------------------------------- *)
(* Closures, function applications, and function calls. *)

Notation "'Anon' '(' '_' '=>' e ')'" :=
  (AnonFun "__osiris_anonymous_arg" e)
    (at level 200,
      format "'Anon'  '(' '_'  '=>' '/    '  '[hv' e ']' ')'").

Goal (trivial
        (AnonFun "__osiris_anonymous_arg" (EInt 0))).
Abort.

Notation "'Anon' '(' x '=>' e ')'" :=
  (AnonFun x e)
    (at level 200,
      format "'Anon'  '(' x  '=>'  '/    ' '[hv' e ']' ')'").

Goal (trivial (AnonFun "argname" (EInt 1))).
Abort.

Goal (trivial
        (AnonFun "x" (ETuple
                        [EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;
                         EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;EInt 0]))).
Abort.

Goal (trivial (EAnonFun (AnonFun "argname" (EInt 1)))). Abort.

Goal (trivial (EAnonFun (AnonFun "__osiris_anonymous_arg" (EInt 0)))). Abort.

Notation "'_'" := (EPath "__osiris_anonymous_arg") (only printing).

Notation "'EApp' '(' e1 ')' '(' e2 ',' .. ',' en ')'" :=
  (EApp (.. (EApp e1 e2) ..) en)
    (at level 200,
      only printing,
      format "'EApp'  '(' e1 ')'  '/' '(' e2 ','  '/' .. ','  '/' en ')'").

Goal (trivial (EApp (EString "fun") (EString "arg"))). Abort.

Goal (trivial
        (EApp
         (EApp
            (EApp
               (EString "fun") (EString "arg1"))
            (EString "arg2"))
         (EString "arg3"))).
Abort.

Notation "'pure' '(' call '(' f ')' '(' arg1 ',' arg2 ',' .. ',' argn ')' ψ" :=
  (pure (call f arg1)
     (λ c, pure (call c arg2)
             (.. (λ c, pure (call c argn) ψ) ..)))
    (at level 200,
      only printing,
    format "'pure'  '(' call  '(' f ')'  '/' '(' '[' arg1 ','  '/' arg2 ','  '/' .. ','  '/' argn ']' ')'  ψ").

Goal (trivial
        (pure (call (VString "F") (VString "X"))
           (λ c, pure (call c (VString "Y"))
                   (λ c, pure (call c (VString "Z"))
                           (λ v : val, True))))).
Abort.

Notation "'WP'  'calln' f v1 v2 .. vn @ s ; E {{ φ }}" :=
  (wp s E (call f v1)
      (fun v => wp s E (call v v2)
                   (.. (fun v =>  wp s E (call v vn) φ ) ..)))
  (only printing).

(* -------------------------------------------------------------------------- *)
(* Loops and conditionals. *)

Notation "e1 ; e2" :=
  (ESeq e1 e2)
    (only printing, format "e1 ;  '/' e2", at level 20, e1, e2 at level 200).

Goal (trivial
        (ESeq
         (EApp (EPath (PathBase "f")) (EPath (PathBase "x")))
         (EAssert (EOpEq (EPath (PathBase "x")) (EInt 2))))).
Abort.

(* -------------------------------------------------------------------------- *)
(* Pattern matching. *)

Notation "'EMatch' '(' x ')' []" :=
  (EMatch x [])
    (at level 90,
      only printing,
      no associativity,
      format "'EMatch'  '(' x ')'  []").

Goal (trivial (EMatch (EPath (PathBase "l")) [])). Abort.

Notation "'EMatch' '(' x ')' 'with' b1 .. bn 'end'" :=
  (EMatch x (cons b1 (.. (cons bn nil) ..)))
    (at level 90,
      only printing,
      no associativity,
      format "'[v' 'EMatch'  '(' x ')'  'with' '//'     '[' b1 '//' ..  '//' bn ']'  '//' 'end' ']'").

Goal (trivial (EMatch (EPath (PathBase "l")) [])). Abort.

Goal (trivial (EMatch (EPath (PathBase "l")) [Branch PAny (EInt 1)])). Abort.

Goal (trivial
        (EMatch (EPath (PathBase "l")) [Branch PAny (EInt 1); Branch PAny 2])).
Abort.

Notation "'|' pat '->' e" :=
  (Branch pat e)
    (at level 80,
      only printing,
      format "'|'  pat  '->'  '[' '/' e ']'").

Goal (trivial (EMatch (EPath (PathBase "l")) [Branch PAny (EInt 1)])). Abort.

Goal (trivial
        (EMatch
           (EPath (PathBase "l"))
           [Branch PAny
              (ESeq
                 (EApp (EPath (PathBase "f")) (EPath (PathBase "x")))
                 (ESeq
                    (EApp (EPath (PathBase "f")) (EPath (PathBase "x")))
                    (ESeq
                       (EApp (EPath (PathBase "f")) (EPath (PathBase "x")))
                       (EAssert (EOpEq (EPath (PathBase "x")) (EInt 2)))
                    )
                 )
              );
            Branch PAny 2]
     )).
Abort.

Goal (trivial (Branch PAny 2)). Abort.

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

Notation "n1 := v1" :=
  ([Fexpr n1 v1])
    (only printing,
     at level 80,
     right associativity,
     format "n1  ':='   v1").

Notation "n1 := v1 ; tail" :=
  ((Fexpr n1 v1) :: tail)
    (only printing,
     at level 80,
     right associativity,
     format "n1  ':='   v1 ;  '/' tail").

Notation "{ }" :=
  (ERecord [])
    (only printing,
      format "{ }").

Notation "{ fds }" :=
  (ERecord fds)
    (only printing,
      format "{  '[hv' fds ']'  }").

Goal (trivial (ERecord [])). Abort.

Goal (trivial
        (ERecord [Fexpr "a" 0;
                  Fexpr "b" 1;
                  Fexpr "c" 2;
                  Fexpr "d" (EString "val")])).
Abort.

Notation "r . f" :=
  (ERecordAccess r f)
    (only printing,
      at level 80, format "r . f").

Goal (trivial
        (ERecordAccess (ERecord [Fexpr "a" 0;
                                 Fexpr "b" 1;
                                 Fexpr "c" 2;
                                 Fexpr "d" (EString "val")]) ("a"))).
Abort.

Notation "{ r 'with' fds }" :=
  (ERecordUpdate r fds)
    (only printing,
       format "{  r  'with'  fds  }").

Close Scope expr.
