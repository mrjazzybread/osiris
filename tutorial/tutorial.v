Set Warnings "-require-in-section". (* .none *)

(*|
=====================
Hoare Logic for OCaml
=====================
|*)

Section Eval. (* .none *)
Require Import base lang free eval. (* .none *)

Notation ε := EnvNil. (* .none *)
Notation int := int.int. (* .none *)

(*|
-----------
Expressions
-----------
|*)

(*|
An OCaml expression is represented in Coq as an abstract syntax tree
of type `expr`. For instance, the following expression represents the
OCaml expression :code:`24 + 18`:
|*)

Definition add_24_plus_18 : expr :=
  EIntAdd (EInt 24) (EInt 18).

(*|
For now, we write these expressions by hand. In the future, of course,
we plan to offer an automated translation from OCaml source code into
Coq.
|*)

(*|
Only a subset of OCaml's syntax is supported at this point. It involves
two syntactic categories, *patterns* and *expressions*.
|*)

Print pat.
Print expr.

(*|
At this time, expressions include:

* Variables;
* Functions and function calls;
* Local definitions, including definitions of recursive functions;
* Tuples;
* Data constructors;
* Boolean operators;
* Integers, integer arithmetic operators, integer comparison operators;
* Sequencing;
* Conditionals (:code:`if`);
* Pattern matching (:code:`match`);
* Loops (:code:`while`, :code:`for`);
* Runtime assertions (:code:`assert`).

|*)

(*|
------
Values
------
|*)

(*|
We define the semantics of OCaml by implementing an *interpreter* of
OCaml programs inside Coq. We want this interpreter to be a classic
environment-based interpreter: when given an environment `η` and an
expression `e`, it should compute a value `v`.
|*)

(*|
*Values* have their own syntactic category: they are not a subset of
expressions. For instance, a closure is a value, not an expression.
|*)

Print val.

(*|
An *environment* is a mapping of variables to values. It is represented
in Coq as an association list. Because a closure captures an environment,
the syntactic categories of values and environments are mutually recursive.
|*)

Print env.

(*|
---------------------
A Monadic Interpreter
---------------------
|*)

(*|
OCaml is an effectful programming language: an OCaml program can
exhibit a variety a side effects. For instance, a program can diverge,
that is, run forever. A program can have observable side effects, such
as mutating heap-allocated objects or performing input/output actions.
A program can behave in a non-deterministic manner, either because of
its interaction with the operating system, or due to intrinsic
non-determinism (some OCaml constructs have unspecified evaluation
order).
|*)

(*|
For these reasons, the interpreter cannot be expected to be a
function of type `env → expr → val`. That would imply that
interpretation is deterministic and always terminates.
Instead, the interpreter must be a *monadic* interpreter:
|*)

Check eval. (* .unfold *)

(*|
The term `eval η e` has type `free val`,
where `free` is a *monad*.
This means that `eval η e` is
an effectful *computation* which may diverge,
may behave in a non-deterministic manner, and
may eventually produce a value.

For instance, evaluating the OCaml expression :code:`42`
in the empty environment `ε`
yields the OCaml value :code:`42`:
|*)

Eval cbn in (eval ε (EInt 42)). (* .unfold *)

(*|
Coq finds that this computation is equal to
`ret (VInt (int.repr 42))`.

The data constructor `ret` is the `return` combinator
of the monad. Its presence means that Coq has been able
to fully evaluate this computation, whose final result
is the value `VInt (int.repr 42)`.
|*)

Check @ret. (* .unfold *)

(*|
The tag `VInt` identifies an integer value. Its payload,
`int.repr 42`, is a machine integer.
OCaml has integers of a limited bit width.
The projection `int.repr` maps the type `Z` of ideal integers
into the finite type `int` of the signed machine integers.

|*)

Check int.repr. (* .unfold *)

(*|
The interpreter is defined in a straightforward way.
It could be taught in an introductory course on
programming language implementation.
Yet, this interpreter plays an important role for us:
it serves as our definition of the semantics of OCaml
and as a basis for the program verification system
that we wish to set up.
|*)

(*|
The following equation highlights one case in the definition of `eval`,
namely the case of the `if/then/else` construct. To evaluate the OCaml
expression :code:`if e then e1 else e2`, the interpreter first
evaluates `e` and checks that its result is a Boolean value `VBool b`.
Then, depending on `b`, it evaluates either `e1` or `e2`.
Because `e`, `e1`, and `e2` are subexpressions of the expression
:code:`if e then e1 else e2`, Coq recognizes that
it is permitted for `eval` to recursively invoke itself.
|*)

Goal ∀ η e e1 e2,
  eval η (EIfThenElse e e1 e2) =
    b ← as_bool (eval η e) ;
    if (b : bool) then eval η e1 else eval η e2. (* .no-goals *)
Proof. (* .none *)
  reflexivity. (* .none *)
Qed. (* .none *)

(*|
That said, there are places in the definition of `eval`
where we would like to recursively invoke `eval`
but that is not permitted by Coq.
An example appears in the case of `while` loops:
|*)

Goal ∀ η e body,
  eval η (EWhile e body) =
    b ← as_bool (eval η e) ;
    if (b : bool) then
      _ ← eval η body ;
      stop Eval (η, EWhile e body)
    else
      ok. (* .no-goals *)
Proof. (* .none *)
  reflexivity. (* .none *)
Qed. (* .none *)

(*|
After executing the loop body by calling `eval η body`,
we would like to execute the loop again.
This could be done by invoking `eval η (EWhile e body)`,
but such a recursive call is not permitted.
Instead, the interpreter *stops*
with a request for a recursive invocation of `eval`.
The monadic combinator `stop` expresses such a request.

This request is intended to be serviced by a scheduler
which supervises the execution of the interpreter.
It is up to the scheduler to step into the recursive call
and resume the execution of the interpreter.

Another interesting monadic combinator is `par`,
a binary combinator that allows two computations
to be executed in parallel.
This combinator is typically used in places where
OCaml has unspecified evaluation order.
For instance, here is how an OCaml function application :code:`e1 e2`
is evaluated:
|*)

Goal ∀ η e1 e2,
  eval η (EApp e1 e2) =
    '(v1, v2) ← par (eval η e1) (eval η e2) ;
    call v1 v2. (* .no-goals *)
Proof. (* .none *)
  reflexivity. (* .none *)
Qed. (* .none *)

(*|
The recursive calls `eval η e1` and `eval η e2` are executed in parallel.
If and once these calls yield two values `v1` and `v2`,
then the auxiliary function `call` (not shown)
is used to interpret the application of the function `v1`
to the argument `v2`.
The use of `par` reflects the fact that the definition of OCaml
does not specify whether `e1` is evaluated before `e2` is evaluated,
or `e2` is evaluated before `e1` is evaluated, or the two evaluations
may be interleaved.

Because we choose a pessimistic semantics
(that is, a non-deterministic semantics),
a programmer who reasons about a function application :code:`e1 e2`
must prove that there is no interference
between `e1` and `e2`. This is done by applying
the parallel composition rule
of concurrent separation logic.

Interpreting an addition expression :code:`e1 + e2`
also involves a parallel composition:
|*)

Goal ∀ η e1 e2,
  eval η (EIntAdd e1 e2) =
    '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
    ret (VInt (int.add i1 i2)). (* .no-goals *)
Proof. (* .none *)
  reflexivity. (* .none *)
Qed. (* .none *)

(*|
The reader may wonder how Coq can execute a parallel composition.
The answer is, it cannot: when the interpreter encounters a `par` combinator,
it stops. It is then up to the scheduler to take control,
to decide what step to take next,
and to resume the interpreter.

This can be observed by asking Coq to evaluate the OCaml expression
`24 + 18`:
|*)

Eval cbn in (eval ε add_24_plus_18). (* .unfold *)

(*|
The interpreter hits a `Par` combinator whose branches are
`ret (int.repr 24)` and `ret (int.repr 18)`
and whose continuation is
`(λ '(i1, i2), ret (VInt (int.add i1 i2)))`.
|*)

(*|
To understand how the `stop` and `par` combinators work,
one must examine how computations are represented
and how the scheduler is implemented.
We do so in the next two sections.
|*)

End Eval. (* .none *)

(*|
---------
The Monad
---------
|*)

Section Free. (* .none *)
Require Import base lang free. (* .none *)

Print free. (* .unfold *)

End Free. (* .none *)

(*|
-------------
The Scheduler
-------------
|*)


(*|
|*)
