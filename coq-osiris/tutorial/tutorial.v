Set Warnings "-require-in-section". (* .none *)
From osiris Require Import osiris. (* .none *)
From osiris.program_logic Require Import safe. (* .none *)
Implicit Type f x : var. (* .none *)
Implicit Type c : data. (* .none *)
Implicit Type p : pat. (* .none *)
Implicit Type ps : pats. (* .none *)
Implicit Type e : expr. (* .none *)
Implicit Type es : exprs. (* .none *)
Implicit Type a : anonfun. (* .none *)
Implicit Type v : val. (* .none *)
Implicit Type vs : vals. (* .none *)
Implicit Type η δ : env. (* .none *)
Implicit Type rbs : rec_bindings. (* .none *)
Implicit Type i : int. (* .none *)
Implicit Type b : bool. (* .none *)

Implicit Type A B X Y : Type. (* .none *)

(*|
=========================
A Program Logic for OCaml
=========================
|*)

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
Only a subset of OCaml's syntax is supported at this point. It involves
two syntactic categories, *patterns* and *expressions*.
|*)

Print pat.
Print expr.

(*|
At this time, expressions include:

* Variables;
* Functions and function calls;
* Local definitions, including definitions of (mutually) recursive functions;
* Tuples;
* Data constructors;
* Boolean operators;
* Integers, integer arithmetic operators, integer comparison operators;
* Sequencing;
* Conditionals (:code:`if`);
* Pattern matching (:code:`match`);
* Loops (:code:`while`, :code:`for`);
* Runtime assertions (:code:`assert`).

These expressions are automatically generated from an OCaml parse tree.
|*)

(*|
------
Values
------
|*)

(*|
We define the semantics of OCaml by implementing an *interpreter* of
OCaml programs inside Coq. We want this interpreter to be an
environment-based interpreter: when given an environment `η` and an
expression `e`, it should compute a value `v`.
|*)

(*|
*Values* have their own syntactic category: they are not a subset of
expressions. For instance, a closure is a value, not an expression.
|*)

Print val.

(*|
An *environment* is a mapping of variables to values. Because a closure captures
an environment, the syntactic categories of values and environments are mutually
recursive.
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
non-determinism (such as unspecified evaluation order).
|*)

(*|
For these reasons, the interpreter cannot be expected to be a
function of type `env → expr → val`. Because of Coq's strongly
normalizing specification language, such a function type would imply
that interpretation is deterministic and always terminates.
Instead, the interpreter must be a *monadic* interpreter:
|*)

Check eval. (* .unfold *)

(*|
The term `eval η e` has type `micro val`,
where `micro` is a *monad*.
This means that `eval η e` is a step of
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
it serves as our definition of the semantics of OCaml (i.e. it is a
definitional interpreter) and as a basis for the program verification
system that we wish to set up.
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
where Coq disallows us to recursively invoke `eval` as we would like.
An example appears in the case of `while` loops:
|*)

Goal ∀ η e body,
  eval η (EWhile e body) =
    b ← as_bool (eval η e) ;
    if (b : bool) then
      _ ← eval η body ;
      stop CEval (η, EWhile e body)
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
|*)

(*|
The reader may wonder how Coq can execute a parallel composition.
The answer is, it cannot: when the interpreter encounters a `par` combinator,
it stops. It is then up to the scheduler to take control,
to decide what step to take next,
and to resume the interpreter.

This can be observed by asking Coq to evaluate the OCaml expression
`24 + 18`:
|*)

Transparent eval. (* .none *)
Eval cbn in (eval ε add_24_plus_18). (* .unfold *)
Opaque eval. (* .none *)

(*|
The interpreter hits a `Par` combinator whose branches are
`ret (repr 24)` and `ret (repr 18)`
and whose continuation is
`(λ '(i1, i2), ret (VInt (add i1 i2)))`.
|*)

(*|
To understand how the `stop` and `par` combinators work,
one must examine how computations are represented
and how the scheduler is implemented.
We do so in the next two sections.
|*)

(*|
---------------
The Micro Monad
---------------
|*)

(*|
The monad that is used to write the interpreter
is named `micro`.
The name is reminiscent of microcode;
it is chosen because this monad offers
a very simple API.
|*)

(*|
As usual,
the `ret` combinator represents
an empty sequence of instructions,
and the `bind` combinator constructs
the concatenation of two sequences of instructions:
|*)

Check @ret. (* .unfold *)
Check @bind. (* .unfold *)

(*|
In other words, `ret a` represents a computation that is finished
and has produced a result `a`; and `bind m1 (λ x, m2)`, also written
`x ← m1 ; m2`, represents the sequential composition of the computations
`m1` and `m2`.
|*)

(*|
The `crash` combinator represents a computation that has
encountered a serious problem and crashed. It is a fatal
error: it cannot be caught and handled.
It is a situation that we want to avoid: proving that a
program cannot crash is the
purpose of the program logics that we wish to set up.
|*)

Check @crash. (* .unfold *)

(*|
In our interpreter, `crash`
is typically used when a primitive operation is applied
to an argument of an invalid nature.
|*)

(*|
The `next` combinator can be thought of as an exception.
This exception can be caught and handled by the `try` combinator.
|*)

Check @next. (* .unfold *)
Check @try. (* .unfold *)

(*|
Our interpreter raises and catches this exception
as part of its normal execution.
For instance, `next` is used during the
evaluation of a pattern matching construct.
Somewhere, deep down in an auxilliary function, this exception
is raised to indicate that a pattern does *not* match
a value. Somewhere higher up,
the interpreter catches this exception
and moves on to the next branch.
|*)

(*|
The `stop` combinator allows a computation to request a service
from an external supervisor. The computation `stop c x`
can be thought of as a system call. The *code* `c` is the name of
the system call. This code has type `code X Y`, where `X` is the type
of the argument of the system call, and `Y` is the type of its result.
Accordingly, the *argument* `x` has type `X`,
and the computation `stop c x` has type `micro Y`.
|*)

Check @stop. (* .unfold *)

(*|
The codes, or system calls, that we use are presented a bit further on.
|*)

(*|
The `par` combinator is a parallel evaluation combinator.
The computation `par m1 m2` evaluates `m1` and `m2`
independently and in parallel. If the two computations have side effects
(via system calls) then these effects are interleaved in a nondeterministic
manner. If both computations succeed and return two results `a1` and `a2`
then `par m1 m2` returns the pair `(a1, a2)`.
|*)

Check @par. (* .unfold *)

(*|
In our interpreter, `par` is used to model OCaml's unspecified
order of evaluation. When OCaml evaluates two subexpressions in
an unspecified order, we consider that they are evaluated in
parallel.
|*)

(*|
`choose m1 m2` is a non-deterministic choice between the computations `m1`
and `m2`. One of them is executed; the other is discarded.
|*)

Check @choose. (* .unfold *)

(*|
In our interpreter, `choose` is used to model OCaml's runtime
assertion construct, `assert`. Depending on a command line
switch, the OCaml compiler can be instructed to either keep
this dynamic test or erase it. We want our semantics to be
independent of this command line switch, so we consider that
the compiler is free to choose between these two alternatives.
|*)


(*|
Internally, the type `micro A` is defined as an inductive type.
Thus, every computation must eventually produce a result, crash, raise
an exception, or stop on a system call, and Coq's execution engine can
(in principle) be used to compute this normal form.
|*)

Print micro.

(*|
The `try` combinator is not a constructor;
it is a function. This is made possible by building `try` into the
constructors `Stop`, `Par`, and `Choose`. Indeed, the continuations `k`
and `z` carried by these constructors correspond to two arms of a `try`
construct.
|*)

(*|
Expert readers may note that the definition of this monad is
reminiscent of *interaction trees*. However, interaction trees are
potentially infinite trees, whereas our computations are finite.
Furthermore, interaction trees do not have the parallel composition
combinator `par` or the non-deterministic choice combinator `choose`.
|*)

(*|
There are several ways of thinking about this monad. On the one hand,
from an abstract point of view, it can be regarded as *an abstract type
of computations*, equipped with the facilities that are needed to write
the interpreter in a natural style. On the other hand, from a concrete
point of view, it offers *a syntactic representation of a collection of
threads*. The constructor `Par` allows describing a binary tree of
threads. At the leaves, the constructors `Ret`, `Crash`, and `Next`
represent threads that have finished (in one way or another), while
the constructor `Stop` represents a thread that is paused and needs
to continue.
|*)

(*|
There are also several ways of thinking about the function `eval`:
|*)

Check eval. (* .unfold *)

(*|
On the one hand, one can think of it as an interpreter:
the computation `eval η e` executes the expression `e`.
On the other hand, one can also think of it as a compiler:
whereas the syntactic object `e` inhabits a large language
(namely, OCaml), the syntactic object `eval η e` inhabits a
much smaller and simpler language (namely, the monad).

It is well-known that a compiler can be in principle obtained
by specializing an interpreter, but this is usually a difficult
task. Here, this happens essentially for micro, thanks to the fact
that Coq's β-reduction engine can simplify the application `eval η e`.
|*)

(*|
The monad is parametric in the type `code`: it does not care what
the system calls are or what is their meaning. Our interpreter
uses the following set of codes:
|*)

Print code. (* .unfold *)

(*|
The code `CEval`, which we have encountered earlier, is used to request
a recursive invocation of the function `eval`. The code `CLoop` plays a
similar role, but is used in the interpretation of `for` loops.
The codes `CAlloc`, `CLoad`, and `CStore` are requests to allocate, read,
write a memory location in the heap.
|*)

(*|
-------------
The Scheduler
-------------
|*)

(*|
There remains to somehow give meaning to monadic computations
of type `micro A`. As explained earlier, these computations are
effectful: in particular, they can diverge, and they are
nondeterministic. Thus, we cannot expect to give them a
computational behavior inside Coq. However, there are other
ways in which we can describe their behavior (or, more accurately,
the set of their possible behaviors) inside Coq. One traditional
approach is *reduction semantics*.
This is done by defining a binary relation `step`:
|*)

Check @step. (* .unfold *)

(*|
The idea is that `step m m'` means that the computation `m`
can, in one step, transform itself into the computation `m'`.

Although reduction semantics is traditionally also known as
*small-step semantics*, in this case, it would be more appropriate
to call this an *ample-step semantics*. Indeed, in this approach,
the β-reduction work performed by Coq is implicit (invisible).
The interpreter pauses itself from time to time, and each step
takes us from one pause to the next pause.

The relation `step` is inductively defined.
|*)

Print step. (* .fold *)

(*|
Let us look at some of the cases in this definition.
An `CEval` request steps to an invocation of `eval`:
|*)

Check @StepEval. (* .unfold *)

(*|
Under a parallel composition constructor `Par`,
either thread is allowed to take a step.
The following reduction rule shows that the left-hand thread
may take a step:
|*)

Check @StepParLeft. (* .unfold *)

(*|
If both threads have reached a result, then
the parallel composition disappears.
The continuation `k` is applied to the pair `(v1, v2)`
of the results:
|*)

Check @StepParRetRet. (* .unfold *)

(*|
The constructor `Choose`
makes a non-deterministic choice
among its two branches:
|*)

Check @StepChooseLeft. (* .unfold *)
Check @StepChooseRight. (* .unfold *)

(*|
There are more reduction rules, not shown.

We sometimes refer to this semantics as the «scheduler»,
because it appears to make scheduling decisions;
however, it is in fact non-deterministic.

We also sometimes refer to this semantics as the «system»,
because it answers `Stop` requests.
|*)

(*|
------
Safety
------
|*)

(*|
This reduction semantics allows us to define what it means for a program
to be safe. A program is *safe* if it cannot crash, that is, if it cannot
reduce (in zero, one, or more steps) to `Crash`.

Technically, we say that a program is *initially safe* for `n` steps
if it cannot reduce in at most `n` steps to `Crash`.
We say that a program is safe
if, for every `n`, this program is initially safe for `n` steps.
|*)

Print initially_safe. (* .fold *)
Print safe. (* .fold *)

(*|
The following lemmas can be used to prove that a program is safe.
Because the monad has few data constructors,
few lemmas are needed.
This is a minimalist program logic,
yet it is a full-fledged logic!
|*)

Check @safe_ret. (* .unfold *)

Check @safe_bind. (* .unfold *)

(*|
|*)
