(*|
=====================
Hoare Logic for OCaml
=====================
|*)

Require Import base lang free eval step safe wp wp_tactics encode. (* .none *)

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

Definition example : expr :=
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

*Values* have their own syntactic category: they are not a subset of
expressions. For instance, a closure is a value, not an expression.

An *environment* is a mapping of variables to values. It is represented
in Coq as an association list. Because a closure captures an environment,
the syntactic categories of values and environments are mutually recursive.
|*)

Print val.

(*|
|*)
