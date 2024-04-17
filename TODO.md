# TODO

## Cleanup

* Remove dead branches.
* Rename `osirisGS` to something less ugly.

## Iris machinery

* Make sure the adequacy statement and proof are clean and well-understood.
* Offer both partial correctness and total correctness WPs,
  with bridges between them?

## Translator

* Document which version of OCaml we depend upon (5.x).

* Primitive operations and constants that still need to be recognized:
  + `min_int`, `max_int`
  + `%compare`
  + `%loc_LOC` and friends (type-directed!)
  + `%andint`, `%orint`, `%xorint`, `%lslint`, `%lsrint`, `%asrint`
  + `%raise`, `%raise_notrace`
  + `%negfloat`, `%addfloat`, `%subfloat`, `%mulfloat`, `%divfloat`, `%absfloat`, `%floatofint`, `%intoffloat`, and more
  + operations on arrays (`array.mli`)

* Generates Coq encoding boilerplate for algebraic data types.
  See if Arthur's code can be re-used.

## Tutorial

* Use CSS to enlarge the text width (the margins are currently too wide)
  and increase the font size.

* Try to improve the suboptimal rendering of Coq's `Check` commands.

## OCaml standard library

* What version of the OCaml standard library do we embark?
* Do we apply the translator to all of it?
  What about unsupported constructs, external primitives, etc.?

## Engineering and proof mode

* What language(s) do we expose to the end user? Just OCaml,
  or part of the micro monad, or all of the micro monad?
  How do we let the end user perform simplification of `par` trees?

* Probably we should use `set` every time we extend the environment,
  so the environment in the goal is always a name and never an explicit list.

* Rework module specifications and establish how [pure] and [wp] proofs work
  on [eval_mexpr].

* Module paths whose specification is known are currently simplified by [simp].
  However, it required to alter [simp1_inspect]. Replace this hack by hints.

* Fix [wp_use]: look at the lemma and apply different tactics depending on its
  body.

* Improve [wp_bind] : if [simp] simplifies [m1] into [ret v1], let Coq compute,
  otherwise, use the lemma [wp_simp].

* Multiple applications of curried functions are difficult to deal with.

* Experiment with the granularity of Coq toplevel definitions.
  We could use as few as one per OCaml file
  and as many as one per AST node.
      => Partially done ; it really improved the build time.
  In between, we could use one per OCaml definition,
  and/or make sure that we use enough to ensure that
  every Coq definition has bounded size.

* By default, hide continuations in goals (they are too verbose).
  Offer an option to show them.

* Display environments in a nice form in goals.
  + One binding per line.
  + By default, display complex values (such as closures)
    in an abbreviated form.

* Write a `help` tactic that analyzes the goal, explains its shape,
  explains why we are here and what likely is the next thing to do.

* Find a way to declare a function n-ary so that proving specifications of its
  partial applications is not required.

* Get tactics to fail: currently, most tactics do not fail and might not make
  progress. Thus, it is difficult to debug them.

* Use more hint databases for typeclasses, not to mix simplifications with
  reasoning.

* Try to always work with values of the form `#v` and never `VInt _`.
  (Hide the constructors of the the type `val` from the end user.)
  `#` should be opaque.

* Fix the notation for environments:
  - values should be explicit in records:
    [ VRecord (EnvCons x v (.. (EnvCons z w EnvNil) ..)) ]
    should be printed as
    [ {[ x := v ; ... ; z := w ]} ] ;
  - values should be hidden in other environments.

* Can we somehow view continuations as linear (instead of affine) in the
  program logic, so that the user is forced to check that a continuation
  is never dropped by mistake?

## Semantics

* Write down an informal argument of why translating `Obj.magic` to the
  identity is sound. First, this relies on the assumption that OCaml has a
  universal representation of values (i.e., every value fits in one word).
  Therefore it is incompatible with OCaml's special treatment of float arrays.
  Second, this relies on the property that "if two values have different
  runtime representations in OCaml then they have different representations in
  our semantics". Indeed, without this property, a program that uses
  `Obj.magic` could be correct in our semantics and incorrect in reality. In
  other words, the runtime representation in OCaml must be a *function* of the
  Osiris representation. Therefore, we should be able to write a text that
  describes, for each Osiris value, how it is represented in memory in OCaml.

  The apparent ambiguity between a unary constructor applied to a
  pair `A (x, y)` and a binary constructor `A (x, y)` is not a problem,
  because they have different representations in Osiris. The Osiris encoding
  of data constructors involves a tuple whose arity is the constructor's
  arity.

  The combination of `Obj.magic` and polymorphic equality `=` may be
  particularly troublesome. It implies that we are giving a semantics to
  comparisons which in OCaml are forbidden. If the comparison crashes in our
  semantics, then all is well. If the comparison returns `true` or `false` in
  our semantics, then we must ascertain that it does the same (and does not
  crash) in OCaml+magic. And **this is false** for data constructors: e.g.
  comparing `A 3` with `A 3` returns `true` in our semantics, but can return
  `false` in OCaml+magic if these two values originate in two distinct
  algebraic data types. To fix this, we could:
  + remove `Obj.magic`,
  + abandon polymorphic equality at algebraic data types, or
  + change our encoding of algebraic data types,
    and use integer tags that faithfully reflect OCaml's
    runtime representation.
    This would be feasible if we generate the encoding boilerplate.

* Can we (and should we) prove that our formulation of the semantics
  is equivalent to a standard small-step presentation?

  We certainly cannot easily prove an equivalence with a substitution
  semantics, because we cannot define a substitution semantics in the
  first place. Due to `open` and `include`, we cannot define sensible
  notions of "free variables" or "capture-avoiding substitution". So,
  we must use delayed substitutions, or equivalently, environments.

  We should also prove that each ample step corresponds to a bounded
  number of small steps (where the bound may depend on the source
  code of the program) (giving formal meaning to this claim requires
  distinguishing the program and the environment in which the program
  is executed). This means that Osiris with time credits is sound!

## Tests and Examples

* Once the translation of OCaml to our AST works, develop a more serious
  test suite of the semantics.

* Can we (automatically) measure the coverage of our test suite?
  i.e., measure whether (and how many times) each line of code
  in the interpreter (eval.v) is exercised by the tests (examples.v).

* Test the reasoning rules via examples:
  - Check that we are able to reason about infinite loops using Löb induction
  - Check that we are able to reason about terminating loops using induction
  - Check that we are able to frame out an assertion during
    the execution of the rest of the loop
  - Check that we are able to use Iris invariants
  - Port Arthur's imperative pairing heaps and compare with CFML.

## Features of OCaml that we want to support (at some point)

* Functions and function applications ✓
* Mutually recursive functions ✓
* Algebraic data types (unit, tuples, sums, records, sums-of-records) ✓
* Pattern matching on immutable data ✓
* Conditionals ✓
* `while` loops ✓
* `for` loops ✓
  + still missing support for `downto`
* Unspecified evaluation order of `let/and` definitions and function applications ✓
* Unspecified evaluation of `assert` statements ✓
* `let` operators
* `Obj.magic` can be supported (just erase it);
  I think that we will be able to verify programs that make "dynamically well-typed"
  use of `Obj.magic` (i.e., programs that do no cast values from one type to another).
* Arrays
  + allow ownership of individual array cells (or slices)
  + see array-based trees in CPP 2024 [Mechanised Reasoning about Array-Based Trees in Separation Logic](https://dl.acm.org/doi/abs/10.1145/3636501.3636944)
* Characters and strings
  + decide how they should be represented in Coq;
    Coq's `char` type seems needlessly inefficient,
    and the model of a string should be a list of characters.
  + do UTF-8 characters in string literals create difficulties?
    do Coq and OCaml read them in the same way?
* `bigarray`
* `bytes`
* `int32`, `int64`, `nativeint`
* Records with mutable fields
  + allow ownership of individual record fields?
  + `let rec` over mutable records could conceivably be supported
* Integers:
  + give lemmas to help establish that the result of an operation
    is representable
  + bitwise operations
* Booleans:
  + We would like to have all of the comparison operators,
    but because our model views Booleans as data constructors,
    we cannot have the ordering operators.
* Polymorphic comparison operators
  + `eq_val` should be extended to records
  + `lt_val` should be extended to chars, strings, tuples, records
  + define `compare`, `min`, `max` as library functions,
    based on other primitive operations
* Polymorphic variants
* Modules, functors, signature ascription
  + Functor application contains an implicit signature ascription
  + An `.mli` file imposes an implicit signature ascription
* Unspecified evaluation order of toplevel modules
* First-class modules
* Extensible algebraic data types
* Exceptions
  + Exception names must be treated like variables,
    *not* like data constructors;
    so, in data constructor applications and data constructor patterns,
    the translator must treat exceptions (and extensible data types)
    in a special way
  + Asynchronous exceptions (`Out_of_memory`, `Stack_overflow`...)
    are not modeled in our semantics, so must not be caught;
    catch-all handlers are therefore problematic;
    `Fun.protect` seems OK because it is effect-polymorphic
* The module `Lazy`
* Effect handlers
* Shared-memory concurrency (SC)
  + Must allow spurious CAS failures
    or restrict CAS to simple values (VBool, VInt, VLoc);
    what does HeapLang do?
  + Should we distinguish between threads and domains,
    and model [the subtle semantics of safe points](https://discuss.ocaml.org/t/using-poll-error-attribute-to-implement-systhread-safe-data-structures/12804)?
* Shared-memory concurrency (weak memory)
* Pattern matching on mutable data
* `when` clauses (may be easy to handle just by viewing `when e1 e2`
    as an expression that raises `Next` if `e1` evaluates to `false`)
* Recursive modules? (Used in Sek, for example.)

## Features of OCaml that we do not want to support

* Floating point numbers
* Objects and classes
* The `lazy` pattern
* Immutable recursive values other than functions
* Labeled arguments
* Optional arguments and default values
* Unix signal handling

## Miscellaneous notes

* Integers (rauch-wolff-03, jacobs-03)
  https://coq.discourse.group/t/best-practices-for-machine-level-representation-of-numbers-and-bitwise-operations/482/6
  coq-nbits (https://troll.iis.sinica.edu.tw/by-publ/recent/coq-qfbv.pdf, Section 4)
  https://github.com/fmlab-iis/coq-nbits
  SInt63:
  https://www.ub.edu/prooftheory/media/sint6320x85.pdf
  https://coq.github.io/doc/master/stdlib/Coq.Numbers.Cyclic.Int63.Sint63.html
  Bit sets:
  https://www.irif.fr/~dagand/stuffs/coq-bitset/flops/paper.pdf
