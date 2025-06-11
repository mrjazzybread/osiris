# TODO

## Features

* Add support for shallow handlers (translator, semantics, reasoning rules).

* Add support for concurrency (SC first; weak memory later).

* Annotate `VData` and `PData` with the unique identity of the data type.
  During pattern matching, check that the types are equal; otherwise crash.
  We might otherwise continue normally (with a match success or a match
  failure) in cases where a crash should occur.

* Improve our current support for tuples and algebraic data types
  (Hoare-style rules for `VTuple`, `VData`, ...).
  In the long term, figure what kind of boilerplate
  we might wish to generate.

* Improve our current support for extensible algebraic data types
  and exceptions. Verify some programs that allocate/raise/catch
  exceptions. (Should `encode` have access to the environment?)

* Modules; nested modules; the standard library.

* Signature ascription; functors.
  Specify and verify a functor as an example (a simplified version
  of `Set.Make`; maybe a functor that produces an abstract type of
  sorted lists).

* Engineering issue: monolithic lemma (one lemma per module)
  versus fine-grained lemmas (one lemma per definition).
  Are we able to propose a fine-grained style
  that is lightweight
  and does not expose internal notions?
  (Perhaps the translator should generate toplevel definitions
   with predictable names.)

* Design satisfactory Hoare-style rules for structure items
  and for module expressions.

* Clean up the reasoning rules in Osiris;
  introduce a `Spec` predicate in Osiris.

* Distinguish undefined behavior and undesirable behavior.

## Cleanup

* Remove dead branches.

## Iris machinery

* Make sure the adequacy statement(s) and proof
  are clean and well-understood.

## Translator

* Primitive operations and constants that still need to be recognized:
  + `min_int`, `max_int`
  + `%compare`
  + `%loc_LOC` and friends (type-directed!)
  + `%andint`, `%orint`, `%xorint`, `%lslint`, `%lsrint`, `%asrint`
  + `%raise`, `%raise_notrace`
  + `%negfloat`, `%addfloat`, `%subfloat`, `%mulfloat`, `%divfloat`, `%absfloat`, `%floatofint`, `%intoffloat`, and more
  + operations on arrays (`array.mli`)

## Tutorial

* Create a tutorial for end users.

## OCaml standard library

* Do we apply the translator to all of it?
  What about unsupported constructs, external primitives, etc.?

## Engineering and proof mode

* How do we want to deal with mutually recursive definitions
  of several functions?

* We should use `set` every time we extend the environment,
  so the environment in the goal is always a name and never
  an explicit list. Can this be automated / made invisible
  to the end user?

* Make sure that we no longer use the tactic `simp`
  and the relation `simplify`.

* Experiment with the granularity of Coq toplevel definitions.
  We could use as few as one per OCaml file
  and as many as one per AST node.
  In between, we could use one per OCaml definition,
  and/or make sure that we use enough to ensure that
  every Coq definition has bounded size.
  At the moment, we generate a Coq definition only at certain nodes
  (see `cut` in `Coqify.ml`).

* Write a `help` tactic that analyzes the goal, explains its shape,
  explains why we are here and what likely is the next thing to do.
  (This assumes that we are able to work with a fixed finite set
  of possible goal shapes.)

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

  In `VData` and `VXData`, some form of unique identity of the algebraic data
  type must be added. So `Obj.magic` does not allow casting from one type to
  a different type.

* The combination of `Obj.magic` and polymorphic equality `=` may be
  particularly troublesome. It implies that we are giving a semantics to
  comparisons which in OCaml are forbidden. We may want to have our
  polymorphic equality crash when it compares two values of distinct types.
  If the comparison crashes in our semantics, then all is well.
  If the comparison returns `true` or `false` in our semantics,
  then we must ascertain that it does the same (and does not crash)
  in OCaml+magic.

## Tests and Examples

* Develop a more serious test of the semantics.

* Test the reasoning rules via examples:
  - Check that we are able to reason about infinite loops using Löb induction
  - Check that we are able to reason about terminating loops using induction
  - Check that we are able to frame out an assertion during
    the execution of the rest of the loop
  - Check that we are able to use Iris invariants
  - Port Arthur's imperative pairing heaps and compare with CFML.

* Suggested examples for different features:
  - pure code: searching in a BST
  - mutually recursive definitions: List.sort
  - exceptions: List.mem using List.iter
  - mutable state: sum of a list using List.iter and a reference
  - try-with catching one exception but not another

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
* `Obj.magic`
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
    we cannot have the ordering operators (e.g. false < true
    crashes in the current semantics).
* Polymorphic comparison operators
  + `eq_val` should be extended to records
  + `lt_val` should be extended to chars, strings, tuples, records
  + define `compare`, `min`, `max` as library functions,
    based on other primitive operations
* Polymorphic variants (what instance of `Encode`?)
* Modules, functors, signature ascription
  + Functor application contains an implicit signature ascription
  + An `.mli` file imposes an implicit signature ascription
* Unspecified evaluation order of toplevel modules
* First-class modules
* Extensible algebraic data types ✓
* Exceptions ✓
  + Asynchronous exceptions (`Out_of_memory`, `Stack_overflow`...)
    are not modeled in our semantics, so must not be caught;
    catch-all handlers are therefore problematic;
    `Fun.protect` seems OK because it is effect-polymorphic
* The module `Lazy`
* Effect handlers ✓
* Shared-memory concurrency (SC)
  + Must allow spurious CAS failures
    or restrict CAS to simple values (VBool, VInt, VLoc);
    what does HeapLang do?
  + Weak memory (Cosmo)
  + Thread-local storage
  + Should we distinguish between threads and domains?
    - Domain-local storage
  + Should we model [the subtle semantics of safe points](https://discuss.ocaml.org/t/using-poll-error-attribute-to-implement-systhread-safe-data-structures/12804)?
* What is "function arity" in OCaml? Is our semantics correct?
  + Careful: the change log for OCaml 5.2 says:
    *Function arity [...] is now based solely on the source program's
    parsetree. Previously, the heuristic for arity had more subtle heuristics
    that involved type information about patterns. Function arity is important
    because it determines when a pattern match's effects run and is an input
    into the fast path for function application.*
* `when` clauses (may be easy to handle just by viewing `when e1 e2`
    as an expression that raises `Next` if `e1` evaluates to `false`)
* Recursive modules? (Used in Sek, for example.)
* The OCaml FFI.
* We *could* support `[%extension_constructor X]`,
  although it is so obscure that it is perhaps not worth the trouble.
  See "Built-in extension nodes" in the OCaml manual.

## Features of OCaml that we do not want to support

* Objects and classes
* Pattern matching on mutable data; the `lazy` pattern
  (more generally, all kinds of effects during pattern matching)
* Immutable recursive values other than functions
* Labeled arguments
* Optional arguments and default values
* Advanced GC features (weak pointers; ephemerons; finalizers)
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
