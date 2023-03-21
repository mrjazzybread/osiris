# TODO

* Can we separate the monadic support layer
  from the OCaml-specific aspects?
  That is, make `free.v` independent of `lang.v`.
  And make that monadic support layer an independent library.

* Find a way of annotating failures with a string,
  so we can keep track of the reason for the failure.

* Clean up the type classes and notation for monads.

* Think about [order of evaluation](https://v2.ocaml.org/manual/expr.html#sss:expr-functions-application).
  Use `par` in the evaluator.
  Write examples to test it.

* The judgement `safe m φ` has just one postcondition
  and forbids the answer `Next`.
  It is really a special case of a more general judgement
  `safe2 m φ ψ` which means that if `m` reduces to `Next`
  then `ψ` holds.
  It may be necessary to define `safe2` and to establish
  its reasoning rules.

* There are two approaches to reasoning about `match` constructs.
  In one approach, the user first performs a case analysis at the
  logical level. In each branch of this logical case analysis,
  enough information is obtained to allow determining which
  branch of the `match` construct is taken. The `match`
  construct can then be symbolically evaluated.
  In the other approach, the user performs no case analysis
  up front; a set of Hoare-style reasoning rules are used
  to reason about the body of each branch,
  under the hypothesis that the previous branches
  have not been taken and that this branch has been taken.
  In the first approach, the judgement `safe` suffices.
  In the second approach, the judgement `safe2` may be needed.
  Which approach do we wish to favor?

* Use Coq lists, if possible, instead of custom `Nil` and `Cons`
  constructors in patterns, values, etc.

* Add support for mutable record fields.
  The name of each field should indicate whether it is mutable
  or immutable.

* Add support for spawning threads.

* Can we (and should we) prove that our formulation of the semantics
  is equivalent to a standard small-step presentation?

## References

* maillard-al-19
* fromherz-steel-21
* silver-zdancewic-21
* nigron-dagand-21
* zakowski-al-21
* yoon-zakowski-zdancewic-22
* [keuchel-al-22](https://iris-project.org/pdfs/2022-icfp-symbexec-final.pdf)
* chappe-al-23

## Features of OCaml that we want to support (at some point)

* Functions and function applications
* Mutually-recursive functions
* Arrays
* Algebraic data types (unit, tuples, sums, records, sums-of-records; mutable fields)
* Integers (bounded or idealized?)
* Pattern matching on immutable data (must prove absence of match failure)
* Polymorphic variants
* Unspecified evaluation order of `let/and` definitions and function applications
* Unspecified evaluation of `assert` statements
* Modules, functors, signature ascription, `open` and `include` directives
  - Note that `open` and `include` break the lexical scoping discipline
    (and require keeping track of module signatures at runtime)
    unless we ask the OCaml compiler to perform disambiguation and annotate
    these constructs with a (fully expanded) signature.
* Unspecified evaluation order of toplevel modules
* First-class modules
* Extensible algebraic data types
* Recursive values of a mutable type
* Exceptions
* Effect handlers
* Shared-memory concurrency (SC)
* Shared-memory concurrency (weak memory)

## Features of OCaml that we do not want to support

* Polymorphic comparison operators
* Floating point numbers
* Pattern matching on mutable data
* The `lazy` pattern
* `when` clauses
* Immutable recursive values other than functions
* Objects and classes
* Labeled arguments
* Optional arguments and default values
