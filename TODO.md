# TODO

* Can we separate the monadic support layer
  from the OCaml-specific aspects?
  That is, make `free.v` independent of `lang.v`.
  And make that monadic support layer an independent library.

* Find a way of annotating failures with a string,
  so we can keep track of the reason for the failure.

* Clean up the type classes and notation for monads.

* Think about [order of evaluation](https://v2.ocaml.org/manual/expr.html#sss:expr-functions-application).
  Is it faithful to have only binary function applications in our calculus?
    (To recover all possible behaviors of an n-ary application,
     our binary application must allow interleaved execution
     of the two sides.)
  Introduce a parallel-bind or a parallel-tuple construct in the evaluator,
  and think about its implementation.
  Can we simplify `par`
  when all components (except at most one) are trivial?

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
