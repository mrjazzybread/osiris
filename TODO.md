# TODO

* Use existing type classes and notation for monads?

* Think about order of evaluation: is it really unspecified in OCaml?
  Introduce a parallel-bind or a parallel-tuple construct in the evaluator,
  and think about its implementation.
  Should the evaluation of a parallel-tuple just cause a [Stop] effect?
  Can we evaluate parallel-tuples without stopping
  when all components (except at most one) are trivial?

* Use Coq lists, if possible, instead of custom `Nil` and `Cons`
  constructors in patterns, values, etc.

* Add support for mutable record fields.
  The name of each field should indicate whether it is mutable
  or immutable.

* Add support for spawning threads.

* Can we (and should we) prove that our formulation of the semantics
  is equivalent to a standard small-step presentation?
