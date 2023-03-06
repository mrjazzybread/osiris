# TODO

* Separate the monadic support layer from the definition of the
  OCaml semantics.

* Clean the type classes and notation for monads.

* Think about [order of evaluation](https://v2.ocaml.org/manual/expr.html#sss:expr-functions-application).
  Is it faithful to have only binary function applications in our calculus?
    (To recover all possible behaviors of an n-ary application,
     our binary application must allow interleaved execution
     of the two sides.)
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

* Can we show that performing a `Stop` effect is "the same" as performing
  a recursive call to `eval`, when this call is permitted?
