# TODO

## Engineering and proof mode

* When we have a tree of nested `Par` and some of the leaves in the middle
  are of the form `Ret _`, one should in principle be able to permute the
  leaves so as to then be able to use `prove_safe_Par_ret_left`. Can this
  be implemented? Is it worth the trouble?
  Minimal example: suppose we have `par m1 (par (ret a2) (ret a3))`
  where `m1` is a complex computation. Currently we are forced to
  apply the general reasoning rule `prove_safe_par` but if we could
  permute and/or reassociate the leaves then we could apply
  `prove_safe_Par_ret_left` or `prove_safe_Par_ret_right` (twice)
  and we would end up *not* needing to reason about a parallel
  composition.

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

* Write a `help` tactic that analyzes the goal, explains its shape,
  explains why we are here and what likely is the next thing to do.

* Allowing the user to place labels in the OCaml code, disguished as comments
  `(* label: *)`, could be useful. (Agree with Mario and the Gospel people on
  a standard syntax.) These comments could be preserved in the AST and could
  serve multiple purposes, e.g.: they could be printed in a special way (print
  just the label, not the code below it); they could be used to prevent `cbn`
  to perform simplifications too early; they could serve as targets for the
  symbolic execution engine ("please perform symbolic execution until the
  label foo"). Comments (perhaps of a different kind?) could also be used to
  indicate where we want a sub-AST to be isolated in a toplevel (Coq)
  definition.

## Semantics

* Can we (and should we) prove that our formulation of the semantics
  is equivalent to a standard small-step presentation?
  We should also prove that each ample step corresponds to a bounded
  number of small steps (where the bound may depend on the source
  code of the program) (giving formal meaning to this claim requires
  distinguishing the program and the environment in which the program
  is executed). This means that Osiris with time credits is sound!

## Tests

* Once the translation of OCaml to our AST works, develop a more serious
  test suite of the semantics.

* Can we (automatically) measure the coverage of our test suite?
  i.e., measure whether (and how many times) each line of code
  in the interpreter (eval.v) is exercised by the tests (examples.v).

## References

* Do Jacques Garrigue and his students have a semantics of a fragment of OCaml?
* Scott Owens
* audebaud-zucca-99 (spec monad)
* claessen-99, harrison-06, pirog-gibbons-14 (resumption monad)
* voigtlander-08, jaskelioff-rivas-15 (efficient presentation of the free monad)
* svenningsson-axelsson-15
* letan-al-18, letan-al-21 (FreeSpec)
* maillard-al-19
* swierstra-baanen-19
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
* Conditionals
* `while` loops
  - Check that we are able to reason about infinite loops using Löb induction
  - Check that we are able to reason about terminating loops using induction
  - Check that we are able to frame out an assertion during
    the execution of the rest of the loop
* Algebraic data types (unit, tuples, sums, records, sums-of-records; mutable fields)
* Integers (bounded, idealized, both?) (rauch-wolff-03, jacobs-03)
  https://coq.discourse.group/t/best-practices-for-machine-level-representation-of-numbers-and-bitwise-operations/482/6
  coq-nbits (https://troll.iis.sinica.edu.tw/by-publ/recent/coq-qfbv.pdf, Section 4)
  https://github.com/fmlab-iis/coq-nbits
  SInt63:
  https://www.ub.edu/prooftheory/media/sint6320x85.pdf
  https://coq.github.io/doc/master/stdlib/Coq.Numbers.Cyclic.Int63.Sint63.html
  Bit sets:
  https://www.irif.fr/~dagand/stuffs/coq-bitset/flops/paper.pdf
* `for` loops
  - Must evaluate both bounds up front,
    then invoke an auxiliary recursive function `eval_for_loop`
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
* Pattern matching on mutable data
* `when` clauses

## Features of OCaml that we do not want to support

* Floating point numbers
* Objects and classes
* Polymorphic comparison operators
* The `lazy` pattern
* Immutable recursive values other than functions
* Labeled arguments
* Optional arguments and default values
