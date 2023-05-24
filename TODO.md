# TODO

## Cleanup

* Rename `free` to `micro`.
* Rename `osirisGS_gen` to something less ugly.
* In `steps.v`, we could use `nsteps` from `stdpp`.

## Iris machinery

* Prove adequacy.
* Add support for Iris invariants.

## Engineering and proof mode

* Develop a set of tactics specifically for reasoning about pure
  programs using `simp`.

* Take advantage of the lemma `wp_simp` in the simplification tactics.

* Once the above is done,
  remove the use of
  `wp_par_ret_ret`,
  `wp_par_ret_left`,
  `wp_par_ret_right`
  in the tactics.
  (Then, remove these lemmas or make them local.)

* Experiment with the granularity of Coq toplevel definitions.
  We could use as few as one per OCaml file
  and as many as one per AST node.
  In between, we could use one per OCaml definition,
  and/or make sure that we use enough to ensure that
  every Coq definition has bounded size.

* By default, hide continuations in goals (they are too verbose).
  Offer an option to show them.

* Display environments in a nice form in goals.
  + One binding per line.
  + By default, display complex values (such as closures)
    in an abbreviated form.

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

 * Find a way to declare a function n-ary so that proving specifications of its
   partial applications is not required.

 * Find a way to declare functions "pure" so that their applications can move
   out of Par-trees.

 * Define a better [wp] tactic so that it automatically calls user-defined
   specification lemmas and those about the standard library.

 * Using distinct typeclasses for partially and totally applied binary functions
   allows to decide which functions are allowed to be partially applied. On the
   other hand, it duplicates all the proofs.  It might be interesting to use
   only one TC and add a trivial typeclass to request an automatic treatment of
   partial applications.

 * Get tactics to fail: currently, tactics usually do not fail and might not
   make progress. Thus, it is difficult to debug them.

 * Use more hint databases for typeclasses, not to mix simplifications with
   reasoning.

 * Find a good way to rewrite `VInt _` and others using the Encode typeclass.
   Currently, special instances are written when applying specifications.
   Two ideas would be to:
   - either rewrite `VInt i` and others as `#i` after each step (might cost a
     lot)
   - either write generic typeclass instances which know about Encode (for the
     lemmas applying specifications). This was not added yet as the
     specification mechanism will probably change soon.


## Semantics

* At closure construction time, should the semantics trim the environment η
  so as to keep only the variables that occur free in the code?
  + Cons: this makes the semantics more complex.
  + Pros: this should lead to simpler and more natural goals.

* Can we (and should we) prove that our formulation of the semantics
  is equivalent to a standard small-step presentation?
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
  - Port Arthur's imperative pairing heaps and compare with CFML.

## References

* Do Jacques Garrigue and his students have a semantics of a fragment of OCaml?
* Scott Owens
* Malfunction
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
* Look at Krebbers's dissertation to see how he handles unspecified evaluation
  order in C.
* Goose and GooseLang (Tej Chajed).

## Features of OCaml that we want to support (at some point)

* Functions and function applications ✓
* Mutually recursive functions ✓
* Algebraic data types (unit, tuples, sums, records, sums-of-records) ✓
* Pattern matching on immutable data ✓
* Conditionals ✓
* `while` loops ✓
* `for` loops ✓
* Unspecified evaluation order of `let/and` definitions and function applications ✓
* Unspecified evaluation of `assert` statements ✓
* `Obj.magic` can be supported (just erase it);
  I think that we will be able to verify programs that make "dynamically well-typed"
  use of `Obj.magic` (i.e., programs that do no cast values from one type to another).
* Arrays
* Characters and strings
* Records with mutable fields
* Integers:
  + give lemmas to help establish that the result of an operation
    is representable
  + bitwise operations
  + comparison operators: `=`, `<>`, `<`, `>`, `<=`, `>=`, `compare`, `min`, `max`
* Booleans:
  + We would like to have all of the comparison operators,
    but because our model views Booleans as data constructors,
    we cannot have the ordering operators.
* Polymorphic comparison operators
  + Equality can be supported at immutable data types
  + Ordering can be supported at base types and tuples
    (ordering at algebraic data types cannot be supported)
* Polymorphic variants
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
  + Exception names must be treated like variables,
    *not* like data constructors
  + Asynchronous exceptions (`Out_of_memory`, `Stack_overflow`...)
    are not modelled in our semantics, so must not be caught;
    catch-all handlers are therefore problematic;
    `Fun.protect` seems OK because it is effect-polymorphic
* Effect handlers
* Shared-memory concurrency (SC)
* Shared-memory concurrency (weak memory)
* Pattern matching on mutable data
* `when` clauses

## Features of OCaml that we do not want to support

* Floating point numbers
* Objects and classes
* The `lazy` pattern
* Immutable recursive values other than functions
* Labeled arguments
* Optional arguments and default values

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
