# TODO

## TODO for artifact submission

- README for more detailed instructions
- VM?

### Irene's TODO's

- Repair bst.v
- Merge exceptions.v into exceptions_pure.v into one file
- Remove fact_rec.v
- Delete the .ml source files that have no correspondences


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
